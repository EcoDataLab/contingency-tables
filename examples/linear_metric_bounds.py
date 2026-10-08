"""Write certified linear commuting-metric bounds using exact rational inputs.

Run from the repository root:
    PYTHONPATH=src python3 examples/linear_metric_bounds.py
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from contingency115.optimize import (
    FlowCutCertificate,
    InfeasibleFlowError,
    LinearCertificate,
    linear_bounds,
    verify_infeasibility,
    verify_optimality,
)
from contingency115.tables import ComputationBudgetExceeded, InfeasibleTableError, TableProblem


REPOSITORY = Path(__file__).resolve().parents[1]


def exact_input(value, name):
    if isinstance(value, bool) or not isinstance(value, (int, str)):
        raise TypeError(f"{name} must be a JSON integer or exact rational string")
    return Fraction(value)


def serialized_optimum(problem, costs, optimum):
    cert = optimum.certificate
    sign = -1 if cert.maximize else 1
    m, n = problem.shape
    reduced = [[sign * costs[i][j] + cert.row_potentials[i] - cert.column_potentials[j]
                for j in range(n)] for i in range(m)]
    signed_dual = (
        sum(cert.column_potentials[j] * problem.column_sums[j] for j in range(n))
        - sum(cert.row_potentials[i] * problem.row_sums[i] for i in range(m))
        + sum(min(reduced[i][j] * problem.lower_bounds[i][j],
                  reduced[i][j] * problem.upper_bounds[i][j]) for i in range(m) for j in range(n))
    )
    certificate = {
        "kind": "bounded_table_dual_potentials_v1",
        "maximize": cert.maximize,
        "row_potentials": [str(p) for p in cert.row_potentials],
        "column_potentials": [str(p) for p in cert.column_potentials],
        "bound": str(cert.bound),
        "signed_primal": str(sign * optimum.value),
        "signed_dual": str(signed_dual),
        "reduced_coefficients": [[str(value) for value in row] for row in reduced],
    }
    # Reconstruct from the serializable payload; this checks exact string
    # round-tripping, as well as the in-memory witness and potentials.
    serialized_table = [list(row) for row in optimum.table]
    round_trip_payload = json.loads(json.dumps({"certificate": certificate, "table": serialized_table}))
    payload = round_trip_payload["certificate"]
    recovered = LinearCertificate(
        payload["maximize"], tuple(map(Fraction, payload["row_potentials"])),
        tuple(map(Fraction, payload["column_potentials"])), Fraction(payload["bound"]),
    )
    verified = verify_optimality(problem, costs, optimum.table, cert)
    round_trip = verify_optimality(problem, costs, round_trip_payload["table"], recovered)
    if not verified or not round_trip or sign * optimum.value != signed_dual:
        raise RuntimeError("a reported exact optimality certificate failed verification")
    return {
        "value": str(optimum.value),
        "table": serialized_table,
        "certificate": certificate,
        "verification": {
            "optimality_verified": verified,
            "serialized_witness_and_certificate_verified": round_trip,
            "signed_primal_equals_signed_dual": sign * optimum.value == signed_dual,
        },
        "work": {"augmentations": optimum.augmentations,
                 "residual_arc_examinations": optimum.work_used},
    }


def elementary_contradictions(problem):
    """Direct constraints-only diagnostics for the pre-flow infeasible cases."""
    m, n = problem.shape
    violations = []
    if sum(problem.row_sums) != sum(problem.column_sums):
        violations.append({"kind": "unequal_margin_totals", "row_total": sum(problem.row_sums),
                           "column_total": sum(problem.column_sums)})
    for i in range(m):
        for j in range(n):
            if problem.lower_bounds[i][j] > problem.upper_bounds[i][j]:
                violations.append({"kind": "lower_exceeds_effective_upper", "row": i, "column": j,
                                   "lower": problem.lower_bounds[i][j],
                                   "upper": problem.upper_bounds[i][j]})
        if sum(problem.lower_bounds[i]) > problem.row_sums[i]:
            violations.append({"kind": "lower_sum_exceeds_row", "row": i,
                               "lower_sum": sum(problem.lower_bounds[i]), "margin": problem.row_sums[i]})
    for j in range(n):
        lower_sum = sum(problem.lower_bounds[i][j] for i in range(m))
        if lower_sum > problem.column_sums[j]:
            violations.append({"kind": "lower_sum_exceeds_column", "column": j,
                               "lower_sum": lower_sum, "margin": problem.column_sums[j]})
    return violations


def build_report(input_path, max_work):
    source_bytes = input_path.read_bytes()
    data = json.loads(source_bytes)
    problem = TableProblem(data["row_sums"], data["column_sums"], data.get("upper_bounds"),
                           data.get("lower_bounds"), data.get("structural_zeros", ()))
    m, n = problem.shape
    distances = [exact_input(value, "one-way distance") for value in data["one_way_distance_miles"]]
    vehicle_factors = [exact_input(value, "vehicle-per-worker factor")
                       for value in data["vehicle_per_worker_by_mode"]]
    legs = exact_input(data["commute_legs_per_workday"], "commute legs per workday")
    days = exact_input(data["workdays_per_year"], "workdays per year")
    if len(distances) != m or len(vehicle_factors) != n:
        raise ValueError("distance and vehicle-factor lengths must match the table axes")
    costs = tuple(tuple(distance * legs * days * vehicle for vehicle in vehicle_factors)
                  for distance in distances)
    try:
        source_name = str(input_path.resolve().relative_to(REPOSITORY))
    except ValueError:
        source_name = input_path.name
    report = {
        "schema_version": 1,
        "method": "exact_rational_successive_shortest_path_with_independent_certificates",
        "input": {"file": source_name, "sha256": hashlib.sha256(source_bytes).hexdigest(),
                  "fixture_name": data.get("name"), "data_classification": data.get("data_classification")},
        "metric": {"name": data["metric_name"], "unit": data["metric_unit"],
                   "coefficients": [[str(value) for value in row] for row in costs]},
        "problem": {"row_sums": list(problem.row_sums), "column_sums": list(problem.column_sums),
                    "lower_bounds": [list(row) for row in problem.lower_bounds],
                    "upper_bounds": [list(row) for row in problem.upper_bounds]},
        "assumptions": data.get("assumptions", []),
        "interpretation": "Sharp possible endpoints under these controls; not a confidence interval.",
        "probability_law_required": False,
        "max_work": max_work,
    }
    try:
        bounds = linear_bounds(problem, costs, max_work=max_work)
    except InfeasibleFlowError as error:
        cert = error.certificate
        payload = {"kind": "lower_shifted_flow_cut_v1", "rows": list(cert.rows),
                   "columns": list(cert.columns), "capacity": cert.capacity, "required": cert.required}
        recovered_payload = json.loads(json.dumps(payload))
        recovered = FlowCutCertificate(tuple(recovered_payload["rows"]), tuple(recovered_payload["columns"]),
                                       recovered_payload["capacity"], recovered_payload["required"])
        verified = verify_infeasibility(problem, cert)
        round_trip = verify_infeasibility(problem, recovered)
        if not verified or not round_trip:
            raise RuntimeError("a reported exact infeasibility certificate failed verification")
        report.update(status="infeasible", reason=str(error), certificate=payload,
                      verification={"infeasibility_verified": verified,
                                    "serialized_certificate_verified": round_trip})
    except InfeasibleTableError as error:
        violations = elementary_contradictions(problem)
        if not violations:
            raise RuntimeError("an elementary infeasibility claim had no direct contradiction") from error
        report.update(status="infeasible", reason=str(error),
                      certificate={"kind": "elementary_constraint_violations_v1", "violations": violations},
                      verification={"direct_contradictions_verified": True})
    except ComputationBudgetExceeded as error:
        report.update(status="budget_exceeded", reason=str(error), endpoints=None)
    else:
        report.update(status="optimal", minimum=serialized_optimum(problem, costs, bounds.minimum),
                      maximum=serialized_optimum(problem, costs, bounds.maximum), work_used=bounds.work_used)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=REPOSITORY / "examples" / "synthetic_commute.json")
    parser.add_argument("--output", type=Path, default=REPOSITORY / "reports" / "linear-bounds.json")
    parser.add_argument("--max-work", type=int, default=2_000_000)
    args = parser.parse_args()
    report = build_report(args.input, args.max_work)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    if report["status"] == "optimal":
        print(f"Certified range: {report['minimum']['value']} .. {report['maximum']['value']} "
              f"{report['metric']['unit']}")
    else:
        print(f"{report['status']}: {report['reason']}")
    print(f"Report: {args.output}")
    return 2 if report["status"] == "budget_exceeded" else 0


if __name__ == "__main__":
    raise SystemExit(main())
