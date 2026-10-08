#!/usr/bin/env python3
"""Find and exactly certify fixed cycle mixtures on the synthetic commute fiber.

Search needs NumPy. Replaying a saved certificate needs only the standard
library and the package. Neither mode makes a runtime claim for large fibers.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict
from fractions import Fraction
import hashlib
import json
from math import floor, isfinite
from pathlib import Path

from contingency115.kernels import heat_bath_kernel, simple_cycles
from contingency115.mixtures import (certify_gap_lower_bound, fixed_mixture,
                                      mixture_gap_upper_bound, rayleigh_quotient)
from contingency115.tables import ExactTableSampler, ProductWeights, TableProblem


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_FIXTURE = ROOT / "examples/synthetic_commute.json"
SOURCE_PATHS = ("src/contingency115/tables.py", "src/contingency115/kernels.py",
                "src/contingency115/mixtures.py", "experiments/cycle_mixtures.py")
TEMPERATURES = (0.03, 0.005, 0.001, 0.0002, 0.00004, 0.000008, 0.0000016)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_inputs(fixture_path):
    fixture = json.loads(fixture_path.read_text())
    problem = TableProblem(fixture["row_sums"], fixture["column_sums"],
                           fixture["upper_bounds"], lower_bounds=fixture["lower_bounds"])
    states = tuple(ExactTableSampler(problem).tables())
    cycles = simple_cycles(problem)
    laws = {
        "uniform_tables": None,
        "conditional_poisson": ProductWeights(fixture["activities"], factorial_weight=True),
    }
    components = {name: tuple(heat_bath_kernel(problem, states, [cycle], weights=weights)
                              for cycle in cycles) for name, weights in laws.items()}
    return fixture, states, cycles, components


def quantize_probabilities(values, denominator=10**6):
    """Largest-remainder quantization; the returned vector sums exactly to one."""
    values = [float(x) for x in values]
    if not values or any(not isfinite(x) or x < 0 for x in values) or sum(values) <= 0:
        raise ValueError("invalid numerical probability vector")
    total = sum(values)
    scaled = [x * denominator / total for x in values]
    numerators = [floor(x) for x in scaled]
    remainder = denominator - sum(numerators)
    if not 0 <= remainder <= len(values):
        raise ArithmeticError("unstable probability quantization")
    order = sorted(range(len(values)), key=lambda i: (-(scaled[i] - numerators[i]), i))
    for i in order[:remainder]:
        numerators[i] += 1
    return tuple(Fraction(n, denominator) for n in numerators)


def rational_vector(values):
    values = [float(x) for x in values]
    scale = max(abs(x) for x in values)
    if not isfinite(scale) or not scale:
        raise ArithmeticError("invalid numerical witness")
    return tuple(round(10**8 * x / scale) for x in values)


def reduced_laplacians(components):
    import numpy as np
    pi = np.array([float(x) for x in components[0].stationary])
    if (pi <= 0).any() or not np.isfinite(pi).all():
        raise ArithmeticError("search requires representable, positive target masses")
    root = np.sqrt(pi)
    # Only numerical search uses this irrational change of basis. Certificates
    # are constructed and replayed in original coordinates over the rationals.
    q = np.linalg.qr(np.column_stack([root, np.eye(len(root))[:, 1:]]))[0][:, 1:]
    matrices = np.array([q.T @ (np.eye(len(root)) - root[:, None]
                                * np.array(kernel.matrix, dtype=float) / root[None, :]) @ q
                         for kernel in components])
    return matrices, q, root


def project_simplex(vector):
    import numpy as np
    ordered = np.sort(vector)[::-1]
    prefix = np.cumsum(ordered) - 1
    indices = np.arange(len(vector)) + 1
    last = np.nonzero(ordered - prefix / indices > 0)[0][-1]
    return np.maximum(vector - prefix[last] / (last + 1), 0)


def search_mixture(components, iterations):
    """Numerical accelerated projected ascent of a smoothed minimum eigenvalue.

    The search result carries no guarantee by itself. Exact primal and dual
    checks below certify its achieved gap and bound the best possible gap.
    """
    import numpy as np
    matrices, q, root = reduced_laplacians(components)
    weights = np.ones(len(components)) / len(components)
    trace = []
    for tau in TEMPERATURES:
        def objective_gradient(x):
            eigenvalues, eigenvectors = np.linalg.eigh(np.einsum("i,ijk->jk", x, matrices))
            exponentials = np.exp(-(eigenvalues - eigenvalues[0]) / tau)
            probabilities = exponentials / exponentials.sum()
            objective = eigenvalues[0] - tau * np.log(exponentials.sum())
            density = (eigenvectors * probabilities) @ eigenvectors.T
            return objective, np.einsum("ij,kij->k", density, matrices)

        current = weights.copy()
        extrapolated = current.copy()
        acceleration, lipschitz = 1.0, 1.0
        for _ in range(iterations):
            value, gradient = objective_gradient(extrapolated)
            for _backtrack in range(80):
                candidate = project_simplex(extrapolated + gradient / lipschitz)
                candidate_value, _ = objective_gradient(candidate)
                delta = candidate - extrapolated
                if candidate_value >= value + gradient @ delta - 0.5 * lipschitz * (delta @ delta) - 1e-14:
                    break
                lipschitz *= 2
            else:
                raise ArithmeticError("numerical line search did not converge")
            new_acceleration = (1 + np.sqrt(1 + 4 * acceleration**2)) / 2
            extrapolated = candidate + (acceleration - 1) / new_acceleration * (candidate - current)
            current = candidate
            acceleration = new_acceleration
            lipschitz = max(lipschitz * 0.9, 1e-5)
        weights = current
        eigenvalues, eigenvectors = np.linalg.eigh(np.einsum("i,ijk->jk", weights, matrices))
        trace.append({"temperature": tau, "float64_gap_before_quantization": float(eigenvalues[0])})
    dual_weights = np.exp(-(eigenvalues - eigenvalues[0]) / TEMPERATURES[-1])
    dual_weights /= dual_weights.sum()
    active = [i for i, weight in enumerate(dual_weights) if weight > 1e-9]
    vectors = [rational_vector(q @ eigenvectors[:, i] / root) for i in active]
    dual_probabilities = quantize_probabilities([dual_weights[i] for i in active], 10**8)
    return quantize_probabilities(weights), vectors, dual_probabilities, trace


def lower_receipt(certificate):
    return {"bound": str(certificate.bound), "positive_support": list(certificate.positive_support),
            "psd": asdict(certificate.psd)}


def certify_case(components, probabilities, cycles, allowed):
    import numpy as np
    mixed = fixed_mixture(components, probabilities)
    matrices, q, root = reduced_laplacians((mixed,))
    eigenvalues, eigenvectors = np.linalg.eigh(matrices[0])
    vector = rational_vector(q @ eigenvectors[:, 0] / root)
    upper = rayleigh_quotient(mixed, vector)
    candidate_numerator = floor(float(eigenvalues[0]) * 10**6) - 1
    for _ in range(20):
        lower = certify_gap_lower_bound(mixed, max(Fraction(0), Fraction(candidate_numerator, 10**6)))
        if lower.certified:
            break
        candidate_numerator -= 1
    else:
        raise ArithmeticError("numerical estimate did not yield an exact lower certificate")
    if lower.bound > upper:
        raise AssertionError("contradictory exact gap certificates")
    return {
        "allowed_cycle_indices": list(allowed),
        "cycle_probabilities": [str(p) for p in probabilities],
        "expected_cycle_cells": str(sum(p * c.length for p, c in zip(probabilities, cycles))),
        "positive_probability_cycles": sum(p > 0 for p in probabilities),
        "exact_stochasticity_and_detailed_balance": mixed.is_stochastic() and mixed.satisfies_detailed_balance(),
        "float64_gap_after_quantization": float(eigenvalues[0]),
        "gap_lower": lower_receipt(lower),
        "gap_upper": {"bound": str(upper), "witness_values": list(vector)},
    }


def improvement(cases, candidate, comparison, *, compare_with_family=False):
    numerator = Fraction(cases[candidate]["gap_lower"]["bound"])
    field = "family_gap_upper" if compare_with_family else "gap_upper"
    denominator = Fraction(cases[comparison][field]["bound"])
    ratio = numerator / denominator
    if ratio <= 1:
        raise AssertionError("the requested improvement was not certified")
    return {"candidate": candidate, "comparison": comparison,
            "comparison_is_every_allowed_mixture": compare_with_family,
            "gap_ratio_at_least": str(ratio), "gap_percent_increase_at_least_float64": float(100 * (ratio - 1))}


def search_report(fixture_path, iterations):
    fixture, states, cycles, by_law = build_inputs(fixture_path)
    rectangles = tuple(i for i, cycle in enumerate(cycles) if cycle.length == 4)
    all_indices = tuple(range(len(cycles)))
    report = {
        "schema_version": 1,
        "scope": "Exact finite-instance gap certificates for state-independent cycle mixtures, not a general rapid-mixing theorem or measured runtime improvement.",
        "fixture": fixture["name"], "fixture_sha256": sha256(fixture_path),
        "data_classification": "synthetic; no empirical accuracy claim",
        "source_sha256": {path: sha256(ROOT / path) for path in SOURCE_PATHS},
        "state_count": len(states),
        "state_order_sha256": hashlib.sha256(json.dumps(states, separators=(",", ":")).encode()).hexdigest(),
        "catalog": [{"index": i, "length": cycle.length, "signs": cycle.signs} for i, cycle in enumerate(cycles)],
        "search": {"method": "smoothed eigenvalue optimization by accelerated projected ascent, followed by rational quantization",
                   "iterations_per_temperature": iterations, "temperatures": TEMPERATURES,
                   "numerical_values_are_proofs": False},
        "certificate_method": "rational PSD lower bound via fraction-free symmetric elimination; rational Rayleigh upper bound; convex combinations of Rayleigh quotients bound every allowed fixed mixture",
        "laws": {},
    }
    for name, components in by_law.items():
        cases = {}
        for label, allowed in (("rectangles", rectangles), ("simple_cycles", all_indices)):
            uniform = tuple(Fraction(1, len(allowed)) if i in allowed else Fraction(0) for i in all_indices)
            cases["equal_" + label] = certify_case(components, uniform, cycles, allowed)
            family = tuple(components[i] for i in allowed)
            weights, vectors, dual_probabilities, trace = search_mixture(family, iterations)
            expanded = tuple(weights[allowed.index(i)] if i in allowed else Fraction(0) for i in all_indices)
            result = certify_case(components, expanded, cycles, allowed)
            dual = mixture_gap_upper_bound(family, vectors, dual_probabilities)
            result["family_gap_upper"] = {
                "bound": str(dual.bound), "component_bounds": [str(x) for x in dual.component_bounds],
                "witness_values": vectors, "witness_probabilities": [str(x) for x in dual_probabilities],
            }
            result["numerical_search_trace"] = trace
            cases["tuned_" + label] = result
        report["laws"][name] = {
            "stationary": [str(p) for p in components[0].stationary],
            "cases": cases,
            "certified_improvements": [
                improvement(cases, "tuned_simple_cycles", "equal_rectangles"),
                improvement(cases, "tuned_rectangles", "equal_rectangles"),
                improvement(cases, "tuned_simple_cycles", "tuned_rectangles", compare_with_family=True),
            ],
        }
    return report


def replay_report(report, fixture_path, *, check_source_hashes=True):
    """Reconstruct all matrices and verify all rational claims, without NumPy."""
    fixture, states, cycles, by_law = build_inputs(fixture_path)
    if report["schema_version"] != 1 or report["fixture"] != fixture["name"] or report["fixture_sha256"] != sha256(fixture_path):
        raise ValueError("fixture provenance mismatch")
    if check_source_hashes and report["source_sha256"] != {path: sha256(ROOT / path) for path in SOURCE_PATHS}:
        raise ValueError("certificate producer sources have changed; rebuild or explicitly inspect the difference")
    if report["state_count"] != len(states) or report["state_order_sha256"] != hashlib.sha256(json.dumps(states, separators=(",", ":")).encode()).hexdigest():
        raise ValueError("state order mismatch")
    catalog = [{"index": i, "length": cycle.length, "signs": [list(row) for row in cycle.signs]}
               for i, cycle in enumerate(cycles)]
    if report["catalog"] != catalog or set(report["laws"]) != set(by_law):
        raise ValueError("catalog or target-law mismatch")
    verified_cases, verified_dual_bounds, strict_comparisons = 0, 0, 0
    intervals = {}
    for name, components in by_law.items():
        law = report["laws"][name]
        if tuple(Fraction(p) for p in law["stationary"]) != components[0].stationary:
            raise ValueError("stationary law mismatch")
        if set(law["cases"]) != {"equal_rectangles", "equal_simple_cycles", "tuned_rectangles", "tuned_simple_cycles"}:
            raise ValueError("missing comparison case")
        intervals[name] = {}
        for label, case in law["cases"].items():
            allowed = [i for i, cycle in enumerate(cycles) if label.endswith("simple_cycles") or cycle.length == 4]
            if case["allowed_cycle_indices"] != allowed:
                raise ValueError("allowed cycle family mismatch")
            probabilities = tuple(Fraction(p) for p in case["cycle_probabilities"])
            if len(probabilities) != len(cycles) or any(p for i, p in enumerate(probabilities) if i not in allowed):
                raise ValueError("probability assigned outside the allowed family")
            if label.startswith("equal_") and probabilities != tuple(Fraction(1, len(allowed)) if i in allowed else Fraction(0) for i in range(len(cycles))):
                raise ValueError("the equal-mixture comparison is not equal")
            mixed = fixed_mixture(components, probabilities)
            if not case["exact_stochasticity_and_detailed_balance"]:
                raise ValueError("missing reversible-kernel assertion")
            if Fraction(case["expected_cycle_cells"]) != sum(p * c.length for p, c in zip(probabilities, cycles)) or case["positive_probability_cycles"] != sum(p > 0 for p in probabilities):
                raise ValueError("cycle cost summary mismatch")
            lower = certify_gap_lower_bound(mixed, Fraction(case["gap_lower"]["bound"]))
            if not lower.certified or lower_receipt(lower) != case["gap_lower"]:
                raise ValueError("invalid lower certificate")
            upper = rayleigh_quotient(mixed, case["gap_upper"]["witness_values"])
            if upper != Fraction(case["gap_upper"]["bound"]) or upper < lower.bound:
                raise ValueError("invalid upper certificate")
            verified_cases += 1
            intervals[name][label] = {"lower_float64_display": float(lower.bound), "upper_float64_display": float(upper)}
            if label.startswith("tuned_"):
                claimed = case["family_gap_upper"]
                dual = mixture_gap_upper_bound(tuple(components[i] for i in allowed), claimed["witness_values"],
                                                tuple(Fraction(p) for p in claimed["witness_probabilities"]))
                if dual.bound != Fraction(claimed["bound"]) or dual.component_bounds != tuple(Fraction(p) for p in claimed["component_bounds"]) or dual.bound < lower.bound:
                    raise ValueError("invalid family upper certificate")
                intervals[name][label]["all_allowed_mixtures_upper_float64_display"] = float(dual.bound)
                verified_dual_bounds += 1
        expected = [improvement(law["cases"], "tuned_simple_cycles", "equal_rectangles"),
                    improvement(law["cases"], "tuned_rectangles", "equal_rectangles"),
                    improvement(law["cases"], "tuned_simple_cycles", "tuned_rectangles", compare_with_family=True)]
        if law["certified_improvements"] != expected:
            raise ValueError("invalid improvement comparison")
        strict_comparisons += len(expected)
    return {"verified_gap_intervals": verified_cases, "verified_family_upper_bounds": verified_dual_bounds,
            "verified_strict_improvements": strict_comparisons, "intervals": intervals}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--output", type=Path, default=ROOT / "reports/cycle-mixtures.json")
    parser.add_argument("--replay", type=Path, help="check this saved certificate using exact arithmetic only")
    parser.add_argument("--iterations", type=int, default=700)
    args = parser.parse_args()
    if args.iterations < 1:
        parser.error("--iterations must be positive")
    if args.replay:
        result = replay_report(json.loads(args.replay.read_text()), args.fixture)
    else:
        report = search_report(args.fixture, args.iterations)
        # A JSON round trip makes the stored witness, not in-memory tuples, the
        # subject of the independent exact replay step.
        encoded = json.dumps(report, indent=2) + "\n"
        result = replay_report(json.loads(encoded), args.fixture)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
