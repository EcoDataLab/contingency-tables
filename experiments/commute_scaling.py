"""Bounded synthetic commuting benchmark; no observed or private records.

Run from the repository root:
    PYTHONPATH=src python3 experiments/commute_scaling.py
Each destination-count case runs in its own worker with a wall-time watchdog.
"""

from __future__ import annotations

import argparse
import cProfile
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import pstats
import random
import subprocess
import sys
import time

from contingency115.optimize import LinearCertificate, linear_bounds, verify_optimality
from contingency115.tables import ComputationBudgetExceeded, ExactTableSampler, TableProblem


ROOT = Path(__file__).resolve().parents[1]
SEED = 1152026
MODES = ("drive_alone", "carpool_2", "transit", "walk", "wfh")
DEFAULT_DESTINATIONS = (4, 12, 30, 75, 150, 300, 750)


def _apportion(total, weights):
    denominator = sum(weights)
    counts = [total * weight // denominator for weight in weights]
    order = sorted(range(len(weights)), key=lambda j: (-(total * weights[j] % denominator), j))
    for j in order[:total - sum(counts)]:
        counts[j] += 1
    return counts


def synthetic_problem(destinations, seed=SEED):
    """Nested destination prefixes and a feasible integer anchor table.

    Shares, restrictions, caps, distances, and attendance are stipulated
    synthetic modeling choices. The generator has no empirical calibration.
    """
    if isinstance(destinations, bool) or not isinstance(destinations, int) or destinations < 1:
        raise ValueError("destinations must be a positive integer")
    rng = random.Random(seed)
    rows, witness, lower, upper, distances = [], [], [], [], []
    for i in range(destinations):
        workers = rng.randrange(25, 251)
        # Include one nearby destination and span 0.50--50.00 miles thereafter.
        distance = Fraction(100 if i == 0 else rng.randrange(50, 5001), 100)
        allowed = [True, True, i % 5 != 0 and distance <= 35, distance <= 3, True]
        weights = [rng.randrange(40, 81), rng.randrange(6, 17), rng.randrange(5, 26),
                   rng.randrange(3, 16), rng.randrange(7, 26)]
        counts = _apportion(workers, [weight if permitted else 0 for weight, permitted in zip(weights, allowed)])
        rows.append(workers)
        witness.append(counts)
        lower.append([value // 5 if i % 7 == 0 else 0 for value in counts])
        upper.append([min(workers, value + max(3, workers // 4)) if permitted and i % 3 == 0
                      else workers if permitted else 0 for value, permitted in zip(counts, allowed)])
        distances.append(distance)
    columns = [sum(row[j] for row in witness) for j in range(len(MODES))]
    problem = TableProblem(rows, columns, upper, lower)
    anchor = problem.validate_table(witness)
    factors = (Fraction(1), Fraction(1, 2), Fraction(0), Fraction(0), Fraction(0))
    costs = tuple(tuple(distance * 2 * 220 * factor for factor in factors) for distance in distances)
    return problem, costs, anchor, tuple(distances)


def switch_family(problem, witness):
    """Construct a checkable lower bound on table count using disjoint rows.

    Pair consecutive rows and vary their drive/wfh 2x2 cycle by independent
    integer t. Disjoint row pairs make the resulting full tables distinct.
    """
    witness = problem.validate_table(witness)
    m, n = problem.shape
    if n != len(MODES):
        raise ValueError("the commute switch construction requires the five configured modes")
    choices, size = [], 1
    for i in range(0, m - 1, 2):
        signed_cells = ((i, 0, 1), (i, 4, -1), (i + 1, 0, -1), (i + 1, 4, 1))
        lows, highs = [], []
        for row, column, sign in signed_cells:
            value = witness[row][column]
            lower, upper = problem.lower_bounds[row][column], problem.upper_bounds[row][column]
            lows.append(lower - value if sign == 1 else value - upper)
            highs.append(upper - value if sign == 1 else value - lower)
        lo, hi = max(lows), min(highs)
        if not lo <= 0 <= hi:
            raise RuntimeError("a known-feasible anchor had an invalid cycle interval")
        count = hi - lo + 1
        choices.append({"rows": [i, i + 1], "columns": [0, 4], "minimum_t": lo,
                        "maximum_t": hi, "choices": count})
        size *= count
    return {"construction": "independent_drive_wfh_cycles_on_disjoint_row_pairs",
            "lower_bound": str(size), "is_exact_fiber_count": False, "cycles": choices}


def verify_switch_family(problem, witness, certificate):
    """Check the explicit family-size lower bound without counting the fiber."""
    try:
        anchor = problem.validate_table(witness)
        m, n = problem.shape
        if (certificate["construction"] != "independent_drive_wfh_cycles_on_disjoint_row_pairs"
                or certificate["is_exact_fiber_count"] is not False):
            return False
        used_rows, size = set(), 1
        for cycle in certificate["cycles"]:
            rows, columns = cycle["rows"], cycle["columns"]
            if len(rows) != 2 or len(columns) != 2 or rows[0] == rows[1] or columns[0] == columns[1]:
                return False
            if any(isinstance(i, bool) or not isinstance(i, int) or not 0 <= i < m for i in rows):
                return False
            if any(isinstance(j, bool) or not isinstance(j, int) or not 0 <= j < n for j in columns):
                return False
            if used_rows.intersection(rows):
                return False
            used_rows.update(rows)
            lo, hi, choices = cycle["minimum_t"], cycle["maximum_t"], cycle["choices"]
            if any(isinstance(value, bool) or not isinstance(value, int) for value in (lo, hi, choices)):
                return False
            if lo > hi or choices != hi - lo + 1:
                return False
            for a, row in enumerate(rows):
                for b, column in enumerate(columns):
                    sign = 1 if a == b else -1
                    for t in (lo, hi):
                        value = anchor[row][column] + sign * t
                        if not problem.lower_bounds[row][column] <= value <= problem.upper_bounds[row][column]:
                            return False
            size *= choices
        return isinstance(certificate["lower_bound"], str) and int(certificate["lower_bound"]) == size
    except (KeyError, TypeError, ValueError, IndexError):
        return False


def _problem_payload(problem):
    return {"row_sums": list(problem.row_sums), "column_sums": list(problem.column_sums),
            "lower_bounds": [list(row) for row in problem.lower_bounds],
            "upper_bounds": [list(row) for row in problem.upper_bounds]}


def _endpoint_payload(problem, costs, optimum):
    cert = optimum.certificate
    payload = {"value": str(optimum.value), "table": [list(row) for row in optimum.table],
               "certificate": {"maximize": cert.maximize,
                               "row_potentials": [str(value) for value in cert.row_potentials],
                               "column_potentials": [str(value) for value in cert.column_potentials],
                               "bound": str(cert.bound)},
               "augmentations": optimum.augmentations, "residual_arc_examinations": optimum.work_used}
    recovered = json.loads(json.dumps(payload))
    raw = recovered["certificate"]
    certificate = LinearCertificate(raw["maximize"], tuple(map(Fraction, raw["row_potentials"])),
                                     tuple(map(Fraction, raw["column_potentials"])), Fraction(raw["bound"]))
    verified = verify_optimality(problem, costs, recovered["table"], certificate)
    if not verified:
        raise RuntimeError("serialized endpoint certificate failed independent verification")
    payload["serialized_certificate_verified"] = verified
    return payload


def profile_case(destinations, max_work, seed=SEED):
    problem, costs, _, _ = synthetic_problem(destinations, seed)
    profiler = cProfile.Profile()
    started = time.perf_counter()
    status, work_used = "optimal", None
    profiler.enable()
    try:
        bounds = linear_bounds(problem, costs, max_work=max_work)
        work_used = bounds.work_used
    except ComputationBudgetExceeded:
        status = "budget_exceeded"
    finally:
        profiler.disable()
    seconds = time.perf_counter() - started
    stats = pstats.Stats(profiler)
    rows = []
    for (filename, line, function), (primitive_calls, calls, total_time, cumulative_time, _) in stats.stats.items():
        rows.append({"file": Path(filename).name, "line": line, "function": function,
                     "primitive_calls": primitive_calls, "calls": calls,
                     "internal_seconds": total_time, "cumulative_seconds": cumulative_time})
    rows.sort(key=lambda row: (-row["internal_seconds"], row["file"], row["line"]))
    return {"destinations": destinations, "seed": seed, "status": status, "max_work": max_work,
            "residual_arc_examinations": work_used, "profiled_wall_seconds": seconds,
            "optimizer_sha256": hashlib.sha256((ROOT / "src" / "contingency115" / "optimize.py").read_bytes()).hexdigest(),
            "top_functions_by_internal_time": rows[:15], "total_function_calls": stats.total_calls,
            "timing_note": "cProfile instrumentation adds overhead; this is not an uninstrumented benchmark."}


def run_case(destinations, max_work, max_states, max_transitions, seed=SEED):
    problem, costs, witness, distances = synthetic_problem(destinations, seed)
    constraints = _problem_payload(problem)
    payload = {"problem": constraints, "coefficients": [[str(value) for value in row] for row in costs]}
    case = {"destinations": destinations, "modes": list(MODES), "workers": sum(problem.row_sums),
            "problem": constraints, "coefficients": payload["coefficients"],
            "anchor_table": [list(row) for row in witness], "anchor_verified": True,
            "one_way_distance_miles": [str(value) for value in distances],
            "input_sha256": hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
            "structural_zero_cells": sum(value == 0 for row in problem.upper_bounds for value in row),
            "fiber_size_certificate": switch_family(problem, witness)}
    case["fiber_size_certificate_verified"] = verify_switch_family(problem, witness, case["fiber_size_certificate"])
    if not case["fiber_size_certificate_verified"]:
        raise RuntimeError("the constructive fiber-size certificate failed verification")
    started = time.perf_counter()
    try:
        bounds = linear_bounds(problem, costs, max_work=max_work)
    except ComputationBudgetExceeded as error:
        case["optimizer"] = {"status": "budget_exceeded", "reason": str(error), "max_work": max_work,
                             "residual_arc_examinations": max_work, "result_available": False,
                             "wall_seconds": time.perf_counter() - started}
    else:
        seconds = time.perf_counter() - started
        case["optimizer"] = {"status": "optimal", "max_work": max_work, "wall_seconds": seconds,
                             "residual_arc_examinations": bounds.work_used,
                             "minimum": _endpoint_payload(problem, costs, bounds.minimum),
                             "maximum": _endpoint_payload(problem, costs, bounds.maximum)}
    started = time.perf_counter()
    sampler = ExactTableSampler(problem, max_states=max_states, max_transitions=max_transitions)
    try:
        count = sampler.count()
    except ComputationBudgetExceeded as error:
        case["exact_dp"] = {"status": "budget_exceeded", "reason": str(error)}
    else:
        case["exact_dp"] = {"status": "complete", "count": str(count)}
    case["exact_dp"].update(wall_seconds=time.perf_counter() - started, max_states=max_states,
                            max_transitions=max_transitions, stats=sampler.stats,
                            orientation="destination_rows_by_five_mode_columns")
    return case


def _worker(args, destinations, *, profile=False):
    command = [sys.executable, str(Path(__file__).resolve()), "--worker", str(destinations),
               "--max-work", str(args.max_work), "--max-states", str(args.max_states),
               "--max-transitions", str(args.max_transitions), "--seed", str(args.seed)]
    if profile:
        command.append("--worker-profile")
    started = time.perf_counter()
    try:
        completed = subprocess.run(command, text=True, capture_output=True, timeout=args.case_timeout, check=True)
    except subprocess.TimeoutExpired:
        return {"destinations": destinations, "status": "watchdog_timeout", "seconds_limit": args.case_timeout,
                "worker_elapsed_seconds": time.perf_counter() - started,
                "note": "No result is claimed from the terminated benchmark worker."}
    return json.loads(completed.stdout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--destinations", type=int, nargs="+", default=list(DEFAULT_DESTINATIONS))
    parser.add_argument("--seed", type=int, default=SEED)
    parser.add_argument("--max-work", type=int, default=25_000_000)
    parser.add_argument("--max-states", type=int, default=2_000)
    parser.add_argument("--max-transitions", type=int, default=10_000)
    parser.add_argument("--case-timeout", type=float, default=30)
    parser.add_argument("--profile-only", type=int)
    parser.add_argument("--baseline-profile", type=Path)
    parser.add_argument("--baseline-report", type=Path)
    parser.add_argument("--profile-destinations", type=int, default=30)
    parser.add_argument("--output", type=Path, default=ROOT / "reports" / "commute-scaling.json")
    parser.add_argument("--worker", type=int, help=argparse.SUPPRESS)
    parser.add_argument("--worker-profile", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker is not None:
        result = (profile_case(args.worker, args.max_work, args.seed) if args.worker_profile else
                  run_case(args.worker, args.max_work, args.max_states, args.max_transitions, args.seed))
        print(json.dumps(result, sort_keys=True))
        return 0
    if not math.isfinite(args.case_timeout) or args.case_timeout <= 0:
        parser.error("--case-timeout must be positive")
    if args.profile_only is not None:
        report = _worker(args, args.profile_only, profile=True)
    else:
        report = {"schema_version": 1, "data_classification": "synthetic", "generator_version": 1,
                  "seed": args.seed, "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  "optimizer_sha256": hashlib.sha256((ROOT / "src" / "contingency115" / "optimize.py").read_bytes()).hexdigest(),
                  "sampler_sha256": hashlib.sha256((ROOT / "src" / "contingency115" / "tables.py").read_bytes()).hexdigest(),
                  "machine": {"python": platform.python_version(), "implementation": platform.python_implementation(),
                              "system": platform.system(), "release": platform.release(), "machine": platform.machine(),
                              "logical_cpus": os.cpu_count()},
                  "watchdog_seconds_per_case": args.case_timeout,
                  "timing_note": "Local perf_counter wall times; include certificate verification, exclude process startup. No machine-independent speed claim.",
                  "metric": {"name": "annual_household_attributed_commute_vehicle_miles", "unit": "vehicle_miles_per_year",
                             "legs_per_day": 2, "workdays_per_year": 220,
                             "vehicle_per_worker_by_mode": ["1", "1/2", "0", "0", "0"]},
                  "assumptions": ["All records, distances, shares, lower bounds, caps, and forbidden cells are synthetic.",
                                  "Workers per destination are integers between 25 and 250.",
                                  "Workplace association is retained for work from home, which adds zero commute VMT.",
                                  "Two-person carpool mileage is attributed equally; other riders may be outside the cohort.",
                                  "No behavioral calibration or inferential accuracy is established.",
                                  "A fixed-budget reference-DP failure is not an impossibility result for other counting algorithms."],
                  "cases": []}
        report["profiling"] = {"current": _worker(args, args.profile_destinations, profile=True)}
        if args.baseline_profile is not None:
            report["profiling"]["before_integer_cost_scaling"] = json.loads(args.baseline_profile.read_text())
        for destinations in args.destinations:
            case = _worker(args, destinations)
            report["cases"].append(case)
            status = case.get("status", case.get("optimizer", {}).get("status"))
            print(f"{destinations} destinations: {status}", flush=True)
        if args.baseline_report is not None:
            previous = json.loads(args.baseline_report.read_text())
            old_cases = {case["destinations"]: case for case in previous["cases"]}
            comparison = []
            for case in report["cases"]:
                old = old_cases.get(case["destinations"])
                if old is None or "optimizer" not in case or "optimizer" not in old:
                    continue
                before, after = old["optimizer"], case["optimizer"]
                if before["status"] != "optimal" or after["status"] != "optimal":
                    continue
                identical = (old["input_sha256"] == case["input_sha256"]
                             and before["minimum"] == after["minimum"]
                             and before["maximum"] == after["maximum"]
                             and before["residual_arc_examinations"] == after["residual_arc_examinations"])
                if not identical:
                    raise RuntimeError("integer scaling changed a baseline result or work count")
                comparison.append({"destinations": case["destinations"], "input_sha256": case["input_sha256"],
                                   "witnesses_certificates_and_work_identical": identical,
                                   "before_wall_seconds": before["wall_seconds"],
                                   "after_wall_seconds": after["wall_seconds"],
                                   "residual_arc_examinations": after["residual_arc_examinations"]})
            report["before_after_comparison"] = {
                "before_optimizer_sha256": previous["optimizer_sha256"],
                "before_machine": previous["machine"], "cases": comparison,
                "timing_note": "Single local runs at different instants; no universal or stable speed ratio is claimed."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"Report: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
