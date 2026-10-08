"""Synthetic benchmarks for the classical ordinary conditional-worker law.

Run from the repository root:
    PYTHONPATH=src python3 experiments/worker_baseline.py
No private data, external service, or optional numerical package is used.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import random
import time

from contingency115.tables import (ComputationBudgetExceeded, ExactWeightedTableSampler,
                                  ProductWeights, TableProblem)
from contingency115.workers import OrdinaryWorkerSampler, worker_linear_moments


ROOT = Path(__file__).resolve().parents[1]
SEED = 115202610


def split_total(total, count):
    quotient, remainder = divmod(total, count)
    return tuple(quotient + (index < remainder) for index in range(count))


def input_cases():
    cases = [("two_by_two", 2, 2, 4),
             ("twenty_destinations", 20, 5, 10_000),
             ("hundred_destinations", 100, 5, 100_000),
             ("thousand_destinations", 1000, 5, 1_000_000),
             ("hundred_categories", 100, 100, 100_000)]
    for name, m, n, total in cases:
        yield name, split_total(total, m), split_total(total, n)
    # The largest row completion avoids a loop over this enormous total.
    total = 10**15
    yield "large_total_ten_required_draws", (total - 10, 6, 4), split_total(total, 5)


def benchmark_case(name, rows, columns, repeats):
    total = sum(rows)
    started = time.perf_counter()
    sampler = OrdinaryWorkerSampler(rows, columns, max_draws=1_000_000,
                                    max_cells=1_000_000)
    preparation_seconds = time.perf_counter() - started
    # Generic linear observable: fictional commute distance by destination,
    # and equally attributed drive/carpool mileage in the first two columns.
    factors = [Fraction(1), Fraction(1, 2)] + [Fraction(0)] * (len(columns) - 2)
    coefficients = tuple(tuple(440 * (1 + i % 40) * factor for factor in factors)
                         for i in range(len(rows)))
    started = time.perf_counter()
    moments = worker_linear_moments(rows, columns, coefficients)
    moments_seconds = time.perf_counter() - started
    draws = []
    for repeat in range(repeats):
        seed = SEED + repeat
        started = time.perf_counter()
        result = sampler.sample_with_stats(random.Random(seed))
        seconds = time.perf_counter() - started
        row_check = tuple(map(sum, result.table)) == rows
        column_check = tuple(map(sum, zip(*result.table))) == columns
        if not row_check or not column_check:
            raise RuntimeError("sample violated a margin")
        metric = sum(coefficients[i][j] * result.table[i][j]
                     for i in range(len(rows)) for j in range(len(columns)))
        encoded = json.dumps(result.table, separators=(",", ":")).encode()
        draws.append({"seed": seed, "seconds": seconds, "random_draws": result.random_draws,
                      "deterministically_assigned_workers": result.deterministically_assigned_workers,
                      "fenwick_steps": result.fenwick_steps, "margins_verified": True,
                      "sample_sha256": hashlib.sha256(encoded).hexdigest(),
                      "linear_metric": str(metric)})
    return {"name": name, "row_sums": rows, "column_sums": columns,
            "plan": asdict(sampler.plan), "preparation_seconds": preparation_seconds,
            "analytic_moments": {"mean": str(moments.mean), "variance": str(moments.variance),
                                 "seconds": moments_seconds, "full_covariance_included": True},
            "samples": draws, "best_sample_seconds": min(draw["seconds"] for draw in draws),
            "metric_note": "Synthetic commute VMT with 2 legs, 220 workdays, distance 1+(row modulo 40), and vehicle factors1,1/2,0,...; no calibration."}


def completion_dp_comparison():
    rows, columns = (25,) * 12, (60,) * 5
    problem = TableProblem(rows, columns)
    weights = ProductWeights([[1] * 5 for _ in rows], factorial_weight=True)
    dp = ExactWeightedTableSampler(problem, weights, max_states=200, max_transitions=1000)
    started = time.perf_counter()
    try:
        normalizer = dp.normalizer()
    except ComputationBudgetExceeded as error:
        reference = {"status": "budget_exceeded", "reason": str(error)}
    else:
        reference = {"status": "completed", "normalizer": str(normalizer)}
    reference.update(seconds=time.perf_counter() - started, max_states=200,
                     max_transitions=1000, stats=dp.stats)
    started = time.perf_counter()
    draw = OrdinaryWorkerSampler(rows, columns).sample_with_stats(random.Random(SEED))
    seconds = time.perf_counter() - started
    if tuple(map(sum, draw.table)) != rows or tuple(map(sum, zip(*draw.table))) != columns:
        raise RuntimeError("comparison sample violated margins")
    return {"row_sums": rows, "column_sums": columns,
            "same_target_law": "ordinary_inverse_factorial",
            "completion_dp": reference,
            "urn_sampler": {"status": "completed", "seconds": seconds,
                            "random_draws": draw.random_draws, "fenwick_steps": draw.fenwick_steps},
            "interpretation": "This single work-capped comparison does not claim the urn algorithm dominates optimized classical samplers."}


def rejection_check():
    class NoRNG:
        calls = 0

        def randrange(self, stop):
            self.calls += 1
            raise AssertionError("rejected work plan requested randomness")

    rng = NoRNG()
    try:
        OrdinaryWorkerSampler([2**80, 2**80], [2**80, 2**80], max_draws=1_000_000).sample(rng)
    except ComputationBudgetExceeded as error:
        return {"status": "rejected_before_rng", "rng_calls": rng.calls,
                "reason": str(error), "required_draw_bound": str(2**80)}
    raise RuntimeError("large work plan should have been rejected")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "reports" / "worker-baseline.json")
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    source_paths = ("src/contingency115/workers.py", "tests/test_workers.py",
                    "experiments/worker_baseline.py")
    report = {
        "schema_version": 1,
        "algorithm": "classical_conditional_worker_urn_with_fenwick_counts",
        "target_law": "ordinary_tables_with_probability_proportional_to_inverse_cell_factorials",
        "python_version": platform.python_version(),
        "seed_base": SEED,
        "data_classification": "synthetic",
        "source_sha256": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                          for path in source_paths},
        "cases": [benchmark_case(name, rows, columns, args.repeats)
                  for name, rows, columns in input_cases()],
        "completion_dp_comparison": completion_dp_comparison(),
        "budget_rejection": rejection_check(),
        "limitations": [
            "Established mathematics; this is not an improvement to the uniform-table theorem.",
            "No cell bounds, structural zeros, or arbitrary interaction activities are accepted.",
            "Runtime depends on numeric worker count; default budgets reject large required draw counts.",
            "Timings measure this Python implementation on one environment, not a universal performance comparison.",
            "No production model, privacy mechanism, behavioral forecast, or empirical validation is claimed.",
            "Random seeds reproduce pseudorandom benchmarks; exact-law proof assumes uniform integer RNG calls."
        ],
        "established_alternatives": [
            "https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.random_table.html",
            "https://stat.ethz.ch/R-manual/R-devel/library/stats/html/r2dtable.html"
        ]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": len(report["cases"]),
                      "sample_times": {case["name"]: case["best_sample_seconds"] for case in report["cases"]},
                      "completion_dp_status": report["completion_dp_comparison"]["completion_dp"]["status"],
                      "budget_rejection": report["budget_rejection"]["status"]}, indent=2))


if __name__ == "__main__":
    main()
