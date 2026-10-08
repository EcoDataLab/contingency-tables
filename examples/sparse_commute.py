#!/usr/bin/env python3
"""Reproduce exact results for a public, wholly synthetic commuting fixture.

Run from the repository with ``PYTHONPATH=src python examples/sparse_commute.py``.
Add ``--spectral`` for optional NumPy floating-point diagnostics.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
import json
from pathlib import Path

from contingency115.kernels import four_cycles, heat_bath_kernel, simple_cycles
from contingency115.tables import ExactTableSampler, ExactWeightedTableSampler, ProductWeights, TableProblem


def metric_summary(tables, probabilities, coefficients):
    values = [sum(Fraction(value) * coefficients[i][j] for i, row in enumerate(table)
                  for j, value in enumerate(row)) for table in tables]
    mean = sum(probability * value for probability, value in zip(probabilities, values))
    variance = sum(probability * (value - mean) ** 2 for probability, value in zip(probabilities, values))
    distribution = defaultdict(Fraction)
    for value, probability in zip(values, probabilities):
        distribution[value] += probability

    def quantile(level):
        cumulative = Fraction(0)
        for value in sorted(distribution):
            cumulative += distribution[value]
            if cumulative >= level:
                return value
        raise AssertionError("probabilities did not sum to one")

    m, n = len(tables[0]), len(tables[0][0])
    return {
        "metric_mean": str(mean),
        "metric_variance": str(variance),
        "model_95pct_equal_tail_interval": [str(quantile(Fraction(1, 40))), str(quantile(Fraction(39, 40)))],
        "interval_interpretation": "Exact quantiles of the stated synthetic model; not calibrated empirical uncertainty.",
        "expected_cells": [[str(sum(p * table[i][j] for p, table in zip(probabilities, tables)))
                            for j in range(n)] for i in range(m)],
        "metric_probability_mass": [{"value": str(value), "probability": str(distribution[value])}
                                    for value in sorted(distribution)],
    }


def two_by_two_contrast():
    problem = TableProblem([2, 2], [2, 2])
    tables = list(ExactTableSampler(problem).tables())
    worker = ExactWeightedTableSampler(problem, ProductWeights([[1, 1], [1, 1]], True))
    return {"row_sums": [2, 2], "column_sums": [2, 2], "tables": tables,
            "uniform_probabilities": ["1/3"] * 3,
            "conditional_poisson_probabilities": [str(worker.probability(table)) for table in tables]}


def six_cycle_obstruction(spectral=False):
    problem = TableProblem([1, 1, 1], [1, 1, 1], [[1, 1, 0], [0, 1, 1], [1, 0, 1]])
    tables = list(ExactTableSampler(problem).tables())
    rectangles, all_cycles = four_cycles(problem), simple_cycles(problem)
    results = {}
    for label, catalog in (("four_cycles", rectangles), ("all_simple_cycles", all_cycles)):
        kernel = heat_bath_kernel(problem, tables, catalog)
        result = {"catalog_size": len(catalog), "communicating_classes": len(kernel.communicating_classes()),
                  "matrix": [[str(p) for p in row] for row in kernel.matrix],
                  "exact_detailed_balance": kernel.satisfies_detailed_balance()}
        if spectral:
            result["float64_spectral_gap"] = kernel.spectral_gap()
        results[label] = result
    return {"upper_bounds": problem.upper_bounds, "tables": tables, "kernels": results}


def run(fixture_path, spectral=False):
    fixture = json.loads(Path(fixture_path).read_text())
    problem = TableProblem(fixture["row_sums"], fixture["column_sums"], fixture["upper_bounds"], fixture["lower_bounds"])
    uniform = ExactTableSampler(problem)
    tables = list(uniform.tables())
    weights = ProductWeights([[Fraction(value) for value in row] for row in fixture["activities"]],
                             factorial_weight=True)
    worker = ExactWeightedTableSampler(problem, weights)
    coefficients = [[Fraction(distance) * fixture["commute_legs_per_workday"] * fixture["workdays_per_year"]
                     * Fraction(vehicle) for vehicle in fixture["vehicle_per_worker_by_mode"]]
                    for distance in fixture["one_way_distance_miles"]]
    uniform_probabilities = [Fraction(1, len(tables))] * len(tables)
    worker_probabilities = [worker.probability(table) for table in tables]
    laws = {"uniform_tables": metric_summary(tables, uniform_probabilities, coefficients),
            "conditional_poisson": metric_summary(tables, worker_probabilities, coefficients)}
    values = [sum(Fraction(value) * coefficients[i][j] for i, row in enumerate(table)
                  for j, value in enumerate(row)) for table in tables]
    check = fixture.get("expected_reference", {})
    actual = {"feasible_table_count": len(tables), "conditional_poisson_normalizer": str(worker.normalizer()),
              "uniform_metric_mean": laws["uniform_tables"]["metric_mean"],
              "conditional_poisson_metric_mean": laws["conditional_poisson"]["metric_mean"],
              "minimum_metric": str(min(values)), "maximum_metric": str(max(values))}
    for key, value in actual.items():
        if key in check and check[key] != value:
            raise AssertionError(f"independent reference mismatch for {key}: {value} != {check[key]}")
    catalogs = {"four_cycles": four_cycles(problem), "all_simple_cycles": simple_cycles(problem)}
    kernels = {}
    for law, law_weights in (("uniform_tables", None), ("conditional_poisson", weights)):
        kernels[law] = {}
        for label, catalog in catalogs.items():
            kernel = heat_bath_kernel(problem, tables, catalog, weights=law_weights)
            diagnostic = {"catalog_size": len(catalog),
                          "communicating_classes": len(kernel.communicating_classes()),
                          "exact_detailed_balance": kernel.satisfies_detailed_balance()}
            if spectral:
                diagnostic["float64_spectral_gap"] = kernel.spectral_gap()
            kernels[law][label] = diagnostic
    return {
        "scope": "Exact small-fiber reference prototype, not the full #115 sampler or FPRAS.",
        "fixture": fixture["name"], "data_classification": fixture["data_classification"],
        "calibration": "All inputs are synthetic. Target-law comparisons do not measure empirical accuracy.",
        "arithmetic": "Integer/Fraction exact, except explicitly labeled optional spectral gaps.",
        "row_labels": fixture["row_labels"], "column_labels": fixture["column_labels"],
        "metric_name": fixture["metric_name"], "metric_unit": fixture["metric_unit"],
        "reference_crosscheck": actual,
        "uniform_dp": uniform.stats, "conditional_poisson_dp": worker.stats,
        "laws": laws, "kernels": kernels,
        "two_by_two_target_contrast": two_by_two_contrast(),
        "sparse_six_cycle_obstruction": six_cycle_obstruction(spectral),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=Path(__file__).with_name("synthetic_commute.json"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--spectral", action="store_true", help="include optional NumPy float64 gap diagnostics")
    args = parser.parse_args()
    result = run(args.fixture, args.spectral)
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
        print(json.dumps({"output": str(args.output), **result["reference_crosscheck"]}, indent=2))
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
