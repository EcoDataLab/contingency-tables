#!/usr/bin/env python3
"""Exact synthetic commuting tables with two independent cycle coordinates."""

from __future__ import annotations

import argparse
from dataclasses import asdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

from contingency115.cactus import CactusTableSampler, CactusWeightedSampler
from contingency115.tables import (ComputationBudgetExceeded, ExactTableSampler,
                                   ExactWeightedTableSampler, ProductWeights, TableProblem)


ROOT = Path(__file__).resolve().parents[1]


def problem_for_width(width):
    # Two four-cycles share the first row. The positive fixed transit cell
    # creates extra cycles in the full support, but is removed from active flow.
    return TableProblem([2 * width, width + 1, width], [width, width, width + 1, width],
                        [[width] * 4, [width, width, 1, 0], [0, 0, width, width]],
                        [[0] * 4, [0, 0, 1, 0], [0] * 4])


def run():
    problem = problem_for_width(2)
    uniform = CactusTableSampler(problem)
    tables = tuple(uniform.tables())
    reference = ExactTableSampler(problem)
    assert uniform.count() == reference.count() == 9
    assert set(tables) == set(reference.tables())
    activities = [[4, 1, 3, 1], [2, 3, 1, 1], [1, 1, 2, 4]]
    coefficients = tuple(tuple(Fraction(distance * 2 * 220) * vehicle_share
                               for vehicle_share in (1, Fraction(1, 2), 0, 0)) for distance in (3, 8, 15))
    metrics = tuple(sum(value * coefficients[i][j] for i, row in enumerate(table) for j, value in enumerate(row))
                    for table in tables)
    laws = {}
    for name, factorial in (("aggregate_activity", False), ("conditional_poisson", True)):
        weights = ProductWeights(activities, factorial)
        sampler = CactusWeightedSampler(problem, weights)
        oracle = ExactWeightedTableSampler(problem, weights)
        probabilities = tuple(sampler.probability(table) for table in tables)
        assert sampler.normalizer() == oracle.normalizer()
        assert sum(probabilities) == 1
        assert all(p == oracle.probability(table) for p, table in zip(probabilities, tables))
        mean = sum(p * value for p, value in zip(probabilities, metrics))
        laws[name] = {
            "normalizer": str(sampler.normalizer()), "support_count": sampler.support_count(),
            "preparation_plan": asdict(sampler.plan),
            "cycle_parameter_probabilities": [[str(mass / line.total) for mass in line.masses] for line in sampler.lines],
            "table_probabilities_in_rank_order": [str(p) for p in probabilities],
            "metric_mean": str(mean),
            "metric_variance": str(sum(p * (value - mean)**2 for p, value in zip(probabilities, metrics))),
            "matches_exact_dp": True,
            "seeded_example_table": sampler.sample(random.Random(115)),
        }
    large_width = 2**200 + 17
    large = CactusTableSampler(problem_for_width(large_width))
    ranks = (0, 1, large_width, large_width + 1, large.count() // 2, large.count() - 1)
    assert large.count() == (large_width + 1)**2
    for rank in ranks:
        assert large.rank(large.unrank(rank)) == rank
        large.problem.validate_table(large.unrank(rank))
    try:
        CactusWeightedSampler(large.problem, ProductWeights(activities, True))
    except ComputationBudgetExceeded as error:
        negative_control = str(error)
    else:
        raise AssertionError("huge weighted line escaped its resource guard")
    return {
        "schema_version": 1,
        "scope": "Exact sampling for bounded cactus variable support; synthetic illustration, not the general #115 sampler.",
        "data_classification": "All controls, activities, distances, and zeros are fictional and uncalibrated.",
        "row_labels": ["work_central", "work_west", "work_east"],
        "column_labels": ["drive_alone", "carpool_2", "transit", "wfh"],
        "row_sums": problem.row_sums, "column_sums": problem.column_sums,
        "lower_bounds": problem.lower_bounds, "upper_bounds": problem.upper_bounds,
        "activities": activities,
        "fixed_positive_cell": {"row": 1, "column": 2, "value": 1},
        "source_sha256": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                          for path in ("src/contingency115/tables.py", "src/contingency115/cactus.py", "examples/cactus_commute.py")},
        "uniform": {"table_count": uniform.count(), "stats": uniform.stats,
                    "base_table": uniform.base,
                    "cycle_coordinates": [asdict(cycle) for cycle in uniform.cycles],
                    "tables_in_coordinate_rank_order": tables,
                    "metric_mean": str(sum(metrics) / len(metrics)),
                    "matches_exact_dp": True},
        "metric": {"name": "annual_attributed_commute_vehicle_miles", "unit": "vehicle_miles_per_year",
                   "coefficient_matrix": [[str(value) for value in row] for row in coefficients],
                   "assumptions": "One-way distances 3/8/15 miles; two legs on 220 days; two-person carpool gets half vehicle attribution; transit/WFH contribute no household auto VMT.",
                   "minimum": str(min(metrics)), "maximum": str(max(metrics))},
        "weighted_laws": laws,
        "binary_margin_example": {"width": str(large_width), "width_bits": large_width.bit_length(),
                                  "table_count": str(large.count()), "count_bits": large.count().bit_length(),
                                  "cycle_count": len(large.cycles), "checked_ranks": [str(rank) for rank in ranks],
                                  "round_trips_and_feasibility_verified": True,
                                  "line_values_enumerated_by_uniform_sampler": 0,
                                  "weighted_default_budget_rejection": negative_control},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "reports/cactus-commute.json")
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"small_fiber_tables": result["uniform"]["table_count"],
                      "conditional_poisson_normalizer": result["weighted_laws"]["conditional_poisson"]["normalizer"],
                      "uniform_vmt_mean": result["uniform"]["metric_mean"],
                      "conditional_poisson_vmt_mean": result["weighted_laws"]["conditional_poisson"]["metric_mean"],
                      "binary_margin_count_bits": result["binary_margin_example"]["count_bits"]}, indent=2))


if __name__ == "__main__":
    main()
