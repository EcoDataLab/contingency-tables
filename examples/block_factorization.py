#!/usr/bin/env python3
"""Synthetic reference benchmark for exact biconnected-block factorization."""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from contingency115.block_sampler import BlockSamplerBudget, BlockTableSampler, BlockWeightedSampler
from contingency115.tables import (ComputationBudgetExceeded, ExactTableSampler,
                                   ExactWeightedTableSampler, ProductWeights, TableProblem)


ROOT = Path(__file__).resolve().parents[1]


def star_blocks(count):
    """K2,3 blocks share a hub row; each local fiber has seven tables."""
    columns = 3 * count
    return TableProblem([3 * count] + [3] * count, [2] * columns,
                        [[2] * columns] + [[2 if j // 3 == i else 0 for j in range(columns)] for i in range(count)])


def table_hash(table):
    return hashlib.sha256(json.dumps(table, separators=(",", ":")).encode()).hexdigest()


def run_case(block_count):
    problem = star_blocks(block_count)
    budget = BlockSamplerBudget(max_dp_states_total=9 * block_count, max_dp_transitions_total=14 * block_count)
    sampler = BlockTableSampler(problem, budget=budget)
    count = sampler.count()
    assert count == 7**block_count
    ranks = sorted({0, count // 2, count - 1})
    rank_checks = []
    for rank in ranks:
        table = sampler.unrank(rank)
        problem.validate_table(table)
        assert sampler.rank(table) == rank
        rank_checks.append({"rank": str(rank), "table_sha256": table_hash(table)})
    weights = ProductWeights([[1] * problem.shape[1] for _ in range(problem.shape[0])], True)
    weighted = BlockWeightedSampler(problem, weights, budget=budget)
    normalizer = weighted.normalizer()
    # Each local first row is (1,1,1) or one of six permutations of (0,1,2).
    # Their factorial weights are 1 and six copies of 1/4, respectively.
    assert normalizer == Fraction(5, 2)**block_count
    direct = ExactTableSampler(problem, max_states=budget.max_dp_states_total,
                               max_transitions=budget.max_dp_transitions_total)
    try:
        reference_count = direct.count()
    except ComputationBudgetExceeded as error:
        direct_result = {"status": "budget_exhausted", "count": None, "reason": str(error), "stats": direct.stats}
    else:
        assert reference_count == count
        direct_result = {"status": "complete", "count": str(reference_count), "stats": direct.stats}
    exhaustive = None
    if block_count <= 2:
        reference = ExactTableSampler(problem)
        reference_weighted = ExactWeightedTableSampler(problem, weights)
        tables = tuple(sampler.tables())
        assert set(tables) == set(reference.tables())
        assert all(weighted.probability(table) == reference_weighted.probability(table) for table in tables)
        exhaustive = {"tables_checked": len(tables), "count_and_all_weighted_probabilities_match_whole_table_dp": True}
    return {
        "complex_blocks": block_count, "shape": problem.shape, "total_count_in_margins": sum(problem.row_sums),
        "construction": "Each K2,3 block has local row margins (3,3), column margins (2,2,2), and caps 2; all blocks share the first row.",
        "factor_count": len(sampler.blocks), "table_count": str(count), "table_count_bits": count.bit_length(),
        "uniform_preparation": sampler.stats,
        "conditional_poisson_normalizer": str(normalizer), "weighted_preparation": weighted.stats,
        "budget": {"dp_states_total": budget.max_dp_states_total, "dp_transitions_total": budget.max_dp_transitions_total},
        "whole_table_dp_under_same_state_transition_allowances": direct_result,
        "rank_round_trips": rank_checks, "exhaustive_small_crosscheck": exhaustive,
    }


def hybrid_case():
    width = 2**200 + 17
    problem = TableProblem([width + 3, width, 3], [width, width, 2, 2, 2],
                           [[width, width, 2, 2, 2], [width, width, 0, 0, 0], [0, 0, 2, 2, 2]])
    sampler = BlockTableSampler(problem, budget=BlockSamplerBudget(max_dp_states_total=9, max_dp_transitions_total=14))
    assert sampler.count() == 7 * (width + 1)
    for rank in (0, sampler.count() // 2, sampler.count() - 1):
        table = sampler.unrank(rank)
        problem.validate_table(table)
        assert sampler.rank(table) == rank
    weighted = BlockWeightedSampler(problem, ProductWeights([[1] * 5 for _ in range(3)], True))
    try:
        weighted.normalizer()
    except ComputationBudgetExceeded as error:
        weighted_status = {"status": "preflight_rejected", "reason": str(error), "stats": weighted.stats}
    else:
        raise AssertionError("huge factorial inputs escaped preflight")
    return {"description": "One huge single-cycle interval and one K2,3 complex block share a row.",
            "cycle_width_parameter": str(width), "cycle_parameter_bits": width.bit_length(),
            "table_count": str(sampler.count()), "expected_count_formula": "7 * (width + 1)",
            "uniform_preparation": sampler.stats, "rank_round_trips_verified": True,
            "weighted_negative_control": weighted_status}


def run():
    return {
        "schema_version": 1,
        "scope": "Classical block/circulation factorization with exact cycle factors and budgeted DP; no general polynomial-time or wall-clock speedup claim.",
        "data_classification": "Synthetic graph-family benchmark; not a calibrated commuting model or real CBEI input.",
        "target_law": "Unit-activity conditional-Poisson law restricted to the stated structural zeros and caps; distinct from an ordinary unconstrained worker urn.",
        "source_sha256": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                          for path in ("src/contingency115/tables.py", "src/contingency115/cactus.py",
                                       "src/contingency115/block_sampler.py", "examples/block_factorization.py")},
        "cases": [run_case(count) for count in (1, 2, 10, 50)],
        "large_cycle_complex_block_hybrid": hybrid_case(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "reports/block-factorization.json")
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"cases": [{"blocks": case["complex_blocks"], "tables": case["table_count"],
                                "dp_states": case["uniform_preparation"]["dp_states"],
                                "dp_transitions": case["uniform_preparation"]["dp_transitions"],
                                "whole_table_dp_status": case["whole_table_dp_under_same_state_transition_allowances"]["status"]}
                               for case in result["cases"]],
                      "hybrid_dp_states": result["large_cycle_complex_block_hybrid"]["uniform_preparation"]["dp_states"]}, indent=2))


if __name__ == "__main__":
    main()
