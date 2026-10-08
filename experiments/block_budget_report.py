#!/usr/bin/env python3
"""Reproducible conditional work allowances, not measured running times.

  PYTHONPATH=src python3 experiments/block_budget_report.py --output reports/block-budget-comparison.json
"""

from __future__ import annotations

import argparse
from dataclasses import asdict
from fractions import Fraction as F
import json
from pathlib import Path

from contingency115.block_budgets import (
    independent_oracle_work,
    inner_block_schedule,
    work_difference,
)


UPSTREAM_COMMIT = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def exact_record(value):
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, F)):
        return str(value)
    if isinstance(value, dict):
        return {key: exact_record(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [exact_record(item) for item in value]
    return value


def ratio(numerator: int, denominator: int) -> dict | None:
    if denominator == 0:
        return None
    value = F(numerator, denominator)
    return {"exact_fraction": str(value), "approx_display_only": float(value)}


def case_record(name: str, parameters: dict) -> dict:
    variants = {
        "quarter_exact_lag1": dict(block_failure_target=F(1, 4)),
        "eighth_exact_lag1": {},
        "eighth_exact_lag2": dict(lag_error_bits=2),
        "eighth_exact_lag4": dict(lag_error_bits=4),
        "eighth_hoeffding_lag1": dict(median_policy="hoeffding"),
    }
    schedules = {key: inner_block_schedule(**parameters, **options)
                 for key, options in variants.items()}
    first = schedules["eighth_exact_lag1"]
    independent = independent_oracle_work(first.reference)
    records = {}
    for key, schedule in schedules.items():
        record = asdict(schedule)
        del record["reference"]
        records[key] = {
            "schedule": exact_record(record),
            "change_from_independent_work": exact_record(work_difference(schedule.work, independent)),
            "independent_transitions_over_block_transitions": ratio(
                independent.bin_transitions, schedule.work.bin_transitions),
            "block_ratio_evaluations_over_independent": ratio(
                schedule.work.ratio_evaluations, independent.ratio_evaluations),
            "block_correction_evaluations_over_independent": ratio(
                schedule.work.correction_evaluations, independent.correction_evaluations),
            "block_offset_draws_over_independent": ratio(
                schedule.work.scalar_offset_draws, independent.scalar_offset_draws),
        }
    eighth, quarter = schedules["eighth_exact_lag1"], schedules["quarter_exact_lag1"]
    return {
        "name": name,
        "interpretation": "Abstract conditional parameter tuple, not a constructed contingency-table instance.",
        "parameters": exact_record(parameters),
        "independent_reference": exact_record(asdict(first.reference)),
        "independent_work": exact_record(asdict(independent)),
        "block_variants": records,
        "eighth_over_quarter_work_ratios": {
            key: ratio(getattr(eighth.work, key), getattr(quarter.work, key))
            for key in eighth.work.__dataclass_fields__
        },
    }


def report() -> dict:
    common = dict(d=19, bin_scale=1000, annealing_height=100,
                  relative_accuracy=F(1, 1000), failure_probability=F(1, 10**6))
    cases = [
        ("height_100_full_index", common),
        ("height_10000_full_index", {**common, "annealing_height": 10000}),
        ("height_100_actual_index_1", {**common, "annealing_step": 1}),
        ("low_mixing_cost_tradeoff", dict(
            d=1, bin_scale=2, annealing_height=1,
            relative_accuracy=F(249, 1000), failure_probability=F(1, 5),
            inverse_gap_bound=F(2),
        )),
    ]
    return {
        "schema_version": 1,
        "provenance": {
            "upstream_repository": "https://github.com/openai/math",
            "upstream_commit": UPSTREAM_COMMIT,
            "upstream_section": "preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/evaluation.tex",
            "implementation": "src/contingency115/block_budgets.py",
            "proof": "docs/block-budgets.md",
            "finite_law_tests": "tests/test_block_budgets.py",
            "reproduce": "PYTHONPATH=src python3 experiments/block_budget_report.py --output reports/block-budget-comparison.json",
        },
        "claim_status": {
            "level": "Conditional analytic schedule with exact arithmetic and finite-law checks",
            "not_claimed": [
                "Measured runtime improvement or universal practical speedup",
                "Implemented physical bin oracle, complete sampler, or FPRAS",
                "New compiled Lean theorem or replacement of the existing Lean oracle interface",
                "A certified gap or verified physical geometry for the illustrative parameter tuples",
            ],
            "required_hypotheses": [
                "Certified common inverse spectral gap bound for the actual fixed finite lazy reversible bin kernels",
                "The stated minimum mass and observable support bounds",
                "Independent blocks and exact transitions within every block",
                "Fresh conditional offset randomness, independent of future transition randomness",
                "The source correction-rounding hypotheses for the claimed positive rational oracle output",
            ],
        },
        "work_accounting": {
            "bin_transitions": "Exact ideal-kernel transition calls, including each independent block's burn-in",
            "ratio_evaluations": "One exact ratio evaluation per recorded ratio-bin observation",
            "correction_evaluations": "One source correction arithmetic evaluation per recorded correction-bin observation",
            "scalar_offset_draws": "Uniform upper allowance d per correction evaluation, coupled to exact conditional offsets",
            "rational_accumulations": "One addition-to-sum allowance per observation",
            "mean_divisions": "One division by the deterministic observation count per block mean",
            "median_comparison_bound": "At most M(M-1)/2 rational comparisons per factor using explicit insertion",
            "limitations": "These are separate operation allowances, not equally priced machine steps. Operand sizes, evaluation internals, array moves, and final product work must be included for a complete machine-cost comparison. No timings were collected.",
        },
        "numeric_convention": "Schedule values and ratios are exact strings. Only fields explicitly named approx_display_only use floating point.",
        "cases": [case_record(name, parameters) for name, parameters in cases],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rendered = json.dumps(report(), indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(rendered, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)


if __name__ == "__main__":
    main()
