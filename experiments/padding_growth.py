#!/usr/bin/env python3
"""Reproduce sequential-padding arithmetic and small actual-fiber comparisons."""

import argparse
from dataclasses import asdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from contingency115.padding_growth import (
    growth_envelope, sequential_padding_bound, sequential_scales,
    sequential_shape_scales,
)
from contingency115.scales import proposed_scales, sharper_scales, shape_aware_scales
from contingency115.tables import ExactTableSampler, TableProblem


def rational_record(bound):
    return {key: str(value) if isinstance(value, Fraction) else value
            for key, value in asdict(bound).items()}


def run():
    comparisons = []
    for d in (14, 19, 30, 100, 10**20):
        sequential = sequential_scales(d)
        bound = sequential_padding_bound(d*sequential.L, d, sequential.U)
        assert bound.acceptance_lower_bound > Fraction(1, 2)
        comparisons.append({
            "d": d,
            "marked_cell_and_donor_allowances": "g<=d and e<=d; upper allowances, not an asserted table shape",
            "first_checkpoint_U": proposed_scales(d).U,
            "second_checkpoint_U": sharper_scales(d).U,
            "sequential_scales": asdict(sequential),
            "bound": rational_record(bound),
        })
    shapes = []
    for rows, columns in ((1, 1), (1, 20), (2, 2), (2, 3), (3, 5), (5, 50), (5, 300)):
        scales = sequential_shape_scales(rows, columns)
        e = (rows-1)*(columns-1)
        bound = sequential_padding_bound(rows*columns*scales.L, e, scales.U)
        assert bound.acceptance_lower_bound > Fraction(1, 2)
        assert scales.U <= shape_aware_scales(rows, columns).U
        shapes.append({
            "rows": rows, "columns": columns,
            "marked_cell_allowance": rows*columns, "donor_pairs": e,
            "previous_shape_U": shape_aware_scales(rows, columns).U,
            "sequential_scales": asdict(scales),
            "bound": rational_record(bound),
        })

    rows, columns = (13, 13), (9, 9, 8)
    original = ExactTableSampler(TableProblem(rows, columns)).count()
    finite_checks = []
    for mask in range(64):
        marked = [(i, j) for i in range(2) for j in range(3)
                  if mask & (1 << (3*i+j))]
        U = min((min(rows[i], columns[j]) for i, j in marked), default=0)
        for padding in (1, 2):
            padded_rows, padded_columns = list(rows), list(columns)
            for i, j in marked:
                padded_rows[i] += padding
                padded_columns[j] += padding
            enlarged = ExactTableSampler(TableProblem(padded_rows, padded_columns)).count()
            q, e = len(marked)*padding, 2
            bound = sequential_padding_bound(q, e, U)
            power_bound = Fraction(U+1+e, U+1)**q
            actual_ratio = Fraction(enlarged, original)
            assert actual_ratio <= power_bound <= bound.count_growth_upper_bound
            finite_checks.append({
                "marked_mask_row_major": mask, "padding": padding,
                "minimum_original_incident_margin": U,
                "padded_rows": padded_rows, "padded_columns": padded_columns,
                "enlarged_count": enlarged,
                "actual_enlarged_to_original_ratio": str(actual_ratio),
                "telescoped_power_bound": str(power_bound),
                "envelope_bound": str(bound.count_growth_upper_bound),
            })

    certificate = growth_envelope(Fraction(32, 47))
    assert certificate == Fraction(10147, 5123) < 2
    root = Path(__file__).resolve().parents[1]
    return {
        "schema_version": 1,
        "upstream_commit": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
        "scope": "Ordinary uniform nonnegative integer tables; all marked cells have both original incident margins >=U. No cell caps, structural zeros, or nonuniform weights.",
        "count_statement": "N_padded/N_original <= (1+e/(U+1))^(gL) <= E(gLe/(U+1)) for a nonempty original fiber and rate<3.",
        "proof_status": "Exact arithmetic and finite-fiber replay; mathematical derivation and current Lean status are recorded in docs/sequential-padding.md and docs/formal-verification.md.",
        "sampler_scope": "A stronger count/acceptance bound for the existing uniform padding construction. This alone does not implement or verify the revised sampler or its bit complexity.",
        "envelope": {
            "formula": "E(t)=(t^2+4t+6)/(6-2t)",
            "domain": "0<=t<3",
            "recurrence_cross_multiplied_difference": "(6-2t)(6-2t-2x)*(E(t+x)-(1+x)E(t)) = 2*x*t^3+x^2*(2*t^2+6*t+18)",
            "recurrence_domain": "t>=0, x>=0, t+x<3",
            "universal_rate_allowance": "32/47",
            "growth_upper_bound": str(certificate),
            "acceptance_lower_bound": str(1/certificate),
        },
        "threshold_comparisons": comparisons,
        "shape_aware_comparisons": shapes,
        "actual_fiber_replay": {
            "row_sums": rows, "column_sums": columns,
            "original_count": original,
            "cases": finite_checks,
        },
        "reproduce": "PYTHONPATH=src python3 experiments/padding_growth.py --output reports/padding-growth.json",
        "source_sha256": {path: hashlib.sha256((root/path).read_bytes()).hexdigest()
                          for path in ("experiments/padding_growth.py", "src/contingency115/padding_growth.py",
                                       "src/contingency115/scales.py", "src/contingency115/tables.py")},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = json.dumps(run(), indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
