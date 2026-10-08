#!/usr/bin/env python3
"""Serialize universal arithmetic certificates and conditional gap allowances."""

import argparse
from dataclasses import asdict
from fractions import Fraction
import hashlib
import json
from math import log10
from pathlib import Path

from contingency115.budgets import sampling_small_gap_bound
from contingency115.scales import (
    padded_margin_scale_probability_bounds, proposed_scale_certificates,
    proposed_scales, scale_probability_bounds, shape_aware_scales,
    shape_aware_scale_probability_bounds, sharper_scale_certificates,
    sharper_scales,
)
from contingency115.transport_bounds import sampling_constants


def run():
    certificates = proposed_scale_certificates()
    sharper_certificates = sharper_scale_certificates()
    if not all(certificate.verify() for certificate in certificates + sharper_certificates):
        raise AssertionError("a universal scale certificate failed")
    comparisons = []
    for d in (14, 19, 30, 100):
        scales = proposed_scales(d)
        sharper = sharper_scales(d)
        bounds = {
            "source_explicit_original_scales": sampling_small_gap_bound(d),
            "localized_original_scales": sampling_constants(d, d**20)["ideal_inverse_gap_integer_bound"],
            "source_transport_new_scales": sampling_small_gap_bound(d, scales.U),
            "localized_new_scales": sampling_constants(d, scales.U)["ideal_inverse_gap_integer_bound"],
            "localized_enlarged_margin_scales": sampling_constants(d, sharper.U)["ideal_inverse_gap_integer_bound"],
        }
        comparisons.append({
            "d": d,
            "small_slot_allowance": "p=d is a conservative upper allowance, not an asserted table shape",
            "proposed_scales": asdict(scales),
            "sharper_enlarged_margin_scales": asdict(sharper),
            "probability_and_geometry_bounds": {k: str(v) for k, v in scale_probability_bounds(scales).items()},
            "sharper_probability_and_geometry_bounds": {
                k: str(v) for k, v in padded_margin_scale_probability_bounds(sharper).items()},
            "inverse_gap_allowances": {k: {"exact_integer": str(v), "log10_display_only": log10(v)}
                                        for k, v in bounds.items()},
        })
    shapes = []
    for rows, columns in ((1, 1), (2, 2), (2, 3), (3, 5), (5, 50), (5, 300)):
        scales = shape_aware_scales(rows, columns)
        bounds = shape_aware_scale_probability_bounds(rows, columns)
        assert bounds["unpadding_bad_fraction"] <= Fraction(1, 2)
        shapes.append({
            "rows": rows, "columns": columns,
            "donor_pairs_per_marked_cell": (rows - 1) * (columns - 1),
            "large_cell_count_allowance": rows * columns,
            "scales": asdict(scales),
            "threshold_formula": "max(2L, 2L*mn*(m-1)*(n-1)-L-(m-1)*(n-1))",
            "probability_and_geometry_bounds": {k: str(v) for k, v in bounds.items()},
            "localized_inverse_gap_allowance": {
                "exact_integer": str(sampling_constants(scales.d, scales.U)["ideal_inverse_gap_integer_bound"]),
                "small_slot_allowance": "p=d; singleton shapes are deterministic and need no gap estimate",
            },
        })
    root = Path(__file__).resolve().parents[1]
    return {
        "schema_version": 2,
        "upstream_commit": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
        "arithmetic_status": "All shifted coefficients are checked nonnegative; these polynomial inequalities hold for every d>=14.",
        "mathematical_status": "New gap allowances are conditional on source lemmas and the manuscript derivations in docs/transport-localization.md and docs/scale-audit.md.",
        "scope": "Ideal small-chain inverse gap, not complete sampler bit complexity, observed gap, or measured runtime.",
        "proof_integration": "Actual ordinary-table switching, product/linear tails and mean, and both U=64d^5 and shape-aware enlarged-margin padding counts compile in Lean. Full transport, revised machine and Comparator integration remains open; see the formal verification ledger for exact checked sources.",
        "reproduce": "PYTHONPATH=src python3 experiments/scale_report.py --output reports/scale-certificates.json",
        "universal_certificates": [asdict(certificate) for certificate in certificates],
        "sharper_universal_certificates": [asdict(certificate) for certificate in sharper_certificates],
        "illustrative_comparisons": comparisons,
        "shape_aware_comparisons": shapes,
        "source_sha256": {path: hashlib.sha256((root / path).read_bytes()).hexdigest()
                          for path in ("experiments/scale_report.py", "src/contingency115/scales.py",
                                       "src/contingency115/transport_bounds.py", "src/contingency115/budgets.py")},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(run(), indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result)
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
