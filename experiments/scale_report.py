#!/usr/bin/env python3
"""Serialize universal arithmetic certificates and conditional gap allowances."""

import argparse
from dataclasses import asdict
import json
from math import log10
from pathlib import Path

from contingency115.budgets import sampling_small_gap_bound
from contingency115.scales import proposed_scale_certificates, proposed_scales, scale_probability_bounds
from contingency115.transport_bounds import sampling_constants


def run():
    certificates = proposed_scale_certificates()
    if not all(certificate.verify() for certificate in certificates):
        raise AssertionError("a universal scale certificate failed")
    comparisons = []
    for d in (14, 19, 30, 100):
        scales = proposed_scales(d)
        bounds = {
            "source_explicit_original_scales": sampling_small_gap_bound(d),
            "localized_original_scales": sampling_constants(d, d**20)["ideal_inverse_gap_integer_bound"],
            "source_transport_new_scales": sampling_small_gap_bound(d, scales.U),
            "localized_new_scales": sampling_constants(d, scales.U)["ideal_inverse_gap_integer_bound"],
        }
        comparisons.append({
            "d": d,
            "small_slot_allowance": "p=d is a conservative upper allowance, not an asserted table shape",
            "proposed_scales": asdict(scales),
            "probability_and_geometry_bounds": {k: str(v) for k, v in scale_probability_bounds(scales).items()},
            "inverse_gap_allowances": {k: {"exact_integer": str(v), "log10_display_only": log10(v)}
                                        for k, v in bounds.items()},
        })
    return {
        "schema_version": 1,
        "upstream_commit": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
        "arithmetic_status": "All shifted coefficients are checked nonnegative; these polynomial inequalities hold for every d>=14.",
        "mathematical_status": "New gap allowances are conditional on source lemmas and the manuscript derivations in docs/transport-localization.md and docs/scale-audit.md.",
        "scope": "Ideal small-chain inverse gap, not complete sampler bit complexity, observed gap, or measured runtime.",
        "proof_integration": "Full physical-context, scale, machine and Comparator integration remains open.",
        "reproduce": "PYTHONPATH=src python3 experiments/scale_report.py --output reports/scale-certificates.json",
        "universal_certificates": [asdict(certificate) for certificate in certificates],
        "illustrative_comparisons": comparisons,
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
