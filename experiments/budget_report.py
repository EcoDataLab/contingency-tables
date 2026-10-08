#!/usr/bin/env python3
"""Deterministic exact schedule comparison; these are not measured runtimes.

Run from the repository root:
  PYTHONPATH=src python3 experiments/budget_report.py --output reports/budget-comparison.json
"""

from __future__ import annotations

import argparse
from dataclasses import asdict
from fractions import Fraction as F
import json
from math import log10
from pathlib import Path

from contingency115.budgets import (
    ceil_fraction, ceil_log2, correction_rounding_budget, counting_bin_gap_bound, dense_schedule,
    dyadic_denominator_budget, exact_correction_schedule, inner_counting_schedule,
    outer_schedule, sampling_dense_gap_bound, sampling_small_gap_bound,
    table_count_upper_bound,
)


UPSTREAM_COMMIT = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def magnitude(value: int) -> dict:
    shift = max(0, value.bit_length() - 52)
    return {
        "exact_integer": str(value),
        "bit_length": value.bit_length(),
        "log10_approx_display_only": round(log10(value >> shift) + shift * log10(2), 9),
    }


def ratio(numerator: int, denominator: int) -> dict:
    value = F(numerator, denominator)
    return {"exact_fraction": str(value), "approx_display_only": float(value)}


def exact_record(value):
    if isinstance(value, (int, F)):
        return str(value)
    if isinstance(value, dict):
        return {key: exact_record(item) for key, item in value.items()}
    return value


def report() -> dict:
    d, total, k = 19, 6, 20
    capacity = total + d*d**12 + d**20 + 2
    b = d + ceil_log2(capacity + 2)
    gap = sampling_small_gap_bound(d)
    old_outer = {"trials": d**4*(k+1), "steps_per_trial": d**200*(k+b)**2, "dense_accuracy_bits": d**4*(k+b)**2}
    review_j = 2*(1+d*d)*(k+2)
    review_t = gap*(2*d*b + ceil_log2(review_j) + k+2)
    review_outer = {"trials": review_j, "steps_per_trial": review_t, "dense_accuracy_bits": k+2+ceil_log2(review_j*(review_t+1))}
    refined_outer = outer_schedule(d, b, k)

    h = 20
    old_dense = {"trials": d**4*(h+1), "steps_per_trial": d**50*(h+1)**2, "offset_extra_bits": 4*(h+d)}
    review_dense_j = 64*(h+2)
    review_dense_ell = h+2+ceil_log2(review_dense_j*(1+d))
    old_dense_gap = sampling_dense_gap_bound(d, sharp_constant=False)
    review_dense = {"trials": review_dense_j, "steps_per_trial": old_dense_gap*(4*d**5+review_dense_ell), "draw_error_bits": review_dense_ell}
    refined_dense = dense_schedule(d, h)

    old_gate = d**6*b*b
    review_gate = 500*d*b + 1
    refined_exact = exact_correction_schedule(d, b)
    count_bound = table_count_upper_bound((3, 3), (3, 3))
    instance_exact = exact_correction_schedule(d, b, count_upper_bound=count_bound)

    # Abstract inner-oracle parameters. This is a schedule algebra example,
    # not a claim that these are the scales of a particular table instance.
    inner_d, inner_b, height = 19, 1000, 100
    xi, theta = F(1, 1000), F(1, 10**6)
    sigma = xi/(50*(height+1))
    old_n = ceil_fraction(10**6*(height+1)/(theta*sigma*sigma))
    old_q = (inner_d+1)*(height+1)*old_n
    old_inner_gap = counting_bin_gap_bound(inner_d, inner_b, sharp_constant=False)
    old_steps = ceil_fraction(old_inner_gap*(height+inner_d*inner_b+16*old_q/theta+2))
    mean_bits = ceil_log2(8*(height+1)/theta)
    review_n = ceil_fraction(1024*mean_bits/(sigma*sigma))
    review_q = (inner_d+1)*(height+1)*review_n
    review_steps = old_inner_gap*(height+inner_d*inner_b+ceil_log2(8*review_q/theta))
    improved_inner = {
        "hoeffding_common": inner_counting_schedule(inner_d, inner_b, height, xi, theta, concentration="hoeffding", allocation="common", sigma_policy="source", correction_support="published"),
        "bernstein_common": inner_counting_schedule(inner_d, inner_b, height, xi, theta, allocation="common", sigma_policy="source", correction_support="published"),
        "bernstein_by_range": inner_counting_schedule(inner_d, inner_b, height, xi, theta, sigma_policy="source", correction_support="published"),
        "bernstein_product_by_range": inner_counting_schedule(inner_d, inner_b, height, xi, theta, sigma_policy="product", correction_support="published"),
        "bernstein_product_sharp_support": inner_counting_schedule(inner_d, inner_b, height, xi, theta),
    }
    previous = improved_inner["bernstein_by_range"]
    product_policy = improved_inner["bernstein_product_by_range"]
    best = improved_inner["bernstein_product_sharp_support"]
    indexed_schedules = {
        step: inner_counting_schedule(inner_d, inner_b, height, xi, theta, annealing_step=step)
        for step in (1, 10, 50, 100)
    }

    return {
        "schema_version": 3,
        "provenance": {
            "upstream_repository": "https://github.com/openai/math",
            "upstream_commit": UPSTREAM_COMMIT,
            "sources": [
                "preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/algorithms.tex",
                "preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/dense.tex",
                "preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/evaluation.tex",
            ],
            "initial_review": "115/115-contingency-tables-review.md, sections 5 and 6",
            "derivations": "docs/error-budgets.md",
            "reproduce": "PYTHONPATH=src python3 experiments/budget_report.py --output reports/budget-comparison.json",
        },
        "claim_status": {
            "arithmetic": "Exact integer/Fraction schedules; floating display fields are labeled.",
            "mathematics": "Analytic refinements conditional on the stated chain, independence, mass, success, and cost hypotheses.",
            "formal_verification": "No new Lean proof or modified Comparator result is claimed by this report.",
            "implementation": "Schedule utilities and small exact-law checks; no full universal sampler or FPRAS implementation.",
            "cost": "Counts and ratios are theorem-schedule allowances, not measured runtime or end-to-end bit-cost improvements.",
            "exactness_obligation": "Every changed sampler must tabulate its actual new law, including all fallback mass; revised machine costs remain to prove.",
        },
        "outer_sampling": {
            "input": {"rows": [3, 3], "columns": [3, 3], "d": d, "b": b, "k": k, "note": "Literal manuscript scales on a four-table fiber, used only to illustrate schedule slack."},
            "published": {key: magnitude(value) for key, value in old_outer.items()},
            "initial_review_existing_gap": {key: magnitude(value) for key, value in review_outer.items()},
            "refined_existing_gap": exact_record(asdict(refined_outer)),
            "published_to_refined_steps_ratio": ratio(old_outer["steps_per_trial"], refined_outer.steps_per_trial),
            "review_to_refined_steps_ratio": ratio(review_t, refined_outer.steps_per_trial),
            "updated_denominator_budget": exact_record(asdict(dyadic_denominator_budget(refined_outer, dense_schedule(d, refined_outer.dense_accuracy_bits)))),
        },
        "dense_sampling": {
            "input": {"d": d, "h": h, "scales": "A=d^4, B=d^8"},
            "published": {key: magnitude(value) for key, value in old_dense.items()},
            "initial_review": {key: magnitude(value) for key, value in review_dense.items()},
            "refined": exact_record(asdict(refined_dense)),
            "extracted_inverse_gap_improvement_factor": ratio(old_dense_gap, int(refined_dense.inverse_gap_bound)),
            "review_to_refined_steps_ratio": ratio(review_dense["steps_per_trial"], refined_dense.steps_per_trial),
            "bin_transition_reserved_bits": {"published": ceil_log2(8*d)+8*d**5, "adjacent_exponent_bound": ceil_log2(8*d)+1},
        },
        "exact_correction": {
            "certified_cost_exponent_assumed": 500,
            "published": {"gate_bits": old_gate, "accuracy_bits": 2*old_gate},
            "initial_review": {"gate_bits": review_gate, "accuracy_bits": review_gate+d*b},
            "refined_generic": exact_record(asdict(refined_exact)),
            "refined_with_count_bound": exact_record(asdict(instance_exact)),
            "count_bound": count_bound,
            "published_to_refined_accuracy_bits_ratio": ratio(2*old_gate, instance_exact.accuracy_bits),
            "gate_expected_reads": "2 - 2^(1-D), strictly below 2; worst case D",
            "expected_exponential_cost_multiplier": "1 with zero slack bits; 2^(-s) with s slack bits",
        },
        "inner_counting": {
            "input": {"d": inner_d, "B": inner_b, "H": height, "xi": str(xi), "theta": str(theta), "status": "Abstract oracle-parameter illustration, not a complete source instance or measured run."},
            "published": exact_record({"samples_per_average": old_n, "draw_bound": old_q, "steps_per_bin_sample": old_steps}),
            "initial_review": exact_record({"samples_per_average": review_n, "draw_bound": review_q, "steps_per_bin_sample": review_steps}),
            "refinements": {name: exact_record(asdict(schedule)) for name, schedule in improved_inner.items()},
            "correction_rounding_budgets": {
                "source_sigma": exact_record(asdict(correction_rounding_budget(previous.sigma))),
                "product_sigma": exact_record(asdict(correction_rounding_budget(product_policy.sigma))),
                "product_sigma_sharp_support": exact_record(asdict(correction_rounding_budget(best.sigma, correction_bounds=(best.correction_lower_bound, best.correction_upper_bound)))),
            },
            "sharp_support_hypotheses": "Requires the original source bin populations N>=100*d*B, at most d free coordinates, and scaled penalty Lipschitz<=1/8; abstract d,B,H inputs alone do not certify these facts.",
            "product_error_certificate": exact_record({
                "factor_count_bound": height+2,
                "sum_of_factor_tolerances": (height+2)*best.sigma,
                "lower_product_bound": 1-(height+2)*best.sigma,
                "upper_product_bound": 1/(1-(height+2)*best.sigma),
                "requested_lower_bound": 1-xi,
                "requested_upper_bound": 1+xi,
            }),
            "previous_to_product_sigma_ratio": ratio(product_policy.sigma.numerator*previous.sigma.denominator, product_policy.sigma.denominator*previous.sigma.numerator),
            "previous_to_product_correction_sample_ratio": ratio(previous.correction_samples, product_policy.correction_samples),
            "previous_to_product_ratio_sample_ratio": ratio(previous.ratio_samples_per_average, product_policy.ratio_samples_per_average),
            "previous_to_product_draw_bound_ratio": ratio(previous.total_draw_bound, product_policy.total_draw_bound),
            "previous_to_product_bin_transition_bound_ratio": ratio((height*previous.ratio_samples_per_average+previous.correction_samples)*previous.steps_per_bin_sample, (height*product_policy.ratio_samples_per_average+product_policy.correction_samples)*product_policy.steps_per_bin_sample),
            "product_to_sharp_support_correction_sample_ratio": ratio(product_policy.correction_samples, best.correction_samples),
            "product_to_sharp_support_draw_bound_ratio": ratio(product_policy.total_draw_bound, best.total_draw_bound),
            "product_to_sharp_support_bin_transition_bound_ratio": ratio((height*product_policy.ratio_samples_per_average+product_policy.correction_samples)*product_policy.steps_per_bin_sample, (height*best.ratio_samples_per_average+best.correction_samples)*best.steps_per_bin_sample),
            "annealing_step_comparison": {
                str(step): {
                    "schedule": exact_record(asdict(schedule)),
                    "full_schedule_reused_at_this_step_bin_transitions": str((step*best.ratio_samples_per_average+best.correction_samples)*best.steps_per_bin_sample),
                    "indexed_schedule_bin_transitions": str((step*schedule.ratio_samples_per_average+schedule.correction_samples)*schedule.steps_per_bin_sample),
                    "same_step_bin_transition_bound_reduction": ratio((step*best.ratio_samples_per_average+best.correction_samples)*best.steps_per_bin_sample, (step*schedule.ratio_samples_per_average+schedule.correction_samples)*schedule.steps_per_bin_sample),
                }
                for step, schedule in indexed_schedules.items()
            },
            "review_to_refined_correction_sample_ratio": ratio(review_n, best.correction_samples),
            "review_to_refined_ratio_sample_ratio": ratio(review_n, best.ratio_samples_per_average),
            "review_to_refined_draw_bound_ratio": ratio(review_q, best.total_draw_bound),
            "review_to_refined_bin_transition_bound_ratio": ratio((height+1)*review_n*review_steps, (height*best.ratio_samples_per_average+best.correction_samples)*best.steps_per_bin_sample),
            "extracted_inverse_gap_improvement_factor": ratio(old_inner_gap, int(best.inverse_gap_bound)),
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    content = json.dumps(report(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(content, encoding="utf-8")
        print(args.output)
    else:
        print(content, end="")


if __name__ == "__main__":
    main()
