"""Reproduce exact padding counts, incidence checks, and dimension growth.

Run from the repository root:
    PYTHONPATH=src python3 experiments/padding_barrier.py
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import time

from contingency115.padding import (count_padded_tables,
                                    half_acceptance_necessary_margin,
                                    padding_target_indegree)


ROOT = Path(__file__).resolve().parents[1]


def finite_case(n, u, ell, *, max_candidates=100_000, max_incidences=1_000_000):
    """Direct Cartesian enumeration, independent of the count formula."""
    cap, row_sum = u + 2 * ell, u + n * ell
    candidates = (cap + 1)**(n - 1)
    if candidates > max_candidates:
        raise ValueError("direct-enumeration candidate budget exceeded")
    rows = set()
    for prefix in product(range(cap + 1), repeat=n - 1):
        last = row_sum - sum(prefix)
        if 0 <= last <= cap:
            rows.add((*prefix, last))
    good = {row for row in rows if all(ell <= value <= cap - ell for value in row)}
    if len(good) * ell * n * (n - 1) > max_incidences:
        raise ValueError("direct-incidence budget exceeded")
    incoming = Counter()
    for row in good:
        for j in range(n):
            for k in range(n):
                if j == k:
                    continue
                for h in range(ell):
                    target = list(row)
                    amount = row[j] - h
                    target[j] -= amount
                    target[k] += amount
                    target = tuple(target)
                    if target not in rows or target in good:
                        raise AssertionError("switching left the bad target space")
                    if [index for index, value in enumerate(target) if value < ell] != [j]:
                        raise AssertionError("switching did not produce a unique low cell")
                    incoming[target] += 1
    counted = count_padded_tables(n, u, ell)
    if (counted.good, counted.total) != (len(good), len(rows)):
        raise AssertionError("exact formula disagrees with direct enumeration")
    if any(incoming[row] != padding_target_indegree(row, u, ell) for row in rows):
        raise AssertionError("incoming multiplicity disagrees with direct incidence count")
    if max(incoming.values()) > u + 1:
        raise AssertionError("indegree bound failed")
    if counted.success_probability > counted.success_upper_bound:
        raise AssertionError("success upper bound failed")
    incidences = sum(incoming.values())
    if incidences != len(good) * ell * n * (n - 1):
        raise AssertionError("outgoing-incidence accounting failed")
    if n == 2 and counted.success_probability != counted.success_upper_bound:
        raise AssertionError("two-column equality failed")
    return {"columns": n, "margin": u, "padding": ell,
            "candidate_prefixes": candidates, "good": len(good), "total": len(rows),
            "incidences": incidences, "outdegree_per_good_table": ell * n * (n - 1),
            "maximum_indegree": max(incoming.values()), "indegree_bound": u + 1,
            "bad_rows_outside_switching_image": len(rows) - len(good) - len(incoming),
            "success_probability": str(counted.success_probability),
            "success_upper_bound": str(counted.success_upper_bound),
            "all_checks_passed": True}


def growth_case(n, regime):
    d = 3 * n + 13
    ell = 32 * d**3
    threshold = half_acceptance_necessary_margin(n, ell)
    u = {"linear_Ln": ell * n,
         "quadratic_Ln_squared": ell * n**2,
         "quadratic_2Ln_squared": 2 * ell * n**2,
         "necessary_half_threshold": threshold}[regime]
    started = time.perf_counter()
    result = count_padded_tables(n, u, ell)
    elapsed = time.perf_counter() - started
    if result.success_probability > result.success_upper_bound:
        raise AssertionError("exact probability exceeds proved upper bound")
    return {"columns": n, "dimension_d": d, "regime": regime,
            "margin_U": str(u), "padding_L": str(ell),
            "necessary_half_acceptance_margin": str(threshold),
            "margin_over_Ln_squared": str(Fraction(u, ell * n**2)),
            "good_count": str(result.good), "total_count": str(result.total),
            "good_count_bits": result.good.bit_length(), "total_count_bits": result.total.bit_length(),
            "success_probability": str(result.success_probability),
            "success_probability_decimal": float(result.success_probability),
            "success_upper_bound": str(result.success_upper_bound),
            "success_upper_bound_decimal": float(result.success_upper_bound),
            "half_acceptance_actual": result.success_probability >= Fraction(1, 2),
            "necessary_condition_satisfied": u >= threshold,
            "plan": asdict(result.plan), "count_seconds": elapsed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "reports" / "padding-barrier.json")
    args = parser.parse_args()
    finite = [finite_case(n, u, ell) for n in range(2, 6)
              for u in range(1, 5) for ell in (1, 2)]
    growth = [growth_case(n, regime) for n in (2, 3, 4, 8, 16, 32, 64, 100)
              for regime in ("linear_Ln", "quadratic_Ln_squared", "quadratic_2Ln_squared",
                             "necessary_half_threshold")]
    source_paths = ("src/contingency115/padding.py", "tests/test_padding_barrier.py",
                    "experiments/padding_barrier.py", "docs/padding-barrier.md")
    report = {
        "schema_version": 1,
        "result": "necessary_margin_scale_for_fixed_uniform_padded_rejection",
        "family": "ordinary 2-by-n, original rows (U,(n-1)U), all columns U, every cell padded by L",
        "proved_success_upper_bound": "(U+1)/(U+1+L*n*(n-1))",
        "half_acceptance_necessary_condition": "U >= L*n*(n-1)-1",
        "formal_verification": "not claimed",
        "novelty_priority": "not claimed",
        "python_version": platform.python_version(),
        "source_sha256": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                          for path in source_paths},
        "upstream_context": {"repository": "https://github.com/openai/math",
                             "commit": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
                             "manuscript": "Exact Uniform Sampling of Contingency Tables with Arbitrary Margins"},
        "finite_incidence_checks": finite,
        "growth_cases": growth,
        "summary": {"finite_cases": len(finite), "incidences_checked": sum(case["incidences"] for case in finite),
                    "target_rows_checked": sum(case["total"] for case in finite),
                    "growth_cases": len(growth), "all_checks_passed": True},
        "scope_limits": [
            "Only this uniform enlarged-table proposal and unpadding rejection rule are covered.",
            "No lower bound on all algorithms, mixing gaps, different padding rules, or the necessary size of L follows.",
            "The half-acceptance margin condition is necessary and generally not sufficient.",
            "Exact integer/rational calculations corroborate a universal elementary proof; they are not Lean verification.",
            "Decimal probabilities are display aids; all comparisons use exact rational arithmetic."
        ]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({**report["summary"],
                      "n100_probabilities": {case["regime"]: case["success_probability_decimal"]
                                             for case in growth if case["columns"] == 100}}, indent=2))


if __name__ == "__main__":
    main()
