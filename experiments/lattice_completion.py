#!/usr/bin/env python3
"""Replay bounded adjacent-lattice codec checks, without a completion oracle."""

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path

from contingency115.lattice_completion import (
    decode_completion, encode_completion, plan_dense_completion, plan_lattice_completion,
)
from contingency115.tables import ComputationBudgetExceeded, TableProblem, _integer


def independent_two_row_tables(problem, *, max_candidates):
    """Exhaust an independently parametrized fiber or fail before enumeration.

    First-row entries independently range through each column's capacity;
    their sum selects the required first-row margin. The second row is then
    forced. A conservative Cartesian work bound is checked before iteration,
    so an exhausted case cannot emit biased partial counts or samples.
    """
    max_candidates = _integer(max_candidates, "max_candidates", positive=True)
    if problem.shape[0] != 2:
        raise ValueError("this independent enumerator supports exactly two rows")
    work = 1
    for column in problem.column_sums:
        if column+1 > max_candidates//work:
            raise ComputationBudgetExceeded("Cartesian candidate allowance exceeded before enumeration")
        work *= column+1
    tables = tuple((top, tuple(c-x for c, x in zip(problem.column_sums, top)))
                   for top in product(*(range(c+1) for c in problem.column_sums))
                   if sum(top) == problem.row_sums[0])
    return tables, work


def finite_case(rows, columns, k, *, max_candidates):
    plan = plan_lattice_completion(TableProblem(rows, columns), k)
    base = {"row_sums": rows, "column_sums": columns, "k": k,
            "dimension": plan.dimension, "max_candidates_per_fiber": max_candidates,
            "fine_row_sums": plan.fine.row_sums,
            "fine_column_sums": plan.fine.column_sums,
            "fine_total": sum(plan.fine.row_sums)}
    try:
        originals, original_work = independent_two_row_tables(plan.original, max_candidates=max_candidates)
        fine_tables, fine_work = independent_two_row_tables(plan.fine, max_candidates=max_candidates)
    except ComputationBudgetExceeded as exc:
        return {**base, "status": "budget_exceeded", "reason": str(exc),
                "count_result": None, "acceptance_result": None}
    groups = Counter()
    max_error = Fraction(0)
    signed_rejected_margins_checked = 0
    for fine in fine_tables:
        decoded = decode_completion(plan, fine)
        candidate = decoded.candidate
        assert tuple(map(sum, candidate)) == rows
        assert tuple(sum(candidate[i][j] for i in range(2)) for j in range(len(columns))) == columns
        error = max((abs(x) for row in decoded.rounding_errors for x in row), default=Fraction(0))
        assert error < 2
        max_error = max(max_error, error)
        if decoded.accepted:
            groups[candidate] += 1
            assert encode_completion(plan, candidate, decoded.offsets) == fine
        else:
            assert decoded.table is None
            signed_rejected_margins_checked += 1
    assert set(groups) == set(originals)
    assert set(groups.values()) == {plan.preimages_per_table}
    encoded_checked = 0
    for original in originals:
        a, b = plan.original.shape
        for flat in product(range(k), repeat=plan.dimension):
            offsets = tuple(tuple(flat[i*(b-1)+j] for j in range(b-1)) for i in range(a-1))
            fine = encode_completion(plan, original, offsets)
            assert fine in fine_tables
            decoded = decode_completion(plan, fine)
            assert decoded.table == original and decoded.offsets == offsets
            encoded_checked += 1
    accepted = sum(groups.values())
    return {**base, "status": "complete", "original_count": len(originals),
            "fine_count": len(fine_tables), "accepted_count": accepted,
            "rejected_count": len(fine_tables)-accepted,
            "acceptance": str(Fraction(accepted, len(fine_tables))),
            "preimages_per_original": plan.preimages_per_table,
            "decoded_output_groups": [{"table": table, "preimages": groups[table]}
                                      for table in sorted(groups)],
            "candidate_work": {"original": original_work, "fine": fine_work},
            "roundtrips_checked": encoded_checked,
            "signed_rejected_margins_checked": signed_rejected_margins_checked,
            "maximum_absolute_rounding_error": str(max_error)}


def actual_scale_case(a, b, d):
    original = tuple((3*d,)*b for _ in range(a))
    plan = plan_dense_completion(TableProblem((3*b*d,)*a, (3*a*d,)*b), d)
    k = plan.codec.k
    offsets = tuple(tuple((i+j) % 2*(k-1) for j in range(b-1)) for i in range(a-1))
    fine = encode_completion(plan.codec, original, offsets)
    decoded = decode_completion(plan.codec, fine)
    assert decoded.table == original and decoded.offsets == offsets
    assert sum(plan.codec.fine.row_sums) == k*(sum(plan.codec.original.row_sums)+2*a*b)
    alpha = plan.geometric_count_ratio_upper_bound
    assert alpha < 4 and plan.conditional_acceptance_lower_bound > Fraction(1, 4)
    return {"shape": [a, b], "dimension": plan.codec.dimension,
            "ambient_d_bit_length": d.bit_length(),
            "uses_minimal_shape_d": d == 10+(a+1)*(b+1),
            "L_bit_length": plan.L.bit_length(), "k_bit_length": k.bit_length(),
            "original_cell_max_bit_length": max(x.bit_length() for row in original for x in row),
            "fine_cell_max_bit_length": max(x.bit_length() for row in fine for x in row),
            "fine_total_bit_length": sum(plan.codec.fine.row_sums).bit_length(),
            "alpha_numerator_bit_length": alpha.numerator.bit_length(),
            "alpha_denominator_bit_length": alpha.denominator.bit_length(),
            "exact_alpha_below_four": True,
            "roundtrip": "passed", "fiber_enumeration": "not attempted",
            "timing_or_end_to_end_runtime_claim": None}


def run():
    cases = []
    for rows, columns in (((0, 0), (0, 0)), ((1, 1), (1, 1)), ((0, 2), (1, 1))):
        for k in (1, 2, 3):
            cases.append(finite_case(rows, columns, k, max_candidates=10_000))
    for rows, columns in (((1, 2), (1, 1, 1)), ((0, 1), (0, 1, 0))):
        for k in (1, 2):
            cases.append(finite_case(rows, columns, k, max_candidates=10_000))
    # This failure is deliberately retained to verify the report's budget path.
    cases.append(finite_case((1, 2), (1, 1, 1), 2, max_candidates=2))
    root = Path(__file__).resolve().parents[1]
    return {
        "schema_version": 1,
        "upstream_commit": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
        "scope": "Ordinary nonnegative equal-total fixed-margin tables; semantically unrestricted cell bounds; nonempty row/column index sets.",
        "codec": {"fine_margins": "k*(R_i+2b), k*(P_j+2a)",
                  "fine_total": "k*(H+2ab)",
                  "decode": "floor each full northwest prefix divided by k, take second differences, subtract 2 per cell; accept iff all cells are nonnegative",
                  "encode": "k*(X+2J)+secondDiff(u), with interior u in {0,...,k-1} and zero prefix boundary",
                  "preimages_each_original": "k^((a-1)*(b-1))",
                  "cell_error": "absolute error <2 for k>1, and zero for k=1"},
        "dense_scale_plan": {"k": "d^12", "L": "3d",
                             "dimension_allowance": "d>=10+(a+1)*(b+1); ambient d may be larger",
                             "residual_requirements": "R_i>=3bd and P_j>=3ad",
                             "dilation_reason": "Retain old DenseScaleConditions minimum-margin allowance after dilation; no large-scale completion draw is implemented."},
        "conditional_geometric_bound": {
            "alpha": "((L+2+2/k)/(L-2))^((a-1)*(b-1))",
            "count_comparison": "N_fine <= alpha*k^((a-1)*(b-1))*N_original",
            "arithmetic_condition": "L=3d, d>=10+(a+1)*(b+1), k>=2d imply alpha<4",
            "uniform_fine_acceptance": ">=1/alpha>1/4",
            "universal_proof_status": "Reviewed mathematical volume/count argument; not a Python or Lean proof. Finite enumeration here is test evidence only.",
            "sampling_assumptions": "Acceptance interpretation requires an exact uniform fine-table draw. No oracle, iid retry adapter, or machine-cost guarantee is supplied."},
        "finite_fiber_replay": cases,
        "actual_scale_roundtrips": [actual_scale_case(a, b, d)
                                    for a, b in ((1, 1), (1, 5), (2, 2), (2, 3), (3, 4))
                                    for d in (10+(a+1)*(b+1), 10**200)],
        "reproduce": "PYTHONPATH=src python3 experiments/lattice_completion.py --output reports/lattice-completion.json",
        "source_sha256": {path: hashlib.sha256((root/path).read_bytes()).hexdigest()
                          for path in ("experiments/lattice_completion.py", "src/contingency115/lattice_completion.py",
                                       "src/contingency115/tables.py", "tests/test_lattice_completion.py")},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = json.dumps(run(), indent=2)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
