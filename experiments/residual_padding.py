"""Exact reduced-padding checks on a genuine weighted completion block.

The walk execution checks feasibility and finite accounting, not mixing.
"""
import argparse
from dataclasses import asdict
from fractions import Fraction as F
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from contingency115.general_defect_chain import GeneralDefectChain
from contingency115.general_defect_terminal import GeneralRepairTerminal
from contingency115.general_scales import reduced_completion_scales
from contingency115.ideal_chain import build_rescaled_ideal_chain
from contingency115.small_completion import SmallCompletionOracle
from contingency115.tables import ExactTableSampler, TableProblem


def run():
    problem = TableProblem((46, 46, 1), (46, 46, 1))
    scales = reduced_completion_scales(problem, large_row_count=2, large_column_count=2)
    assert (scales.U, scales.L) == (46, 2)
    backend = build_rescaled_ideal_chain(problem, U=scales.U, L=scales.L)
    oracle = SmallCompletionOracle(max_margin=scales.completion_margin_bound,
                                   word_bits=16, max_cells=4)
    chain = GeneralDefectChain(problem, U=scales.U, L=scales.L, oracle=oracle,
                              geometry_bits=16, star_trials=16)
    terminal = GeneralRepairTerminal(chain, acceptance_bits=16)
    acceptance = []
    for i, state in enumerate(backend.states):
        assert sum(chain.completion_request(state).row_sums) <= chain.large_capacity
        for j in backend.neighbors[i]:
            acceptance.append(F(backend.acceptance_counts[i][j], backend.completion_counts[i]))
        if not state.balanced:
            targets = [chain.proposal(state, slot) for slot in range(chain.Q)]
            actual = [target for target in targets if target is not None]
            assert len(actual) == len(set(actual))
            assert set(actual) == {backend.states[j] for j in backend.neighbors[i]}
    assert min(acceptance) >= F(1, 2)
    original = ExactTableSampler(problem).count()
    padded = ExactTableSampler(TableProblem((50, 50, 1), (50, 50, 1))).count()
    assert (original, padded) == (231, 251) and padded <= 2*original
    state = next(state for state in backend.states if not state.balanced)
    rng = random.Random(11514)
    bits = calls = accepted = 0
    for step in range(128):
        move = chain.step(state, rng)
        state = move.state
        bits += move.fair_bits
        calls += move.oracle_calls
        if (step+1) % 8 == 0:
            draw = terminal.terminal(state, rng)
            bits += draw.fair_bits
            calls += draw.oracle_calls
            if draw.table is not None:
                problem.validate_table(draw.table)
                accepted += 1
    planned_bits = 128*chain.max_fair_bits + 16*terminal.planned_fair_bits
    assert bits <= planned_bits

    # This refutes replacing the full-table donor dimension in padding growth
    # by the completion block's donor dimension (which is zero here).
    recurrence_counts = [ExactTableSampler(TableProblem(margins, margins)).count()
                         for margins in ((2, 1, 1, 1), (3, 1, 1, 1))]
    assert recurrence_counts == [33, 34]
    return {
        "evidence": "exact finite graph and count checks; bounded feasibility execution",
        "scales": asdict(scales), "states": len(backend.states),
        "directed_edges_checked": len(acceptance), "minimum_acceptance": min(acceptance),
        "completion_weights": sorted(set(backend.completion_counts)),
        "ordinary_count": original, "padded_count": padded, "padded_ratio": F(padded, original),
        "execution": {"steps": 128, "marks": 16, "accepted": accepted,
                      "fair_bits": bits, "planned_fair_bits": planned_bits,
                      "oracle_calls": calls, "endpoint_accuracy": "unmeasured"},
        "full_table_recurrence_obstruction": {"before": 33, "after": 34,
                                              "completion_block": [1, 1]},
        "checks": "passed",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    if not __debug__:
        parser.error("run without -O so the exact checks remain enabled")
    args = parser.parse_args()
    rendered = json.dumps(run(), default=str, indent=2)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
        print(f"Wrote {args.output}: reduced-padding checks passed.")
    else:
        print(rendered, end="")
