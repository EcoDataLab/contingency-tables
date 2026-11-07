"""Exact shape-degree/scaling checks and bounded execution on a weighted core.

Enumeration is confined to this finite reference audit. The general transition,
completion and terminal implementations do not enumerate the state space.
The executed walk is a feasibility diagnostic, not a mixing-time experiment.
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
from contingency115.general_defect_chain import GeneralDefectChain, defect_degree_bound
from contingency115.general_defect_terminal import GeneralRepairTerminal
from contingency115.general_scales import two_by_two_core_scales
from contingency115.ideal_chain import build_rescaled_ideal_chain
from contingency115.small_completion import SmallCompletionOracle
from contingency115.tables import ExactTableSampler, TableProblem


def type_bounds(m, n, r, c):
    a, b = m-r, n-c
    A, B = a*c, r*b
    counts = {"SS": a*b, "LS": B, "SL": A}
    bounds = {
        ("SS", "SS"): 2*(m+n)-3,
        ("SS", "LS"): n+2*m+A+B-3,
        ("SS", "SL"): 2*n+m+A+B-3,
        ("LS", "LS"): 2*(A+B+m)-3,
        ("SL", "SL"): 2*(A+B+n)-3,
        ("LS", "SL"): 2*(A+B)+m+n-4,
    }
    return {tuple(sorted(k)): v for k, v in bounds.items()
            if all(counts[t] for t in k) and (k[0] != k[1] or counts[k[0]] >= 2)}


def audit_case(rows, columns, U, L):
    problem = TableProblem(rows, columns)
    reference = build_rescaled_ideal_chain(problem, U=U, L=L)
    m, n = problem.shape
    r, c, p = len(reference.large_rows), len(reference.large_columns), len(reference.small_cells)
    Q = defect_degree_bound(m, n, m-r, n-c)
    bounds = type_bounds(m, n, r, c)
    observed = {}

    def kind(label):
        i, j = reference.small_cells[label]
        return ("L" if i in reference.large_rows else "S") + ("L" if j in reference.large_columns else "S")

    for index, state in enumerate(reference.states):
        if state.balanced:
            continue
        s, t = state.defect_labels()
        pair = tuple(sorted((kind(s), kind(t))))
        degree = len(reference.neighbors[index])
        assert degree <= bounds[pair] and degree <= Q <= 4*p-3
        name = ",".join(pair)
        observed[name] = max(observed.get(name, 0), degree)
    minimum_acceptance = min(F(reference.acceptance_counts[i][j], reference.completion_counts[i])
                             for i, row in enumerate(reference.neighbors) for j in row)
    half_premise = L >= max(1, 3*max(0, r-1)*max(0, c-1))
    if half_premise:
        assert minimum_acceptance >= F(1, 2)
    return reference, dict(
        rows=rows, columns=columns, U=U, L=L, large_shape=(r, c), small_cells=p,
        degree_bound=Q, previous_degree_bound=8*p-7,
        observed_type_max_degrees=observed, completion_weights=sorted(set(reference.completion_counts)),
        minimum_acceptance=minimum_acceptance, half_acceptance_premise=half_premise,
        checked_defects=sum(not s.balanced for s in reference.states))


def run():
    fixtures = [((2, 1), (2, 1), 2, 1), ((4, 4, 1), (4, 4, 1), 4, 1),
                ((4, 4, 1), (4, 4, 1), 4, 78), ((2, 2, 1), (2, 2, 1), 2, 1),
                ((4, 1, 1), (3, 3), 3, 1), ((2, 2, 2), (4, 2), 3, 1),
                ((70, 70, 1), (70, 70, 1), 70, 3)]
    cases = []
    for fixture in fixtures:
        reference, record = audit_case(*fixture)
        cases.append(record)
    # The last fixture meets the new scales, with actual nonconstant weights.
    scales = two_by_two_core_scales(reference.problem)
    N = ExactTableSampler(reference.problem).count()
    P = ExactTableSampler(TableProblem((76, 76, 1), (76, 76, 1))).count()
    assert (N, P) == (351, 381) and P <= 2*N
    oracle = SmallCompletionOracle(max_margin=scales.completion_margin_bound, word_bits=16, max_cells=4)
    chain = GeneralDefectChain(reference.problem, U=scales.U, L=scales.L, oracle=oracle,
                              geometry_bits=16, star_trials=16)
    terminal = GeneralRepairTerminal(chain, acceptance_bits=16)
    # Every compact proposal matches the independent physical reference graph.
    for i, state in enumerate(reference.states):
        if state.balanced:
            continue
        targets = [chain.proposal(state, slot) for slot in range(chain.Q)]
        actual = [state for state in targets if state is not None]
        expected = {reference.states[j] for j in reference.neighbors[i]}
        assert len(actual) == len(set(actual)) and set(actual) == expected
    state = next(state for state in reference.states if not state.balanced)
    rng = random.Random(1152026)
    bits = calls = work = accepted = 0
    for step in range(256):
        move = chain.step(state, rng)
        state = move.state
        bits += move.fair_bits
        calls += move.oracle_calls
        work += move.oracle_work
        if (step+1) % 8 == 0:
            draw = terminal.terminal(state, rng)
            bits += draw.fair_bits
            calls += draw.oracle_calls
            work += draw.oracle_work
            if draw.table is not None:
                reference.problem.validate_table(draw.table)
                accepted += 1
    planned_bits = 256*chain.max_fair_bits + 32*terminal.planned_fair_bits
    assert bits <= planned_bits
    return {
        "evidence": "exact finite graph/count checks; bounded seeded execution only, no mixing claim",
        "cases": cases, "scaled_core": asdict(scales), "ordinary_count": N, "padded_count": P,
        "padded_ratio": F(P, N),
        "execution": {"steps": 256, "marks": 32, "accepted": accepted,
                      "fair_bits": bits, "planned_fair_bits": planned_bits,
                      "oracle_calls": calls, "oracle_logical_work": work,
                      "row_tv_allowance": chain.error.total_variation_bound,
                      "terminal_tv_allowance": terminal.error.total_variation_bound,
                      "scope": "actual finite words and feasible outputs; endpoint accuracy unmeasured"},
        "checks": "passed",
    }


def jsonable(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {key: jsonable(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [jsonable(item) for item in value]
    return value


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    if not __debug__:
        parser.error("run without -O so the exact checks remain enabled")
    args = parser.parse_args()
    rendered = json.dumps(jsonable(run()), indent=2)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
        print(f"Wrote {args.output}: seven exact cases and the bounded execution passed.")
    else:
        print(rendered, end="")
