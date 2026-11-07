"""Opt-in exact finite checks for the proposed general weighted defect trace.

Run from any directory; only the standard library and this repository are used.
The fixtures are finite evidence, not a general geometry/trace/terminal proof or
a sampler implementation. Family enumeration deliberately uses quadratic loops.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import asdict
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from contingency115.ideal_chain import IdealChainBudget, PhysicalState, build_rescaled_ideal_chain
from contingency115.tables import ExactTableSampler, TableProblem


CASES = (
    ((2, 2), (3, 1), 3, 1),
    ((3, 1), (2, 2), 3, 1),
    ((2, 2, 2), (4, 2), 3, 1),
    ((2, 1), (2, 1), 2, 1),
    ((3, 1), (3, 1), 3, 1),
    ((4, 4, 1), (4, 4, 1), 4, 1),
    ((2, 2, 1), (2, 2, 1), 2, 1),
    ((4, 4, 1), (4, 4, 1), 4, 3 * (10 + 4 * 4)),  # L = 3d = 78.
    ((2, 2), (2, 2), 3, 1),  # Both sides small.
    ((2, 1, 1), (2, 1, 1), 2, 1),  # Includes zero ordinary large-line slack.
    ((2, 2, 1), (2, 2, 1), 2, 3 * (10 + 4 * 4)),  # L=3d with a nonideal U.
)
FAMILIES = ("small_crossing_inverse_repairs", "large_crossing_inverse_repairs",
            "distinct_large_row_transfers", "distinct_large_column_transfers",
            "simultaneous_decreases")


def balanced_families(chain, balanced_index, lookup):
    """Enumerate five families and independently evaluate their count formulas."""
    cells = chain.small_cells
    locations = {cell: index for index, cell in enumerate(cells)}
    large_rows, large_columns = set(chain.large_rows), set(chain.large_columns)
    values = chain.states[balanced_index].row_view
    rows, columns = chain.problem.row_sums, chain.problem.column_sums
    row_slack = {i: rows[i] - sum(values[k] for k, cell in enumerate(cells) if cell[0] == i)
                 for i in large_rows}
    column_slack = {j: columns[j] - sum(values[k] for k, cell in enumerate(cells) if cell[1] == j)
                    for j in large_columns}
    assert all(slack >= 0 for slack in (*row_slack.values(), *column_slack.values()))
    families = [set() for _ in FAMILIES]

    def add(family, x, q):
        state = PhysicalState(tuple(x), tuple(q))
        assert state in lookup and not state.balanced
        index = lookup[state]
        assert index not in families[family], "family description has multiplicity"
        families[family].add(index)

    for s, s_cell in enumerate(cells):
        for t, t_cell in enumerate(cells):
            if s == t:
                continue
            crossing = locations.get((t_cell[0], s_cell[1]))
            if crossing is not None and values[crossing] > 0:
                x, q = list(values), list(values)
                x[t] += 1
                x[crossing] -= 1
                q[s] += 1
                q[crossing] -= 1
                add(0, x, q)
            elif (crossing is None and row_slack.get(t_cell[0], 0) > 0
                  and column_slack.get(s_cell[1], 0) > 0):
                x, q = list(values), list(values)
                x[t] += 1
                q[s] += 1
                add(1, x, q)
    for donor, (di, dj) in enumerate(cells):
        for receiver, (ri, rj) in enumerate(cells):
            if values[donor] > 0 and di in large_rows and ri in large_rows and di != ri and row_slack[ri] > 0:
                x = list(values)
                x[donor] -= 1
                x[receiver] += 1
                add(2, x, values)
            if values[donor] > 0 and dj in large_columns and rj in large_columns and dj != rj and column_slack[rj] > 0:
                q = list(values)
                q[donor] -= 1
                q[receiver] += 1
                add(3, values, q)
    for s, s_cell in enumerate(cells):
        for t, t_cell in enumerate(cells):
            if s_cell[0] in large_rows and t_cell[1] in large_columns and values[s] > 0 and values[t] > 0:
                x, q = list(values), list(values)
                x[s] -= 1
                q[t] -= 1
                add(4, x, q)

    # Closed-form counts use only entry support, line sizes and active slacks;
    # they do not inspect the enumerated family sets or graph adjacency.
    a, b = len(rows) - len(large_rows), len(columns) - len(large_columns)
    active_rows = {i for i, slack in row_slack.items() if slack > 0}
    active_columns = {j for j, slack in column_slack.items() if slack > 0}
    positive_ls = [i for (i, _), value in zip(cells, values) if i in large_rows and value > 0]
    positive_sl = [j for (_, j), value in zip(cells, values) if j in large_columns and value > 0]
    counts = (
        sum((b if i in large_rows else len(columns)) * (a if j in large_columns else len(rows)) - 1
            for (i, j), value in zip(cells, values) if value > 0),
        a * len(active_columns) * b * len(active_rows),
        b * sum(len(active_rows) - int(i in active_rows) for i in positive_ls),
        a * sum(len(active_columns) - int(j in active_columns) for j in positive_sl),
        len(positive_ls) * len(positive_sl),
    )
    enumerated = tuple(map(len, families))
    assert counts == enumerated
    union = set().union(*families)
    assert len(union) == sum(enumerated), "five families overlap"
    assert union == set(chain.neighbors[balanced_index]), "five-family partition misses graph neighbors"
    return {"balanced_state_index": balanced_index, "closed_form_N0_to_N4": counts,
            "enumerated_family_counts": enumerated, "neighbors": len(union),
            "zero_large_row_slacks": sum(slack == 0 for slack in row_slack.values()),
            "zero_large_column_slacks": sum(slack == 0 for slack in column_slack.values())}


def joint_terminal_certificate(chain, defects, balanced, partitions, state_lookup):
    """Count repaired joint preimages, then compare outputs with the original DP.

    The input law for this count check is uniform on enumerated
    (defect, completion) pairs. This is the completion-retaining repair,
    distinct from the star translation used for physical transitions.
    """
    rows, columns = chain.problem.row_sums, chain.problem.column_sums
    assert min(rows) > 0 and min(columns) > 0 and chain.U >= 2 and chain.L >= 1
    cells = chain.small_cells
    small_locations = {cell: index for index, cell in enumerate(cells)}
    large_row_locations = {row: index for index, row in enumerate(chain.large_rows)}
    large_column_locations = {column: index for index, column in enumerate(chain.large_columns)}
    balanced_completions = {i: set(chain.completions[i]) for i in balanced}
    observed = Counter()
    joint_defect_pairs = sum(chain.completion_counts[i] for i in defects)
    for index in sorted(defects):
        state = chain.states[index]
        s, t = state.defect_labels()
        crossing = cells[t][0], cells[s][1]
        repaired = list(state.row_view)
        repaired[t] -= 1
        if crossing in small_locations:
            repaired[small_locations[crossing]] += 1
        target = state_lookup[PhysicalState(tuple(repaired), tuple(repaired))]
        assert target in balanced
        for completion in chain.completions[index]:
            repaired_completion = [list(row) for row in completion]
            if crossing not in small_locations:
                i, j = large_row_locations[crossing[0]], large_column_locations[crossing[1]]
                repaired_completion[i][j] += 1
            repaired_completion = tuple(tuple(row) for row in repaired_completion)
            assert repaired_completion in balanced_completions[target]
            if all(value >= chain.L for row in repaired_completion for value in row):
                observed[target, repaired_completion] += 1

    a, b = len(rows) - len(chain.large_rows), len(columns) - len(chain.large_columns)
    c0 = max(a * (len(columns) * a - 1), b * (len(rows) * b - 1))
    assert c0 > 0
    expected, output_masses, successful_outputs, loads = {}, defaultdict(Fraction), set(), set()
    for partition in partitions:
        target = partition["balanced_state_index"]
        N0, N1 = partition["closed_form_N0_to_N4"][:2]
        load = N0 + N1
        assert c0 <= load <= len(cells) * (len(cells) - 1)
        for completion in chain.completions[target]:
            if not all(value >= chain.L for row in completion for value in row):
                continue
            expected[target, completion] = load
            loads.add(load)
            table = chain._output_pair(target, completion)
            assert table is not None and table not in successful_outputs
            successful_outputs.add(table)
            output_masses[table] += Fraction(observed[target, completion], joint_defect_pairs) * Fraction(c0, load)
    assert expected == dict(observed), "successful joint repair load differs from N0+N1"
    assert set(output_masses.values()) == {Fraction(c0, joint_defect_pairs)}

    # Independent original-fiber enumeration uses the ordinary-margin DP and
    # unranking, not physical states, five-family counts or joint repair.
    oracle = ExactTableSampler(chain.problem, max_states=chain.budget.max_dp_states,
                               max_transitions=chain.budget.max_dp_transitions)
    original_count = oracle.count()
    original_tables = {oracle.unrank(rank) for rank in range(original_count)}
    assert len(original_tables) == original_count
    assert successful_outputs == original_tables
    assert len(expected) == original_count
    corrected_success = sum(output_masses.values(), Fraction(0))
    assert corrected_success == Fraction(original_count * c0, joint_defect_pairs)
    return {
        "input_law": "Uniform over enumerated defect/completion pairs",
        "joint_defect_pairs": joint_defect_pairs, "successful_balanced_joint_pairs": len(expected),
        "successful_defect_joint_preimages": sum(observed.values()), "inverse_load_values": sorted(loads),
        "inverse_load_equals_N0_plus_N1": True, "c0": c0,
        "c0_lower_bound_and_p_times_p_minus_one_upper_bound": True,
        "zero_slack_balanced_profiles": sum(bool(p["zero_large_row_slacks"] or p["zero_large_column_slacks"])
                                             for p in partitions),
        "equal_unconditional_corrected_table_masses": True,
        "unconditional_success_mass_per_table": str(Fraction(c0, joint_defect_pairs)),
        "corrected_success_probability": str(corrected_success),
        "finite_success_at_least_1_over_8p": corrected_success >= Fraction(1, 8 * len(cells)),
        "comparison_1_over_8p": str(Fraction(1, 8 * len(cells))),
        "independent_original_table_count": original_count,
        "output_table_set_equals_independent_unrank_oracle": True,
        "successful_balanced_joint_pairs_bijective_with_original_tables": True,
        "output_table_set_sha256": sha256(json.dumps(sorted(original_tables), separators=(",", ":")).encode()).hexdigest(),
        "independent_original_fiber_dp_stats": oracle.stats,
    }


def zero_margin_scope_obstruction():
    """Expected scope failure; do not apply the positive-margin terminal rule."""
    chain = build_rescaled_ideal_chain(TableProblem((2, 0, 0), (2, 0, 0)), U=2, L=1)
    balanced = {i for i, state in enumerate(chain.states) if state.balanced}
    defects = set(range(len(chain.states))) - balanced
    lookup = {state: i for i, state in enumerate(chain.states)}
    partitions = [balanced_families(chain, i, lookup) for i in sorted(balanced)]
    a = len(chain.problem.row_sums) - len(chain.large_rows)
    b = len(chain.problem.column_sums) - len(chain.large_columns)
    c0 = max(a * (len(chain.problem.column_sums) * a - 1), b * (len(chain.problem.row_sums) * b - 1))
    loads = [sum(partition["closed_form_N0_to_N4"][:2]) for partition in partitions]
    assert len(chain.small_cells) == 8 and c0 == 10 and loads == [4]
    invalid_correction = Fraction(c0, loads[0])
    assert invalid_correction == Fraction(5, 2) and invalid_correction > 1
    try:
        joint_terminal_certificate(chain, defects, balanced, partitions, lookup)
    except AssertionError:
        rejected = True
    else:
        raise AssertionError("nonpositive-margin terminal input was not rejected")
    return {"rows": chain.problem.row_sums, "columns": chain.problem.column_sums,
            "U": chain.U, "L": chain.L, "p": len(chain.small_cells), "c0": c0,
            "inverse_load_N0_plus_N1": loads[0], "invalid_c0_over_load": str(invalid_correction),
            "positive_margin_guard_rejects": rejected,
            "conclusion": "Positive ordinary margins are essential to the c0 lower bound and terminal correction."}


def trace_certificate(chain, defects, balanced, conductance):
    """Row domination and weighted-star energy identity, using exact fractions.

    Conductances are unnormalized. Full energy sums each graph edge once;
    trace energy sums each DD edge once plus each eliminated star's unordered
    defect pairs. Overlapping stars add their contributions.
    """
    weights = chain.completion_counts
    rates = {x: Fraction(sum(conductance(x, y) for y in chain.neighbors[x] if y in defects))
             for x in defects}
    # State index is a simple nonconstant defect observable on every fixture.
    harmonic = {x: Fraction(x) for x in defects}
    stars = []
    for center in balanced:
        incident = {x: conductance(center, x) for x in chain.neighbors[center]}
        total = sum(incident.values())
        stars.append((incident, total))
        harmonic[center] = (sum((weight * harmonic[x] for x, weight in incident.items()), Fraction(0)) / total
                            if total else Fraction(0))
        if total:
            for x, weight in incident.items():
                rates[x] += Fraction(weight * (total - weight), total)
    assert len(set(harmonic[x] for x in defects)) > 1
    assert all(rates[x] <= weights[x] * len(chain.neighbors[x]) for x in defects)
    full_energy = sum((conductance(i, j) * (harmonic[i] - harmonic[j]) ** 2
                       for i, neighbors in enumerate(chain.neighbors) for j in neighbors if i < j), Fraction(0))
    trace_energy = sum((conductance(x, y) * (harmonic[x] - harmonic[y]) ** 2
                        for x in defects for y in chain.neighbors[x] if y in defects and x < y), Fraction(0))
    for incident, total in stars:
        if total:
            trace_energy += sum((Fraction(wx * wy, total) * (harmonic[x] - harmonic[y]) ** 2
                                 for x, wx in incident.items() for y, wy in incident.items() if x < y), Fraction(0))
    assert full_energy == trace_energy
    return {
        "row_domination_by_completion_weight_times_full_degree": True,
        "maximum_trace_row_rate": str(max(rates[x] / weights[x] for x in defects)),
        "minimum_row_domination_slack": str(min(weights[x] * len(chain.neighbors[x]) - rates[x] for x in defects)),
        "observable": "g(defect state index) = state index",
        "observable_nonconstant": True,
        "full_harmonic_extension_energy": str(full_energy),
        "eliminated_defect_trace_energy": str(trace_energy),
        "weighted_harmonic_energy_identity": True,
    }


def check_case(rows, columns, U, L):
    # One exact physical-chain construction supplies all checks for this case.
    chain = build_rescaled_ideal_chain(TableProblem(rows, columns), U=U, L=L)
    balanced = {i for i, state in enumerate(chain.states) if state.balanced}
    defects = set(range(len(chain.states))) - balanced
    weights, p = chain.completion_counts, len(chain.small_cells)
    assert defects and p >= 2 and all(weight > 0 for weight in weights)
    assert all(not (set(chain.neighbors[i]) & balanced) for i in balanced)
    assert all(value < U for i in balanced for value in chain.states[i].row_view)
    maximum_degree = max(len(chain.neighbors[x]) for x in defects)
    maximum_balanced_neighbors = max(len(set(chain.neighbors[x]) & balanced) for x in defects)
    assert maximum_degree <= 8 * p - 7
    assert maximum_balanced_neighbors <= 2
    assert all(chain.large_capacity >= sum(rr) for rr, _ in chain.residual_margins)
    lookup = {state: i for i, state in enumerate(chain.states)}
    partitions = [balanced_families(chain, i, lookup) for i in sorted(balanced)]
    for i, neighbors in enumerate(chain.neighbors):
        for j in neighbors:
            assert chain.acceptance_counts[i][j] == chain.acceptance_counts[j][i]
            assert 0 <= chain.acceptance_counts[i][j] <= weights[i]
    minimum_acceptance = min(Fraction(chain.acceptance_counts[i][j], weights[i])
                             for i, neighbors in enumerate(chain.neighbors) for j in neighbors)
    padding_at_least_3d = L >= 3 * chain.d
    if padding_at_least_3d:
        assert minimum_acceptance >= Fraction(1, 2)
    witness = next((x for x in sorted(defects) if len(set(chain.neighbors[x]) & balanced) > 1), None)
    return {
        "rows": rows, "columns": columns, "U": U, "L": L, "d": chain.d,
        "small_cells": chain.small_cells, "p": p, "physical_states": len(chain.states),
        "balanced_states": len(balanced), "defect_states": len(defects),
        "completion_weights": sorted(set(weights)), "no_balanced_balanced_edges": True,
        "balanced_entries_strictly_below_U": True,
        "max_defect_full_degree": maximum_degree, "defect_full_degree_bound_8p_minus_7": 8 * p - 7,
        "max_defect_defect_degree": max(len(set(chain.neighbors[x]) & defects) for x in defects),
        "max_balanced_neighbors_per_defect": maximum_balanced_neighbors,
        "five_families_disjoint_and_exhaustive": True, "closed_form_family_counts_match": True,
        "balanced_family_counts": partitions,
        "row_view_hits_U": any(U in state.row_view for state in chain.states),
        "column_view_hits_U": any(U in state.column_view for state in chain.states),
        "multiple_balanced_neighbor_witness": None if witness is None else {
            "defect_index": witness, "row_view": chain.states[witness].row_view,
            "column_view": chain.states[witness].column_view,
            "balanced_neighbor_indices": sorted(set(chain.neighbors[witness]) & balanced)},
        "minimum_directed_completion_acceptance": str(minimum_acceptance),
        "padding_at_least_3d": padding_at_least_3d,
        "half_acceptance_checked_under_3d_padding": padding_at_least_3d,
        "source_large_capacity_dominates_all_residual_totals": True,
        "minimum_weight_trace": trace_certificate(chain, defects, balanced, lambda i, j: min(weights[i], weights[j])),
        "actual_accepted_trace": trace_certificate(chain, defects, balanced, lambda i, j: chain.acceptance_counts[i][j]),
        "joint_terminal": joint_terminal_certificate(chain, defects, balanced, partitions, lookup),
        "physical_chain_work_counts": dict(chain.work_counts),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / ".local/reports/general-defect-trace.json")
    args = parser.parse_args()
    if not __debug__:
        parser.error("run without -O: exact certificate checks must remain enabled")
    source_paths = ("experiments/general_defect_trace.py", "src/contingency115/ideal_chain.py",
                    "src/contingency115/tables.py", "src/contingency115/kernels.py")
    fixtures = [check_case(*case) for case in CASES]
    nonideal_padding = next(fixture for fixture in fixtures
                           if fixture["rows"] == (2, 2, 1) and fixture["U"] == 2 and fixture["L"] == 78)
    success = Fraction(nonideal_padding["joint_terminal"]["corrected_success_probability"])
    comparison = Fraction(nonideal_padding["joint_terminal"]["comparison_1_over_8p"])
    assert nonideal_padding["padding_at_least_3d"] and success == Fraction(11, 3474) < comparison == Fraction(1, 40)
    result = {
        "schema_version": 2,
        "source_sha256": {path: sha256((ROOT / path).read_bytes()).hexdigest() for path in source_paths},
        "scope": "Eleven positive-margin finite exact fixtures plus one expected nonpositive-margin scope failure, using the existing bounded physical-chain oracle. Unrestricted ordinary equal-total margins only; no additional bounds, structural zeros or arbitrary product weights. No general proof, formal verification or sampler/runtime claim.",
        "normalization": "Unnormalized conductances; each full graph edge and each defect-trace pair counted once. Accepted conductance is the actual completion-translation acceptance count; minimum-weight conductance is a separate surrogate.",
        "evidence_limits": "L=1 fixtures check geometry and exact accepted counts but do not certify a general half-acceptance premise. The L=3d fixture also checks directed acceptance >=1/2. The harmonic identity is checked on one nonconstant observable per fixture and per conductance, not on all functions or dimensions.",
        "enumeration": "Each case built once. Five-family evidence uses quadratic pair enumeration, not a proposed linear-time neighbor sampler. Existing oracle caps retained; no new CI or unit-test dependency.",
        "joint_terminal_scope": "Enumerate completion-retaining repair preimages, reject repaired dense entries below L, then apply the exact rational correction c0/(N0+N1). Count equality is checked for each successful balanced/completion pair. Output tables are compared with an independent ordinary-margin DP unrank enumeration. These are finite joint-law checks, not a general terminal proof.",
        "success_bound_scope": "L>=3d alone does not establish the linear terminal success lower bound. The general derivation also uses ideal U=5d^3 and a separate padding-mass bound; those premises are not certified by these fixtures.",
        "oracle_budget": asdict(IdealChainBudget()),
        "family_order_N0_to_N4": FAMILIES,
        "fixtures": fixtures,
        "expected_scope_obstructions": {
            "zero_margins": zero_margin_scope_obstruction(),
            "large_padding_with_nonideal_U": {
                "rows": nonideal_padding["rows"], "columns": nonideal_padding["columns"],
                "U": nonideal_padding["U"], "L": nonideal_padding["L"], "p": nonideal_padding["p"],
                "L_equals_3d": True, "corrected_success_probability": str(success),
                "comparison_1_over_8p": str(comparison), "success_strictly_below_comparison": True,
                "equal_unconditional_corrected_table_masses": True,
                "conclusion": "Finite output uniformity survives; L=3d by itself is insufficient for the stated success lower bound.",
            },
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"All {len(CASES)} positive finite cases and both expected scope obstructions passed; result written to the requested output.")


if __name__ == "__main__":
    main()
