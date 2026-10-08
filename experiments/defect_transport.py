#!/usr/bin/env python3
"""Exact synthetic checks of #115 repair geometry; no spectral-gap claim.

PYTHONPATH=src python3 experiments/defect_transport.py --output reports/defect-transport-research.json
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

from contingency115.tables import ExactTableSampler, TableProblem


UPSTREAM_COMMIT = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def compositions(total, length):
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, length - 1):
                yield (first,) + rest


def defect_labels(state):
    p = len(state) // 2
    differences = [state[p + k] - state[k] for k in range(p)]
    if all(value == 0 for value in differences):
        return None
    negative = [k for k, value in enumerate(differences) if value == 1]
    positive = [k for k, value in enumerate(differences) if value == -1]
    assert len(negative) == len(positive) == 1
    assert all(value in (-1, 0, 1) for value in differences)
    return negative[0], positive[0]


def direct_states(n, margin):
    """Independent enumeration of row views and all ordered defect labels."""
    p = n*n
    result = set()
    row_choices = tuple(compositions(margin, n))
    for rows in product(row_choices, repeat=n):
        x = tuple(value for row in rows for value in row)
        if all(sum(x[i*n + j] for i in range(n)) == margin for j in range(n)):
            result.add(x + x)
        for s in range(p):
            for t in range(p):
                if s == t or x[t] == 0:
                    continue
                q = list(x)
                q[s] += 1
                q[t] -= 1
                if all(sum(q[i*n + j] for i in range(n)) == margin for j in range(n)):
                    result.add(x + tuple(q))
    return result


def unit_edges(states, n):
    """All feasible unit exchanges: x within a row or q within a column.

    A mixed x/y move would change the fixed total of x, so cannot be feasible
    when the large block is empty. The remaining moves preserve the stated
    row/column margins only in the indicated common row/column.
    """
    lookup = {state: i for i, state in enumerate(states)}
    p = n*n
    edges = set()
    for i, state in enumerate(states):
        for view in (0, 1):
            for line in range(n):
                cells = [line*n + k if view == 0 else k*n + line for k in range(n)]
                for donor in cells:
                    if state[view*p + donor] == 0:
                        continue
                    for receiver in cells:
                        if donor == receiver:
                            continue
                        moved = list(state)
                        moved[view*p + donor] -= 1
                        moved[view*p + receiver] += 1
                        other = lookup.get(tuple(moved))
                        if other is not None:
                            edges.add(tuple(sorted((i, other))))
    return edges


def direct_doubled_unit_edges(states, capacity):
    """Independent edge check in the literal (x,y) coordinates."""
    p = len(states[0])//2
    doubled = [state[:p] + tuple(capacity-value for value in state[p:]) for state in states]
    lookup = {state: i for i, state in enumerate(doubled)}
    edges = set()
    for i, state in enumerate(doubled):
        for donor in range(2*p):
            if state[donor] == 0:
                continue
            for receiver in range(2*p):
                if donor == receiver or state[receiver] == capacity:
                    continue
                moved = list(state)
                moved[donor] -= 1
                moved[receiver] += 1
                other = lookup.get(tuple(moved))
                if other is not None:
                    edges.add(tuple(sorted((i, other))))
    return edges


def variance(values):
    total = sum(values, F(0))
    return sum((F(value)-total/len(values))**2 for value in values)


def energy(values, edges):
    return sum((values[i]-values[j])**2 for i, j in edges)


def case(n, margin):
    problem = TableProblem((margin,)*n, (margin,)*n)
    tables = tuple(ExactTableSampler(problem).tables(max_tables=10000))
    bases = [tuple(value for row in table for value in row) for table in tables]
    p = n*n
    # This small U has the same all-small state set/graph as any larger U,
    # including the published U=d^20. All row/column views are <=margin<U.
    capacity = margin + 1
    repairs = {}
    for base in bases:
        for s in range(p):
            for t in range(p):
                if s == t:
                    continue
                v = (t//n)*n + s % n
                if base[v] == 0:
                    continue
                x, q = list(base), list(base)
                x[t] += 1
                x[v] -= 1
                q[s] += 1
                q[v] -= 1
                state = tuple(x + q)
                assert defect_labels(state) == (s, t)
                assert state not in repairs
                assert min(state) >= 0 and max(state) < capacity
                repairs[state] = base + base
    states = sorted(set(repairs) | {base + base for base in bases})
    assert set(states) == direct_states(n, margin)
    lookup = {state: i for i, state in enumerate(states)}
    base_indices = {lookup[base + base] for base in bases}
    exchange = unit_edges(states, n)
    independently_checked_edges = p <= 4 or (n == 3 and margin == 1)
    if independently_checked_edges:
        assert exchange == direct_doubled_unit_edges(states, capacity)
    edges = exchange | {tuple(sorted((lookup[state], lookup[target])))
                        for state, target in repairs.items()}
    incoming = Counter(repairs.values())
    for base in bases:
        assert incoming[base + base] == (p-1)*sum(value > 0 for value in base)
    neighbors = defaultdict(set)
    for i, j in edges:
        neighbors[i].add(j)
        neighbors[j].add(i)
    for state, target in repairs.items():
        assert neighbors[lookup[state]] & base_indices == {lookup[target]}
    same_type_edges = sum(defect_labels(states[i]) is not None and
                          defect_labels(states[i]) == defect_labels(states[j])
                          for i, j in edges)
    assert same_type_edges == 0

    # A projected observable can vanish despite genuine within-type variance.
    groups = defaultdict(list)
    for i, state in enumerate(states):
        labels = defect_labels(state)
        if labels is not None:
            groups[labels].append(i)
    centered = [F(0)]*len(states)
    witness = None
    for labels, indices in sorted(groups.items()):
        mean = F(sum(states[i][0] for i in indices), len(indices))
        for i in indices:
            centered[i] = states[i][0]-mean
        assert sum(centered[i] for i in indices) == 0
        if witness is None and len({states[i][0] for i in indices}) > 1:
            low = min(indices, key=lambda i: states[i][0])
            high = max(indices, key=lambda i: states[i][0])
            witness = {"negative_positive_cells": list(labels),
                       "row_column_views_1": list(states[low]), "row_column_views_2": list(states[high])}
    assert sum(centered) == 0

    observables = {
        "first_row_view_cell": [F(state[0]) for state in states],
        "first_repaired_cell": [F(repairs.get(state, state)[0]) for state in states],
        "zero_projection_within_type": centered,
    }
    measurements = {}
    for name, values in observables.items():
        v, e = variance(values), energy(values, edges)
        defect_edges = {(i, j) for i, j in edges if i not in base_indices and j not in base_indices}
        measurements[name] = {
            "unnormalized_variance": str(v), "unnormalized_graph_energy": str(e),
            "defect_to_defect_energy": str(energy(values, defect_edges)),
            "transversal_to_defect_energy": str(e-energy(values, defect_edges)),
            "variance_over_energy": str(v/e) if e else None,
        }
    measurements["zero_projection_within_type"]["projected_variance"] = "0"
    return {
        "dimension": n, "common_margin": margin, "small_cells_p": p,
        "reference_capacity": capacity, "transversal_states": len(bases),
        "defect_states": len(repairs), "defect_to_transversal_mass_ratio": str(F(len(repairs), len(bases))),
        "minimum_incoming_repairs": min(incoming[base + base] for base in bases),
        "maximum_incoming_repairs": max(incoming[base + base] for base in bases),
        "maximum_generic_type_count": p*(p-1),
        "transversal_neighbors_per_defect": 1,
        "exchange_edges": len(exchange), "full_graph_edges": len(edges),
        "within_same_defect_type_edges": same_type_edges,
        "independent_state_enumeration_equal": True,
        "literal_doubled_edge_crosscheck": independently_checked_edges,
        "incoming_support_identity_checked": True,
        "observables": measurements, "within_type_variance_witness": witness,
    }


def report():
    cases = [case(n, margin) for n, margin in
             ((2, 1), (2, 2), (2, 4), (2, 8), (3, 1), (3, 2), (3, 3), (4, 1))]
    for item in cases:
        if item["dimension"] == 2:
            margin = item["common_margin"]
            assert item["transversal_states"] == margin+1
            assert item["defect_states"] == 12*margin
    return {
        "schema_version": 1,
        "upstream_commit": UPSTREAM_COMMIT,
        "status": "Exact small-instance evidence and method obstructions; no new gap bound or Lean theorem",
        "data": "Synthetic integer margins only; all weights are one because the large block is empty",
        "reproduce": "PYTHONPATH=src python3 experiments/defect_transport.py --output reports/defect-transport-research.json",
        "generic_repair_only_counterexample": {
            "construction": "Two unit-weight base vertices joined by an edge, with D unit-weight defect leaves at each; observable is +1/-1 on a base vertex and all its leaves",
            "base_variance": "2", "full_variance": "2(D+1)",
            "graph_energy": "4", "repair_energy": "0",
            "interpretation": "A D-independent repair-only extension is false; this graph omits the physical defect-to-defect exchange structure",
        },
        "fixed_defect_exposure_obstruction": {
            "capacity": 2,
            "display_pairs": [[0, 1], [1, 2], [1, 2], [1, 1]],
            "occupancies_before_removal": [1, 3, 3, 2],
            "occupancies_after_ordinary_slot_3_removal": [1, 3, 3, 1],
            "interpretation": "The ordinary-slot leaf removal produces two negative and two positive slots, outside the actual one-defect graph; this is a combinatorial template, not a physical-weight assertion",
        },
        "cases": cases,
        "limitations": [
            "No eigenvalues are estimated and no general spectral-gap conclusion is inferred from observable ratios",
            "Repair-load and neighbor obstructions do not disprove improvement through defect-to-defect edges",
            "The CommonBases defect-mean result controls a projected observable, leaving the within-type term unresolved for a full #115 gap",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rendered = json.dumps(report(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
