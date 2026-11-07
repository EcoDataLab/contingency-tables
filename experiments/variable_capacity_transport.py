"""Exact finite bridge checks; not a proof by enumeration."""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from contingency115.ideal_chain import build_rescaled_ideal_chain
from contingency115.tables import TableProblem


def run(rows, cols):
    m, n = len(rows), len(cols)
    p = m*n
    U = max(rows + cols) + 1
    caps = tuple(min(rows[i], cols[j]) + 1 for i in range(m) for j in range(n))
    chain = build_rescaled_ideal_chain(TableProblem(rows, cols), U=U, L=1)
    lookup = {state: i for i, state in enumerate(chain.states)}
    raw = [state.row_view + tuple(B-q for B, q in zip(caps, state.column_view))
           for state in chain.states]
    rlookup = {z: i for i, z in enumerate(raw)}
    assert all(0 <= z[k] <= caps[k % p] for z in raw for k in range(2*p))
    for i, z in enumerate(raw):
        found = set()
        for donor in range(2*p):
            for receiver in range(2*p):
                if donor == receiver or z[donor] == 0 or z[receiver] == caps[receiver % p]:
                    continue
                moved = list(z)
                moved[donor] -= 1
                moved[receiver] += 1
                target = rlookup.get(tuple(moved))
                if target is not None:
                    found.add(target)
        expected = {j for j in chain.neighbors[i]
                    if sum(abs(a-b) for a, b in zip(raw[i], raw[j])) == 2}
        assert found == expected
    bases = [s.row_view for s in chain.states if s.balanced]
    weighted_contexts, profiles, leaf_edges = 0, 0, 0
    owners = {}
    for current in range(p):
        prefixes = {A[:current] for A in bases}
        for prefix in prefixes:
            for level in range(1, caps[current]+1):
                left = sum(A[:current] == prefix and A[current] == level-1 for A in bases)
                right = sum(A[:current] == prefix and A[current] == level for A in bases)
                weighted = F(0)
                for later in range(current+1, p):
                    matches = [s for s in chain.states if s.defect_labels() == (current, later)
                               and s.row_view[:current] == prefix and s.row_view[current] == level-1]
                    repaired = set()
                    for s in matches:
                        A = list(s.row_view)
                        A[later] -= 1
                        A[(later//n)*n + current%n] += 1
                        A = tuple(A)
                        assert A in bases and A[:current] == prefix
                        assert A[current] == level-1 + (later//n == current//n)
                        assert all(v < B for v, B in zip(A, caps))
                        repaired.add(A)
                    assert len(repaired) == len(matches) <= max(left, right)
                    weighted += F((caps[later]+1)**2, 4)*len(matches)
                    profiles += len(matches)
                assert weighted <= F(sum((B+1)**2 for B in caps[current+1:]), 4)*max(left, right)
                weighted_contexts += 1
                # Literal leaf displays, with variable ordinary pair balances.
                for choices in product(*(range(B+1) for B in caps[current+1:])):
                    x = prefix + (level,) + choices
                    y = tuple(B-v for B, v in zip(caps, x))
                    y = y[:current] + (y[current]+1,) + y[current+1:]
                    display = x+y
                    endpoints = []
                    for hole in list(range(current, p))+list(range(p+current, 2*p)):
                        if display[hole] == 0:
                            continue
                        vertex = list(display)
                        vertex[hole] -= 1
                        index = rlookup.get(tuple(vertex))
                        if index is not None:
                            endpoints.append(index)
                    for i, j in combinations(endpoints, 2):
                        assert j in chain.neighbors[i]
                        recovered = tuple(max(a,b) for a,b in zip(raw[i], raw[j]))
                        assert recovered == display
                        assert [k for k in range(p) if recovered[k]+recovered[p+k] != caps[k]] == [current]
                        owner = current, level, prefix
                        edge = min(i,j), max(i,j)
                        assert edge not in owners or owners[edge] == owner
                        owners[edge] = owner
                        leaf_edges += 1
    return {'rows':rows, 'columns':cols, 'capacities':caps, 'states':len(raw),
            'weighted_contexts':weighted_contexts, 'positive_auxiliary_profiles':profiles,
            'literal_leaf_edge_occurrences':leaf_edges, 'owned_physical_edges':len(owners),
            'graph_translation_auxiliary_repair_and_variable_owner_checks':'passed'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    cases = [((3,2),(2,2,1)), ((2,2,1),(3,2)),
             ((3,3),(3,2,1)), ((3,2,1),(3,3))]
    data = {'evidence':'exact finite bridge checks; no general theorem by exhaustion',
            'cases':[run(r,c) for r,c in cases]}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(data, indent=2)+'\n')
    print(json.dumps(data,indent=2))
