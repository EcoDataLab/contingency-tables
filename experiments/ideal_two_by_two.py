"""Exact certificates for the all-small 2x2 ideal chain; no trajectory timing.

The base graph is enumerated independently from row/column views, not through
ideal_chain's profile generator. The general block argument is in the guide;
finite checks below are not a Lean proof of that argument.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
from itertools import product
import json
from pathlib import Path

from contingency115.chain_diagnostics import stationary_variance
from contingency115.ideal_chain import build_ideal_chain
from contingency115.tables import TableProblem

ROOT = Path(__file__).resolve().parents[1]
BETA = F(1, 16384)  # Literal d=19 dyadic proposal.


def base_graph():
    """Every pair of binary row-valid X and column-valid Q, independently."""
    states = []
    for a, b, c, d in product(range(2), repeat=4):
        x, q = (a, 1-a, b, 1-b), (c, d, 1-c, 1-d)
        delta = tuple(v-u for u, v in zip(x, q))
        if x == q or (delta.count(1) == delta.count(-1) == 1 and
                      all(abs(v) <= 1 for v in delta)):
            states.append((x, q))
    states = tuple(sorted(states))
    index = {s: i for i, s in enumerate(states)}
    edges = set()
    for i, (x, q) in enumerate(states):
        for j, (y, p) in enumerate(states):
            # Differences of actual doubled coordinates (X,U-Q); U cancels.
            delta = tuple(v-u for u, v in zip(x, y)) + tuple(u-v for u, v in zip(q, p))
            if delta.count(1) == delta.count(-1) == 1 and all(abs(v) <= 1 for v in delta):
                edges.add(tuple(sorted((i, j))))
        if x != q:
            delta = tuple(v-u for u, v in zip(x, q))
            s, t = delta.index(1), delta.index(-1)
            repaired = list(x)
            repaired[t] -= 1
            repaired[2 * (t//2) + s%2] += 1
            target = (tuple(repaired), tuple(repaired))
            edges.add(tuple(sorted((i, index[target]))))
    return states, tuple(sorted(edges))


def base_certificate():
    states, edges = base_graph()
    left = states.index(((0, 1, 1, 0), (0, 1, 1, 0)))
    right = states.index(((1, 0, 0, 1), (1, 0, 0, 1)))
    # Independently check a rational Dirichlet witness; no numerical solver.
    h = tuple(map(F, ('3/5', '1/3', '2/3', '2/5', '1/3', '0', '1/3',
                     '2/3', '1', '2/3', '2/5', '1/3', '2/3', '3/5')))
    adjacent = [set() for _ in states]
    for i, j in edges:
        adjacent[i].add(j)
        adjacent[j].add(i)
    interior = [i for i in range(len(states)) if i not in (left, right)]
    assert len(states) == 14 and len(edges) == 28
    assert h[left] == 0 and h[right] == 1
    for i in interior:
        assert len(adjacent[i]) * h[i] == sum(h[j] for j in adjacent[i])
        assert len(adjacent[i] & {left, right}) == 1
    conductance = sum((h[i]-h[j])**2 for i, j in edges)
    assert conductance == F(32, 15)
    assert sum(h[i] for i in interior) == 6
    assert sum(h[i]**2 for i in interior) == F(734, 225)
    assert len(adjacent[left]) == len(adjacent[right]) == 6
    return states, edges, h, left, right


def block_family(m):
    """Construct the proposed general graph by gluing independent base cells."""
    if type(m) is not int or m < 1:
        raise ValueError('m must be a positive integer')
    base, edges, h, _, _ = base_certificate()
    all_states, all_edges, potential = set(), set(), {}
    for k in range(m):
        background = (k, m-k-1, m-k-1, k)
        translated = tuple((tuple(x+b for x, b in zip(s[0], background)),
                            tuple(q+b for q, b in zip(s[1], background))) for s in base)
        all_states.update(translated)
        for i, state in enumerate(translated):
            value = k+h[i]
            assert state not in potential or potential[state] == value
            potential[state] = value
        all_edges.update(tuple(sorted((translated[i], translated[j]))) for i, j in edges)
    return tuple(sorted(all_states)), tuple(sorted(all_edges)), potential


def formulas(m, beta=BETA):
    q = F(32, 15)*beta
    variance = F(m*(m+2), 12)
    inflation = F((m+1)**2+1, 5)/q-1
    rayleigh = F(5, 128)/beta*(13*m*m+3*m-F(514, 75))
    return {
        'physical_states': 13*m+1, 'undirected_edges': 28*m,
        'balanced_tables': m+1, 'stationary_success_probability': F(m+1, 13*m+1),
        'mean_physical_steps_per_return': F(13*m+1, m+1),
        'return_neighbor_probability': q, 'coordinate_variance': variance,
        'coordinate_asymptotic_variance': variance*inflation,
        'coordinate_variance_inflation': inflation,
        'full_physical_inverse_gap_lower_bound': rayleigh,
    }


def run():
    base, edges, h, left, right = base_certificate()
    cases = []
    for m in range(1, 7):
        chain = build_ideal_chain(TableProblem([m, m], [m, m]))
        states, glued_edges, potential = block_family(m)
        actual_states = tuple((s.row_view, s.column_view) for s in chain.states)
        actual_edges = tuple(sorted({tuple(sorted((actual_states[i], actual_states[j])))
                                    for i, row in enumerate(chain.neighbors) for j in row}))
        assert chain.beta == BETA and states == actual_states and glued_edges == actual_edges
        f = formulas(m)
        censored = chain.all_small_return_kernel()
        q = f['return_neighbor_probability']
        path = tuple(tuple(q if abs(i-j) == 1 else
                           1-q*((i > 0)+(i < m)) if i == j else F(0)
                           for j in range(m+1)) for i in range(m+1))
        assert censored.kernel.matrix == path
        assert censored.stationary_success_probability == f['stationary_success_probability']
        assert censored.expected_physical_steps_per_return == f['mean_physical_steps_per_return']
        assert censored.per_start_expected_physical_steps == tuple(F(7 if k in (0, m) else 13)
                                                                  for k in range(m+1))
        diagnostic = stationary_variance(censored.kernel, [t[0][0] for t in censored.kernel.states])
        assert diagnostic.variance == f['coordinate_variance']
        assert diagnostic.asymptotic_variance == f['coordinate_asymptotic_variance']
        values = [potential[state] for state in states]
        mean = sum(values)/len(values)
        unnormalized_variance = sum((v-mean)**2 for v in values)
        unnormalized_energy = BETA*sum((potential[a]-potential[b])**2 for a, b in glued_edges)
        assert mean == F(m, 2)
        assert unnormalized_variance/unnormalized_energy == f['full_physical_inverse_gap_lower_bound']
        cases.append({'equal_margin': m, **f, 'complete_state_and_edge_match': True,
                      'exact_censor_poisson_and_rayleigh_checks': True})
    sources = ['experiments/ideal_two_by_two.py', 'src/contingency115/ideal_chain.py',
               'src/contingency115/chain_diagnostics.py', 'src/contingency115/kernels.py',
               'src/contingency115/tables.py']
    return {
        'status': 'exact_finite_certificates_and_reviewed_mathematical_derivation',
        'upstream_revision': 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
        'source_parameters': {'dimension_allowance': 19, 'U': 19**20, 'L': 19**12, 'beta': BETA},
        'scope': 'ordinary all-small 2x2 equal margins 1 <= m < U; no cap or weighted law',
        'base_certificate': {'states': base, 'edges': edges, 'harmonic_potential': h,
                             'left_boundary': left, 'right_boundary': right,
                             'unit_conductance': F(32, 15),
                             'internal_potential_sum': F(6),
                             'internal_squared_potential_sum': F(734, 225)},
        'finite_validations': cases,
        'limitations': ['The general block-decomposition argument is a mathematical derivation, not a Lean theorem.',
                       'Only margins one through six are exhaustively compared with the separate backend.',
                       'Asymptotic variance assumes stationarity; finite trajectories are not independent uniform samples.',
                       'Censored draws bypass physical excursions; no wall-clock performance is inferred.',
                       'The Omega(U^2) obstruction is for this free-cutoff all-small chain family, not every sampler.'],
        'source_sha256': {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
    }


def jsonable(value):
    if isinstance(value, F): return str(value)
    if isinstance(value, dict): return {key: jsonable(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)): return [jsonable(item) for item in value]
    return value


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    rendered = json.dumps(jsonable(run()), indent=2)+'\n'
    if args.output: args.output.write_text(rendered)
    else: print(rendered, end='')
