"""Exact finite checks of the accelerated all-small defect-trace chain.

Enumeration is exponential. The general d^16 result is a mathematical
derivation, not a Lean theorem or a complete machine-time bound.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from contingency115.ideal_chain import PhysicalState, build_rescaled_ideal_chain
from contingency115.tables import TableProblem


def repair(state, columns):
    result = list(state.row_view)
    if not state.balanced:
        s, t = state.defect_labels()
        result[t] -= 1
        result[(t // columns) * columns + s % columns] += 1
    return tuple(result)


def case(rows, columns, U=None, *, spectral=False):
    U = max(rows + columns) + 1 if U is None else U
    chain = build_rescaled_ideal_chain(TableProblem(rows, columns),
                                     U=U, L=1)
    assert chain.all_small
    m, n = len(rows), len(columns)
    p = m * n
    degrees = tuple(map(len, chain.neighbors))
    delta = max(degrees)
    for i, state in enumerate(chain.states):
        if state.balanced:
            assert degrees[i] == (p - 1) * sum(v > 0 for v in state.row_view)
        else:
            assert degrees[i] <= 2 * (m + n - 2) + 1
            base_neighbors = [j for j in chain.neighbors[i] if chain.states[j].balanced]
            assert len(base_neighbors) == 1
            assert chain.states[base_neighbors[0]].row_view == repair(state, n)
    assert delta <= p * (p - 1)
    beta_global = F(1, 2 * p * (p - 1))
    # Two faster kernels share the original uniform physical stationary law.
    # The local-degree MH kernel gives more weight to low-degree defect edges.
    for local in (False, True):
        for i, neighbors in enumerate(chain.neighbors):
            rates = [F(1, 2 * max(degrees[i], degrees[j])) if local
                     else beta_global for j in neighbors]
            assert sum(rates) <= F(1, 2)
            for j, rate in zip(neighbors, rates):
                assert rate >= beta_global >= chain.beta
                if local:
                    assert rate == F(1, 2 * max(degrees[j], degrees[i]))
    result = {'rows': rows, 'columns': columns, 'U': U, 'states': len(chain.states),
              'max_degree': delta, 'all_small_degree_bound': p * (p - 1),
              'source_beta': str(chain.beta), 'global_beta': str(beta_global),
              'guaranteed_gap_gain': str(beta_global / chain.beta),
              'degree_identity_and_exact_stochasticity': 'passed'}
    # Exact balanced-star elimination. The remaining defects have uniform law.
    defects = [i for i, state in enumerate(chain.states) if not state.balanced]
    lookup = {state: i for i, state in enumerate(chain.states)}
    groups = defaultdict(list)
    for i in defects:
        groups[repair(chain.states[i], n)].append(i)
    dindex = {i: j for j, i in enumerate(defects)}
    h = {i: F((i * i + 3 * i) % 17 - 8) for i in defects}
    hfull = dict(h)
    for i, state in enumerate(chain.states):
        if state.balanced:
            group = groups[state.row_view]
            assert len(group) == (p - 1) * sum(v > 0 for v in state.row_view)
            hfull[i] = sum((h[j] for j in group), F(0)) / len(group)
    def variance(values):
        mean = sum(values, F(0)) / len(values)
        return sum((value - mean) ** 2 for value in values)
    e_full = sum((hfull[i] - hfull[j]) ** 2
                 for i, nbrs in enumerate(chain.neighbors) for j in nbrs if i < j)
    e_trace = sum((h[i] - h[j]) ** 2 for i in defects
                  for j in chain.neighbors[i] if j in dindex and i < j)
    e_trace += sum(sum((h[i] - h[j]) ** 2 for i in group for j in group)
                   / (2 * len(group)) for group in groups.values())
    assert e_trace == e_full
    assert variance(list(h.values())) <= variance(list(hfull.values()))
    beta_trace = F(1, 4 * (m + n - 2) + 2)
    trace = [[F(0)] * len(defects) for _ in defects]
    max_dd = 0
    for i in defects:
        ii = dindex[i]
        dd = [j for j in chain.neighbors[i] if j in dindex]
        max_dd = max(max_dd, len(dd))
        assert len(dd) <= 2 * (m + n - 2)
        # Independently recover every DD neighbor from the four move channels.
        state = chain.states[i]
        s, t = state.defect_labels()
        channels = [(0, t, (t // n) * n + j) for j in range(n) if j != t % n]
        channels += [(0, (s // n) * n + j, s) for j in range(n) if j != s % n]
        channels += [(1, s, row * n + s % n) for row in range(m) if row != s // n]
        channels += [(1, row * n + t % n, t) for row in range(m) if row != t // n]
        assert len(channels) == 2 * (m + n - 2)
        targets = []
        for view, donor, receiver in channels:
            x, q = list(state.row_view), list(state.column_view)
            moved = x if view == 0 else q
            moved[donor] -= 1
            moved[receiver] += 1
            target = lookup.get(PhysicalState(tuple(x), tuple(q)))
            if target in dindex:
                targets.append(target)
        assert len(targets) == len(set(targets))
        assert set(targets) == set(dd)
        group = groups[repair(chain.states[i], n)]
        for j in dd:
            trace[ii][dindex[j]] += beta_trace
        for j in group:
            trace[ii][dindex[j]] += beta_trace / len(group)
        trace[ii][ii] += 1 - beta_trace * (len(dd) + 1)
        assert sum(trace[ii]) == 1 and min(trace[ii]) >= 0 and trace[ii][ii] >= F(1, 2)
    assert all(trace[i][j] == trace[j][i]
               for i in range(len(defects)) for j in range(len(defects)))
    # Check the full quadratic-form matrix, not just the displayed witness.
    # L_DD - L_DB L_BB^-1 L_BD; L_BB is diagonal since bases have no edges.
    bases = [i for i, state in enumerate(chain.states) if state.balanced]
    for b in bases:
        assert all(j in dindex for j in chain.neighbors[b])
    for ii, i in enumerate(defects):
        for jj, j in enumerate(defects):
            schur = F(degrees[i]) if i == j else F(-int(j in chain.neighbors[i]))
            schur -= sum(F(1, degrees[b]) for b in bases
                         if i in chain.neighbors[b] and j in chain.neighbors[b])
            assert schur == (F(ii == jj) - trace[ii][jj]) / beta_trace
    output_mass = {}
    support_lower = max(m, n)
    for table, group in groups.items():
        accept = F((p - 1) * support_lower, len(group))
        assert 0 < accept <= 1
        output_mass[table] = len(group) * accept
    assert len(set(output_mass.values())) == 1
    result['defect_trace'] = {'states': len(defects), 'max_DD_degree': max_dd,
        'beta': str(beta_trace), 'uniform_reversibility': 'exact check passed',
        'four_DD_channel_families': 'exact neighbor equality; no duplicate DD targets',
        'entire_Schur_matrix': 'exact equality passed for every entry',
        'harmonic_energy_identity': str(e_trace),
        'variance_restriction_and_repair_output': 'exact checks passed'}
    if spectral:
        import numpy as np
        # Original graph Laplacian without beta. Avoid subtracting tiny gaps.
        def gap(local):
            lap = np.zeros((len(degrees), len(degrees)))
            for i, neighbors in enumerate(chain.neighbors):
                for j in neighbors:
                    rate = F(1, 2 * max(degrees[i], degrees[j])) if local else beta_global
                    lap[i, j] = -float(rate)
                lap[i, i] = -sum(lap[i])
            return float(np.linalg.eigvalsh(lap)[1])
        result['floating_diagnostic'] = {'global_gap': gap(False),
                                         'degree_MH_gap': gap(True),
                                         'scope': 'floating-point finite diagnostics; not spectral certificates'}
        trace_lap = np.array([[float((i == j) - trace[i][j])
                              for j in range(len(defects))]
                             for i in range(len(defects))])
        result['floating_diagnostic']['defect_trace_gap'] = float(np.linalg.eigvalsh(trace_lap)[1])
    result['scope'] = ('primary: positive margins on both sides strictly below U'
                       if max(rows + columns) < U else
                       'exploratory: only one side below U; outside the primary claim')
    return result


def report(*, spectral=False):
    cases = [((t, t), (t, t), None) for t in range(1, 7)]
    cases += [((2, 2), (2, 1, 1), None), ((1, 1, 1), (1, 1, 1), None)]
    cases += [((1, 1, 1), (2, 1), 2), ((2, 1), (1, 1, 1), 2),
              ((2, 2, 2), (3, 3), 3), ((3, 3), (2, 2, 2), 3)]
    sources = ['experiments/defect_trace.py', 'src/contingency115/ideal_chain.py',
               'src/contingency115/tables.py']
    return {
        'evidence_class': 'exact finite checks of a mathematical derivation; not Lean',
        'upstream_revision': 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
        'scope': 'primary: m,n>=2, ordinary positive equal-total margins, every margin below U',
        'claimed_research_allowances': {
            'rational_defect_trace': '2500*d^16',
            'dyadic_defect_trace': '5000*d^16',
            'dimension': 'd=10+(m+1)*(n+1)',
            'ideal_cutoff': 'U=5*d^3',
            'status': 'mathematical derivation; not integrated with the compiled sampler',
        },
        'primary_fixture_count': 8,
        'exploratory_one_side_small_fixture_count': 4,
        'cases': [case(r, c, U, spectral=spectral) for r, c, U in cases],
        'limits': [
            'The accelerated trace changes the chain and its stationary repair law.',
            'Four one-side-small fixtures are diagnostics outside the primary reviewed scope.',
            'All graph identities are exact on these finite fixtures; enumeration is exponential.',
            'Optional NumPy eigenvalues are floating diagnostics, not universal gap certificates.',
            'No improved general reference/selected-chain theorem or complete runtime exponent is established.',
            'Conditional support and label draws still require bounded finite-word error composition.',
        ],
        'source_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sources},
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('.local/reports/defect-trace.json'))
    parser.add_argument('--spectral', action='store_true',
                        help='also compute optional NumPy eigenvalue diagnostics')
    args = parser.parse_args()
    rendered = json.dumps(report(spectral=args.spectral), indent=2) + '\n'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered)
    print(f'Wrote {args.output}: 12 exact fixture checks passed.')
