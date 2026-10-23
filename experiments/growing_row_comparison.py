"""One bounded growing-row literal count/bridge/energy fixture; no general theorem."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
from types import SimpleNamespace
import argparse, hashlib, json, subprocess, sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / 'src'), str(ROOT)]
from contingency115.general_neighbors import BalancedNeighborCatalog
from contingency115.ideal_chain import IdealPhysicalChain, PhysicalState
from contingency115.tables import TableProblem, _bounded_vectors
from experiments.thin_row_extension import variance


def compositions(total, parts):
    return tuple(_bounded_vectors(total, (0,) * parts, (total,) * parts))


def run():
    R, b, U, L = 3, 2, 3, 7
    H, C, delta = U - 1, b, F(41, 42)
    T = 42 * (R - 1) * b * (b * H + 1) + U
    S = T + b * L
    J = (R - 1) * S + 2
    Tlast = b * H + b * J - 1 - (R - 1) * T
    problem = TableProblem((1,) + (T,) * (R - 1) + (Tlast,), (H,) * b + (J,) * C)
    dshape = 10 + (R + 2) * (2 * b + 1)
    cap = sum(problem.row_sums) + dshape * L + U + 2
    cells = tuple((i, j) for i in range(R + 1) for j in range(2 * b) if i == 0 or j < b)
    p = len(cells)
    assert p == b * (R + 2)
    def vec(A): return tuple(A[v] for v in cells)
    def views(d): return dict(zip(cells, d.row_view)), dict(zip(cells, d.column_view))
    weights, residuals = {}, {}
    def weight(d):
        if d in weights: return weights[d]
        x, q = views(d)
        assert all(0 <= z <= U for z in d.row_view + d.column_view)
        assert sum(x[0, j] for j in range(2 * b)) == 1
        assert all(sum(q[i, j] for i in range(R + 1)) == H for j in range(b))
        used = tuple(sum(x.get((i, j), 0) for j in range(2 * b)) for i in range(R + 1))
        assert all(z <= r for z, r in zip(used, problem.row_sums))
        rr = tuple(problem.row_sums[i] - used[i] + C * L for i in range(1, R + 1))
        cc = tuple(J - q[0, j] + R * L for j in range(b, 2 * b))
        assert sum(rr) == sum(cc) and min(cc) >= sum(rr[:-1])
        assert all(S - b * H - 1 <= r <= S for r in rr[:-1])
        assert sum(rr) <= cap
        weights[d] = 1
        for r in rr[:-1]: weights[d] *= comb(r + C - 1, C - 1)
        residuals[d] = rr, cc
        return weights[d]
    def translation(d, e):
        context = SimpleNamespace(all_small=False, residual_margins=(residuals[d], residuals[e]))
        return IdealPhysicalChain.translation(context, 0, 1)
    def accepted(d, e):
        change = translation(d, e)
        rr, cc = residuals[d]
        assert max(abs(z) for row in change for z in row) <= 1
        assert all(c - sum(rr[:-1]) >= R * L for c in cc)
        result = 1
        for i, r in enumerate(rr[:-1]):
            k = sum(max(0, -z) for z in change[i])
            result *= comb(r - k + C - 1, C - 1)
        # The forced last row stays positive for every first-row composition.
        assert min(cc) - sum(rr[:-1]) + min(change[-1]) >= 0
        return result
    def adjacent(d, e):
        z = tuple(y - x for x, y in zip(d.row_view, e.row_view)) + tuple(x - y for x, y in zip(d.column_view, e.column_view))
        return sorted(t for t in z if t) == [-1, 1]
    profiles, place, lookup, balanced = {}, {}, {}, []
    for P in range(2 * b):
        column_choices = [compositions(H - int(j == P), R) for j in range(b)]
        for columns in product(*column_choices):
            A = {v: 0 for v in cells}; A[0, P] = 1
            for j, eta in enumerate(columns):
                for r, z in enumerate(eta, 1): A[r, j] = z
            a = PhysicalState(vec(A), vec(A)); weight(a)
            balanced.append(a); profiles[a] = A; place[a] = P; lookup[a.row_view] = a
    small_size = comb(H - 1 + R - 1, R - 1) * comb(H + R - 1, R - 1) ** (b - 1)
    large_size = comb(H + R - 1, R - 1) ** b
    assert len(balanced) == b * (small_size + large_size) == 108
    assert Counter(place.values()) == {j: small_size if j < b else large_size for j in range(2 * b)}
    coupling = defaultdict(F)
    for eta in compositions(H - 1, R):
        for r in range(R):
            target = list(eta); target[r] += 1
            coupling[tuple(target)] += F(eta[r] + 1, (H + R - 1) * comb(H - 1 + R - 1, R - 1))
    assert set(coupling) == set(compositions(H, R))
    assert set(coupling.values()) == {F(1, comb(H + R - 1, R - 1))}
    repair, db = {}, defaultdict(dict)
    for a in balanced:
        catalog = BalancedNeighborCatalog.from_problem(problem, a, U=U, L=L)
        for rank in range(catalog.degree):
            z = catalog.unrank(rank); weight(z)
            c = accepted(a, z)
            assert c == accepted(z, a) and c >= F(weights[a], 2) and c >= F(weights[z], 2)
            db[a][z] = c
            if rank < catalog.counts[0] + catalog.counts[1]:
                if z in repair: assert repair[z] == a
                repair[z] = a
    defects = sorted({z for neighbors in db.values() for z in neighbors})
    assert set(defects) == set(repair)
    assert all(sum(z in neighbors for neighbors in db.values()) <= 2 for z in defects)
    nu = {a: sum(weights[z] for z in defects if repair[z] == a) for a in balanced}
    W = comb(S + b - 1, b - 1) ** (R - 1)
    for a in balanced:
        assert delta * W <= weights[a] <= W
        assert F(R * b * b * weights[a], 2) <= nu[a] <= p * (p - 1) * weights[a]
    def inverse(a, s, t):
        A = profiles[a]; x, q = dict(A), dict(A); v = (t[0], s[1])
        x[t] += 1; q[s] += 1; x[v] -= 1; q[v] -= 1
        return PhysicalState(vec(x), vec(q))
    grid, dd, pair_charge, list_charge = [], {}, Counter(), Counter()
    jumps, jump_nodes, incoming = [], set(), Counter()
    Lrow = b * ((R + 1) * b - 2)
    for a in balanced:
        A = profiles[a]
        for j in range(b):
            for r in range(1, R + 1):
                if not A[r, j]: continue
                for rp in range(r + 1, R + 1):
                    B = dict(A); B[r, j] -= 1; B[rp, j] += 1; e = lookup[vec(B)]
                    we = min(weights[a], weights[e]); grid.append((a, e, we)); copy_count = 0
                    for i in range(R + 1):
                        s = (i, j)
                        src = [inverse(a, s, (r, k)) for k in range(b) if s != (r, k)]
                        tgt = [inverse(e, s, (rp, k)) for k in range(b) if s != (rp, k)]
                        for z in src: assert repair[z] == a and weights[z] == weights[a]; list_charge[z] += 1
                        for z in tgt: assert repair[z] == e and weights[z] == weights[e]; list_charge[z] += 1
                        for z in src:
                            for t in tgt:
                                assert adjacent(z, t)
                                c = accepted(z, t)
                                assert c == accepted(t, z) and c >= we / 2
                                key = tuple(sorted((z, t))); assert key not in dd; dd[key] = c
                                pair_charge[z] += 1; pair_charge[t] += 1; copy_count += 1
                    assert copy_count == Lrow
        P = place[a]
        if P >= b: continue
        for c in range(b, 2 * b):
            for r in range(1, R + 1):
                B = dict(A); B[0, P] -= 1; B[0, c] += 1; B[r, P] += 1; e = lookup[vec(B)]
                x, q = dict(A), dict(A); x[0, P] -= 1; x[0, c] += 1; q[0, P] -= 1; q[r, P] += 1
                z = PhysicalState(vec(x), vec(q)); we = min(weights[a], weights[e])
                assert z not in jump_nodes and repair[z] == a and z in db[a] and z in db[e]
                assert db[a][z] == weights[a] and db[e][z] >= we / 2 and adjacent(z, e)
                jump_nodes.add(z); jumps.append((a, e, we, z)); incoming[e] += 1
    assert len(dd) == Lrow * len(grid)
    assert max(list_charge.values()) <= R - 1 and max(pair_charge.values()) <= b * (R - 1)
    assert max(incoming.values()) <= R * b
    def direct_count(state, target=None):
        rr, cc = residuals[state]; total = passes = 0
        context = None
        if target is not None:
            context = SimpleNamespace(all_small=False, residual_margins=(residuals[state], residuals[target]))
            context.translation = lambda source, dest: IdealPhysicalChain.translation(context, source, dest)
        for first in range(rr[0] + 1):
            for second in range(rr[1] + 1):
                completion = ((first, rr[0] - first), (second, rr[1] - second),
                              (cc[0] - first - second, cc[1] - rr[0] - rr[1] + first + second))
                if min(z for row in completion for z in row) < 0: continue
                if max(z for row in completion for z in row) > cap: continue
                assert tuple(map(sum, completion)) == rr
                assert tuple(sum(row[j] for row in completion) for j in range(C)) == cc
                total += 1
                if target is not None: passes += IdealPhysicalChain.completion_passes(context, 0, 1, completion)
        assert total == weights[state]
        if target is not None: assert passes == accepted(state, target)
        return dict(rows=rr, columns=cc, direct_count=total, formula_count=weights[state], accepted_direct=passes if target else None,
                    accepted_formula=accepted(state, target) if target else None)
    first = balanced[0]
    A = profiles[first]; x, q = dict(A), dict(A); x[1, 0] += 1; q[0, b] += 1
    ll = PhysicalState(vec(x), vec(q)); assert repair[ll] == first
    edge = next(iter(dd)); z, t = edge
    direct = [direct_count(first), direct_count(ll), direct_count(z, t), direct_count(t, z)]
    records = []
    for mode in range(4):
        g = {z: (F((i % 7) - 3, 1 + i % 3) if mode == 0 else F(profiles[repair[z]][1, 0]) if mode == 1 else F(place[repair[z]] >= b) if mode == 2 else F(sum(z.row_view[cells.index((1, j))] for j in range(b)))) for i, z in enumerate(defects)}
        centers = {a: sum(weights[z] * g[z] for z in defects if repair[z] == a) / nu[a] for a in balanced}
        noise = sum(weights[z] * (g[z] - centers[repair[z]]) ** 2 for z in defects)
        harmonic = {a: sum(c * g[z] for z, c in db[a].items()) / sum(db[a].values()) for a in balanced}
        star = sum(c * (g[z] - harmonic[a]) ** 2 for a in balanced for z, c in db[a].items())
        dd_energy = sum(c * (g[z] - g[t]) ** 2 for (z, t), c in dd.items())
        eg = sum(we * (centers[a] - centers[e]) ** 2 for a, e, we in grid)
        ej = sum(we * (centers[a] - centers[e]) ** 2 for a, e, we, z in jumps)
        egu = sum((centers[a] - centers[e]) ** 2 for a, e, we in grid)
        eju = sum((centers[a] - centers[e]) ** 2 for a, e, we, z in jumps)
        vd = variance([weights[z] for z in defects], [g[z] for z in defects])
        vn = variance([nu[a] for a in balanced], [centers[a] for a in balanced])
        vu = variance([1] * len(balanced), [centers[a] for a in balanced])
        assert vd == noise + vn and noise <= 2 * star
        assert eg <= F(6, Lrow) * dd_energy + F(3 * b * (R - 1), Lrow) * noise
        assert ej <= (6 + F(12, b)) * star
        assert vu <= F(U * U, 4 * R) * egu + F(2, b) * eju
        assert vn <= F(p * p * U * U, 4 * R * delta) * eg + F(2 * p * p, b * delta) * ej
        assert vd <= 30 * p * U * U * (star + dd_energy)
        records.append(dict(observable=mode, variance_D=str(vd), repair_noise=str(noise), variance_nu=str(vn), star_energy=str(star), DD_bridge_energy=str(dd_energy), grid_center_energy=str(eg), jump_center_energy=str(ej)))
    paths = ['docs/growing-row-comparison.md', 'experiments/growing_row_comparison.py', 'experiments/thin_row_extension.py', 'src/contingency115/general_neighbors.py', 'src/contingency115/ideal_chain.py', 'src/contingency115/tables.py']
    return dict(checks='passed', schema_version=1,
                created_utc=datetime.now(timezone.utc).isoformat(),
                target_law='ordinary_uniform_completion_cardinalities',
                source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(), scope='ONE R3,b2,U3,L7 focused exact fixture, four rational observables, four direct dense-count contexts including one two-direction translated DD pair. No general theorem, Lean build, full DD matrix, all-state dense-fiber enumeration or runtime claim.',
                normalization='Raw ordinary completion weights; each actual bridge and star incidence charged once; no successful-move or clock rescaling',
                complexity_assessment=dict(balanced=108, crude_defect_presentations_upper=10800, dense_count_upper=W, reduced_parameters=False),
                rows=problem.row_sums, columns=problem.column_sums, R=R,b=b,U=U,L=L,p=p,canonical_capacity=cap,
                balanced=len(balanced), defects=len(defects), DB_incidences=sum(map(len,db.values())), grid_center_edges=len(grid), parallel_DD_edges=len(dd), copies_per_grid_edge=Lrow, max_endpoint_list_charge=max(list_charge.values()), max_endpoint_pair_charge=max(pair_charge.values()), jump_shared_defects=len(jumps), max_incoming_jump_degree=max(incoming.values()),
                polya_coupling={str(k):str(v) for k,v in sorted(coupling.items())}, direct_count_contexts=direct, exact_observables=records,
                source_sha256={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in paths})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / '.local/reports/growing-row-comparison.json')
    args = parser.parse_args()
    if not __debug__: parser.error('run without -O')
    result = run(); args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('Focused growing-row exact fixture passed.')
