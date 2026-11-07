"""One exact higher-token slice/place check; no dense, defect or physical-gap audit."""
from collections import defaultdict
from fractions import Fraction as F
from math import comb
from pathlib import Path
import argparse, hashlib, json, sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from contingency115.tables import _bounded_vectors


def compositions(total, parts):
    return tuple(_bounded_vectors(total, (0,) * parts, (total,) * parts))


def transfer(v, i, j):
    out = list(v); out[i] -= 1; out[j] += 1
    assert min(out) >= 0
    return tuple(out)


def run():
    R, b, U, h = 3, 2, 8, 2
    H = U - 1
    assert 1 <= h <= F(U, 2 * (R - 1)) and h <= H
    places = compositions(h, 2 * b)
    M = lambda t: comb(t + R - 1, R - 1)
    B0 = M(H) ** b
    slices = []
    for v in places:
        size = 1; product_ratio = F(1)
        for j in range(b):
            size *= M(H - v[j])
            for q in range(1, R): product_ratio *= 1 - F(v[j], H + q)
        ratio = F(size, B0)
        density_lower = 1 - F((R - 1) * sum(v[:b]), U)
        assert ratio == product_ratio and ratio >= density_lower >= F(1, 2)
        slices.append(dict(place=v, B=size, B_over_B0=str(ratio), product_ratio=str(product_ratio), density_lower=str(density_lower)))
    polya_contexts = {}
    relevant_edges = []
    for v in places:
        for j in range(b):
            if not v[j]: continue
            for c in range(b, 2 * b):
                target_place = transfer(v, j, c)
                assert target_place in places
                t = H - v[j]
                if t not in polya_contexts:
                    source = compositions(t, R); targets = compositions(t + 1, R)
                    source_marginal, target_marginal = defaultdict(F), defaultdict(F)
                    joint = []
                    for eta in source:
                        conditional_total = F(0)
                        for r in range(R):
                            z = list(eta); z[r] += 1; z = tuple(z)
                            conditional = F(eta[r] + 1, t + R)
                            conditional_total += conditional
                            mass = conditional / len(source)
                            source_marginal[eta] += mass; target_marginal[z] += mass
                            joint.append(dict(source=eta, target=z, row=r, conditional=str(conditional), joint_mass=str(mass)))
                        assert conditional_total == 1
                    assert set(source_marginal) == set(source) and set(target_marginal) == set(targets)
                    assert set(source_marginal.values()) == {F(1, len(source))}
                    assert set(target_marginal.values()) == {F(1, len(targets))}
                    assert sum(source_marginal.values()) == sum(target_marginal.values()) == 1
                    polya_contexts[t] = dict(source_total=t, target_total=t + 1, source_compositions=len(source), target_compositions=len(targets), source_probability=str(F(1, len(source))), target_probability=str(F(1, len(targets))), joint=joint)
                # Other small-column totals are unchanged, so uniform product
                # marginals reduce exactly to this changed-coordinate coupling.
                assert all(H - v[k] == H - target_place[k] for k in range(b) if k != j)
                relevant_edges.append(dict(source_place=v, target_place=target_place, small_donor=j, large_receiver=c, polya_source_total=t))
    complete_edges, bip_edges = set(), set()
    loads = defaultdict(F); routes = []
    for v in places:
        for i in range(2 * b):
            if not v[i]: continue
            for j in range(2 * b):
                if i == j: continue
                w = transfer(v, i, j)
                complete_edges.add((v, w))
                if (i < b) != (j < b):
                    bip_edges.add((v, w)); continue
                opposite = range(b, 2 * b) if i < b else range(b)
                pair_routes = 0
                common_min = tuple(min(x, y) for x, y in zip(v, w))
                for k in opposite:
                    mid = transfer(v, i, k)
                    for edge in [(v, mid), (mid, w)]:
                        assert tuple(min(x, y) for x, y in zip(*edge)) == common_min
                        loads[edge] += F(2, b)  # path length2 times flow1/b
                    routes.append(dict(source=v, target=w, donor=i, receiver=j, intermediate_place=k, midpoint=mid, donor_occupancy=v[i], route_weight=str(F(1, b)), per_step_energy_charge=str(F(2, b))))
                    pair_routes += 1
                # Configuration edges have unit weight even if donor occupancy2.
                assert pair_routes == b
    assert set(loads) <= bip_edges
    expected_within_bound = F(4 * (b - 1), b)
    assert max(loads.values()) <= expected_within_bound
    assert all(loads[v, w] == loads[w, v] for v, w in bip_edges)
    assert all((w, v) in complete_edges for v, w in complete_edges)
    assert len(complete_edges) == len(set(tuple(sorted(edge)) for edge in complete_edges)) * 2
    source_paths = ['docs/growing-row-extension.md', 'experiments/growing_row_extension.py', 'src/contingency115/tables.py']
    return dict(schema_version=1, checks='passed',
                scope='ONE R3,b2,U8,h2 slice/place fixture. Exact place compositions, binomial slice cardinalities, changed-column Polya source/target marginals for every relevant edge, and unit-configuration routing charges only. No dense completions, defects, full physical graph, all-observable physical gap, Lean build, runtime claim or parameter sweep.',
                normalization='Uniform place and conditional column composition laws; unit configuration-edge weights, route weights1/b and two-step square charge2/b. No particle multiplicity or inclusion-rate energy is assigned to the unit graph.',
                parameters=dict(R=R,b=b,U=U,h=h,H=H), place_compositions=len(places), B0=B0, minimum_B_over_B0=str(min(F(s['B'],B0) for s in slices)), slices=slices,
                relevant_small_to_large_place_edges=len(relevant_edges), relevant_edges=relevant_edges,
                polya_contexts=[polya_contexts[t] for t in sorted(polya_contexts)],
                routing=dict(directed_complete_edges=len(complete_edges), unordered_complete_edges=len(complete_edges)//2, directed_bipartite_edges=len(bip_edges), unordered_bipartite_edges=len(bip_edges)//2, same_part_directed_edges=len(complete_edges-bip_edges), averaged_paths=len(routes), max_within_part_charge=str(max(loads.values())), within_part_bound=str(expected_within_bound), complete_to_bipartite_factor=str(1+max(loads.values())), claimed_factor=str(1+expected_within_bound), directed_edge_charges=[dict(source=v,target=w,within_charge=str(loads[v,w]),total_charge=str(1+loads[v,w])) for v,w in sorted(bip_edges)], routes=routes),
                source_sha256={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in source_paths})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT / '.local/reports/growing-row-extension.json')
    args = parser.parse_args()
    if not __debug__: parser.error('run without -O')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(run(),indent=2,sort_keys=True)+'\n')
    print('Focused higher-token slice/place fixture passed.')
