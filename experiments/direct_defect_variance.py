"""Exact incidence decomposition; bounded fixtures and an abstract obstruction."""
from fractions import Fraction as F
from pathlib import Path
import argparse,json,sys
from math import comb

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from contingency115.ideal_chain import build_rescaled_ideal_chain
from contingency115.tables import TableProblem

def variance(weights,values):
    mass=sum(weights)
    assert mass>0
    mean=sum(w*v for w,v in zip(weights,values))/mass
    return sum(w*(v-mean)**2 for w,v in zip(weights,values))

def physical_case(rows,cols,U,L):
    chain=build_rescaled_ideal_chain(TableProblem(rows,cols),U=U,L=L)
    B=[i for i,s in enumerate(chain.states) if s.balanced]
    D=[i for i,s in enumerate(chain.states) if not s.balanced]
    w=chain.completion_counts
    a={x:sum(chain.acceptance_counts[x][b] for b in B) for x in D}
    S={b:sum(chain.acceptance_counts[b][x] for x in D) for b in B}
    for x in D:
        assert a[x]>0 and w[x]<=2*a[x]<=4*w[x]
        assert sum(b in chain.neighbors[x] for b in B)<=2
    records=[]
    for observable in range(3):
        if observable==0:g={x:F((x%7)-3,1+x%3) for x in D}
        elif observable==1:g={x:F(chain.states[x].row_view[0]) for x in D}
        else:g={x:F(sum(chain.states[x].defect_labels())) for x in D}
        H={b:(sum(chain.acceptance_counts[b][x]*g[x] for x in D)/S[b]
              if S[b] else F(0)) for b in B}
        star=sum(chain.acceptance_counts[b][x]*(g[x]-H[b])**2 for b in B for x in D)
        dd=sum(chain.acceptance_counts[x][y]*(g[x]-g[y])**2
               for pos,x in enumerate(D) for y in D[pos+1:])
        Va=variance([a[x] for x in D],[g[x] for x in D])
        VS=variance([S[b] for b in B],[H[b] for b in B])
        Vw=variance([w[x] for x in D],[g[x] for x in D])
        assert Va==star+VS and Vw<=2*Va
        # Independently check the unordered Schur-complement star expression.
        star_pairs=sum(F(chain.acceptance_counts[b][x]*chain.acceptance_counts[b][y],S[b])
                       *(g[x]-g[y])**2
                       for b in B if S[b] for pos,x in enumerate(D) for y in D[pos+1:])
        assert star_pairs==star
        records.append(dict(observable=observable,variance_w=str(Vw),variance_a=str(Va),
                            variance_S=str(VS),star_energy=str(star),DD_energy=str(dd),
                            trace_energy=str(star+dd)))
    return dict(rows=rows,columns=cols,U=U,L=L,states=len(chain.states),balanced=len(B),
                defects=len(D),completion_weights=sorted(set(w)),
                neighbor_weight_ratios=sorted(set(str(F(S[b],w[b])) for b in B)),
                exact_observables=records)

def generic_obstruction(r,U):
    p=r*r;k=p*(p-1);q=r*U+1
    varB=F(q*(q*q-1),12)
    varD=k*varB
    energy=q-1
    ratio=varD/energy
    assert ratio==F(k*q*(q+1),12)
    # Centers linked by three-edge repair/bridge/repair paths; each repair
    # edge occurs at most twice, yielding Efull >= (1/6) sum(delta H)^2.
    balanced_upper=3*q*(q-1)
    balanced_lower=varB/energy
    inverse_gap_lower=2*(p+1)*ratio
    return dict(scope='abstract graph, not a physical-table construction',p=p,U=U,
                balanced_centers=q,defects_per_center=k,full_degree_bound=p+1,
                variance_B=str(varB),variance_D=str(varD),trace_energy=energy,
                transversal_constant_lower=str(balanced_lower),
                transversal_constant_upper=balanced_upper,
                defect_variance_over_energy=str(ratio),
                normalized_inverse_gap_lower=str(inverse_gap_lower))

def actual_load(p,L=7):
    U=p+1;T=2*U+p*L;K=U+p*L
    rows=[T]*p;cols=[U-1,U,p*T-2*U+1]
    assert sum(rows)==sum(cols) and U-1==p
    assert min(rows)>=U and cols[0]<U<=min(cols[1:])
    w=comb(K+p-1,p-1)
    ell=p*(p-1)
    # Balanced A=(1,...,1), every ordered distinct label yields x=A,
    # q=A+e_s-e_t, with identical residual completion sets/counts.
    c_other=comb(K+p-2,p-1)
    assert F(c_other,w)==F(K,K+p-1)
    S=ell*(w+c_other)
    return dict(p=p,U=U,L=L,row_margin=T,column_margins=cols,
                completion_weight=w,designated_repair_fiber_load=ell,
                accepted_balanced_degree_weight=str(F(S,w)),
                explanation='exact nonempty p-by-2 completion block; no fiber enumeration')

def one_column_check():
    from collections import defaultdict
    rows,cols,U,L=(3,3,3),(2,3,4),3,7
    c=build_rescaled_ideal_chain(TableProblem(rows,cols),U=U,L=L)
    ct=build_rescaled_ideal_chain(TableProblem(cols,rows),U=U,L=L)
    lookup={s:i for i,s in enumerate(c.states)}
    trans_lookup={(s.row_view,s.column_view):i for i,s in enumerate(ct.states)}
    p,H=len(c.small_cells),cols[0]
    assert c.small_cells==((0,0),(1,0),(2,0)) and not c.problem.row_sums[0]<U
    B=[i for i,s in enumerate(c.states) if s.balanced]
    D=[i for i,s in enumerate(c.states) if not s.balanced]
    loads=defaultdict(list)
    for d in D:
        x,q=c.states[d].row_view,c.states[d].column_view
        repair=lookup[type(c.states[d])(x,x)]
        s,t=c.states[d].defect_labels()
        assert x[t]>0 and sum(x)==sum(q)==H and max(x+q)<=H<U
        assert c.completions[d]==c.completions[repair]
        loads[repair].append(d)
    for b in B:
        supp=sum(v>0 for v in c.states[b].row_view)
        assert len(loads[b])==(p-1)*supp<=(p-1)*min(p,H)
        assert sum(c.completion_counts[d] for d in loads[b])==len(loads[b])*c.completion_counts[b]
    checked=0
    for s in range(p):
        prefixes={c.states[b].row_view[:s] for b in B}
        for prefix in prefixes:
            choices={c.states[b].row_view[s] for b in B if c.states[b].row_view[:s]==prefix}
            for ell in range(min(choices)+1,max(choices)+1):
                left=[b for b in B if c.states[b].row_view[:s]==prefix and c.states[b].row_view[s]==ell-1]
                a=sum(c.completion_counts[b] for b in left)
                moment=sum(c.completion_counts[b]*sum(v*(U+1-v) for v in c.states[b].row_view[s+1:]) for b in left)
                actual=0
                for d in D:
                    root,t=c.states[d].defect_labels();x=c.states[d].row_view
                    if root==s and t>s and x[:s]==prefix and x[s]==ell-1:
                        actual+=c.completion_counts[d]*x[t]*(U+1-x[t])
                assert actual==moment<=H*(U+1)*a
                checked+=1
    mapping=[trans_lookup[(s.column_view,s.row_view)] for s in c.states]
    assert len(mapping)==len(ct.states)==len(set(mapping))
    for i,ti in enumerate(mapping):
        assert c.completion_counts[i]==ct.completion_counts[ti]
        assert {mapping[j] for j in c.neighbors[i]}==set(ct.neighbors[ti])
        for j in c.neighbors[i]:assert c.acceptance_counts[i][j]==ct.acceptance_counts[ti][mapping[j]]
    return dict(rows=rows,columns=cols,U=U,L=L,states=len(c.states),balanced=len(B),defects=len(D),
                completion_weights=sorted(set(c.completion_counts)),contexts=checked,
                exact_repair_loads=sorted(set(len(v) for v in loads.values())),
                load_envelope=(p-1)*min(p,H),transpose_graph_and_conductance_equivalence='passed')

if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Exact checks require assertions; run without -O.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'.local/reports/direct-defect-variance.json')
    args=parser.parse_args()
    out=dict(checks='passed',scope='exact identities and generic-method obstruction; no new universal gap bound',
             physical=[physical_case(*args) for args in [((2,2,1),(2,2,1),2,7),
                                                        ((3,3,1),(4,2,1),2,7),
                                                        ((2,2,2),(4,2),3,1)]],
             generic_obstruction=[generic_obstruction(r,2) for r in (2,3,4)],
             actual_quadratic_load=[actual_load(p) for p in (3,10,100)],
             one_small_column=one_column_check())
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(checks=out['checks'],physical_states=[c['states'] for c in out['physical']],
                         weighted_counts=[c['completion_weights'] for c in out['physical']])))
