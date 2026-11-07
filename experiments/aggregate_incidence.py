"""Exact checks of completed-fiber aggregation and reviewed shape constants.

Small actual fibers include large-crossing repairs with changed completion
weights. Finite checks supplement docs/aggregate-incidence.md; no mixing or
machine-runtime measurement is performed.
"""
from collections import Counter,defaultdict
from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction as F
import argparse,hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from contingency115.ideal_chain import PhysicalState,build_rescaled_ideal_chain
from contingency115.tables import TableProblem

def completed(backend,view,completion):
    m,n=backend.problem.shape
    X=[[0]*n for _ in range(m)]
    for (i,j),x in zip(backend.small_cells,view):X[i][j]=x
    for r,i in enumerate(backend.large_rows):
        for c,j in enumerate(backend.large_columns):X[i][j]=completion[r][c]
    return tuple(map(tuple,X))

def add_cells(X,positive,negative):
    Y=list(map(list,X));Y[positive[0]][positive[1]]+=1;Y[negative[0]][negative[1]]-=1
    return tuple(map(tuple,Y))

def audit(rows,cols,U,L=7):
    backend=build_rescaled_ideal_chain(TableProblem(rows,cols),U=U,L=L)
    m,n=backend.problem.shape;p=len(backend.small_cells)
    a,b=m-len(backend.large_rows),n-len(backend.large_columns)
    small=set(backend.small_cells)
    index={state:i for i,state in enumerate(backend.states)}
    balanced=[(i,state) for i,state in enumerate(backend.states) if state.balanced]
    Rbar=tuple(rows[i]+(len(backend.large_columns)*L if i in backend.large_rows else 0) for i in range(m))
    Cbar=tuple(cols[j]+(len(backend.large_rows)*L if j in backend.large_columns else 0) for j in range(n))
    owners=[];ll_examples=[];joint_count=0;left_seen=right_seen=ll_seen=0
    for s in range(p):
        prefixes={A.row_view[:s] for _,A in balanced}
        for prefix in sorted(prefixes):
            z=[sum(backend.completion_counts[i] for i,A in balanced
                   if A.row_view[:s]==prefix and A.row_view[s]==j) for j in range(U+1)]
            raw=Counter();grouped=defaultdict(dict);seen=set()
            Kleft=(a+b)*U*U+p*U
            Kright=U*U+(n-2)*U if rows[backend.small_cells[s][0]]<U else (b-1)*U*U
            Ksafe=(a+b+max(1,b-1))*U*U+(p+n-2)*U
            assert Kleft+Kright<=Ksafe
            for i,d in enumerate(backend.states):
                if d.balanced or d.defect_labels()[0]!=s:continue
                t=d.defect_labels()[1]
                if t<=s or d.row_view[:s]!=prefix:continue
                l=d.row_view[s]+1
                mu=d.row_view[t]*(U+1-d.row_view[t])
                assert 1<=d.row_view[t]<=U and 1<=l<=U
                raw[l]+=backend.completion_counts[i]*mu
                sp,tp=backend.small_cells[s],backend.small_cells[t]
                v=(tp[0],sp[1]);side='right' if tp[0]==sp[0] else 'left'
                for C in backend.completions[i]:
                    X=completed(backend,d.row_view,C);Q=completed(backend,d.column_view,C)
                    A=add_cells(X,v,tp)
                    assert tuple(map(sum,X))==Rbar
                    assert tuple(map(sum,zip(*Q)))==Cbar
                    assert tuple(map(sum,A))==Rbar and tuple(map(sum,zip(*A)))==Cbar
                    assert add_cells(A,tp,v)==X and add_cells(A,sp,v)==Q
                    assert min(x for row in A for x in row)>=0
                    small_values=tuple(A[r][c] for r,c in backend.small_cells)
                    repaired=PhysicalState(small_values,small_values)
                    j=index[repaired]
                    target_completion=tuple(tuple(A[r][c] for c in backend.large_columns)
                                            for r in backend.large_rows)
                    assert target_completion in backend.completions[j]
                    assert small_values[:s]==prefix
                    assert small_values[s]==l-int(side=='left')
                    At=A[tp[0]][tp[1]]
                    assert d.row_view[t]==At+int(v!=tp)
                    assert At<=U-1
                    if v==tp:assert mu<=U*At+At
                    else:assert mu<=U*(At+1)
                    assert all(sum(A[r][c] for c in range(n) if (r,c) in small)<=rows[r] for r in range(m))
                    assert all(sum(A[r][c] for r in range(m) if (r,c) in small)<=cols[c] for c in range(n))
                    assert sum(small_values)<=(a+b)*(U-1)
                    key=(l,A,t)
                    assert key not in seen;seen.add(key)
                    assert t not in grouped[l,side,A]
                    grouped[l,side,A][t]=mu
                    joint_count+=1
                    if side=='left':left_seen+=1
                    else:right_seen+=1
                    if v not in small:
                        ll_seen+=1
                        assert target_completion!=C
                        assert backend.completion_counts[i]<=backend.completion_counts[j]
                        if len(ll_examples)<3 and backend.completion_counts[i]!=backend.completion_counts[j]:
                            ll_examples.append(dict(source_x=d.row_view,source_q=d.column_view,
                                                    labels=(s,t),cross=v,source_completion=C,
                                                    target_completion=target_completion,
                                                    source_weight=backend.completion_counts[i],
                                                    target_weight=backend.completion_counts[j]))
                    else:
                        assert target_completion==C
                        assert backend.completion_counts[i]==backend.completion_counts[j]
            reconstructed=Counter()
            for (l,side,A),moments in grouped.items():
                actual=sum(moments.values())
                assert actual<=(Kleft if side=='left' else Kright)
                reconstructed[l]+=actual
            assert raw==reconstructed
            for l,cvalue in raw.items():
                assert cvalue<=Kleft*z[l-1]+Kright*z[l]
                assert cvalue<=Ksafe*max(z[l-1],z[l])
            owners.append(dict(current=s,prefix=prefix,z=z,c=dict(raw),
                               left_cap=Kleft,right_cap=Kright,safe_cap=Ksafe,
                               grouped_full_tables=len(grouped)))
    unit=not backend.large_rows or not backend.large_columns
    Q=2*(m+n)-3 if unit else 4*p-3
    assert all(len(backend.neighbors[i])<=Q for i,state in enumerate(backend.states) if not state.balanced)
    minimum_acceptance=min(F(backend.acceptance_counts[i][j],backend.completion_counts[i])
                           for i,targets in enumerate(backend.neighbors) for j in targets)
    assert minimum_acceptance>=(1 if unit else F(1,2))
    return dict(rows=rows,cols=cols,U=U,L=L,a=a,b=b,p=p,
                positive_states=len(backend.states),contexts=len(owners),owners=owners,
                completed_auxiliary_assignments=joint_count,left=left_seen,right=right_seen,
                large_crossings=ll_seen,LL_weight_change_examples=ll_examples,
                branch='unit' if unit else 'reference',degree_allowance=Q,
                minimum_acceptance=str(minimum_acceptance))

def run():
    fixtures=[audit((2,5,5),(2,5,5),5),audit((0,3,3),(0,3,3),3),
              audit((2,2),(2,2),3)]
    assert fixtures[0]['large_crossings'] and fixtures[1]['large_crossings']
    assert fixtures[0]['LL_weight_change_examples'] or fixtures[1]['LL_weight_change_examples']
    return dict(checks='passed',created_utc=datetime.now(timezone.utc).isoformat(),
                target_law='ordinary_uniform_completion_cardinalities',
                source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
                upstream_pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
                source_sha256={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in
                    ['experiments/aggregate_incidence.py','docs/aggregate-incidence.md',
                     'src/contingency115/ideal_chain.py','src/contingency115/tables.py',
                     'research/retained-root/formal/Research/RetainedPhysicalCap.lean']},
                fixtures=fixtures,
                scope='Exact finite completed-fiber injectivity and moment checks; arbitrary-parameter proof is separate, no physical-gap lower bound or runtime claim')

if __name__=='__main__':
    if not __debug__:raise SystemExit('run without -O so assertions remain enabled')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'.local/reports/aggregate-incidence.json')
    out=parser.parse_args().output
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(run(),indent=2)+'\n')
    print(out)
