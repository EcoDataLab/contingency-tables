"""One focused actual thin family: literal bridges, counts, charges and identities.

Enumerates selected profiles and catalogued DB incidences; computes ordinary
cap-vacuous counts, never dense completions or a full DD adjacency matrix.
"""
from collections import Counter,defaultdict
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'src'))
from contingency115.general_neighbors import BalancedNeighborCatalog
from contingency115.ideal_chain import PhysicalState
from contingency115.tables import TableProblem

def variance(weights,values):
    mass=sum(weights);mean=sum(w*x for w,x in zip(weights,values))/mass
    return sum(w*(x-mean)**2 for w,x in zip(weights,values))

def run():
    b=C=2;U=3;H=U-1;L=7;delta=F(41,42)
    T1=42*C*(b*H+1)+U;J=T1+C*L+1;T2=b*H+C*J-1-T1
    problem=TableProblem((1,T1,T2),(H,)*b+(J,)*C)
    cells=tuple((i,j) for i in range(3) for j in range(b+C) if i==0 or j<b)
    idx={v:i for i,v in enumerate(cells)};p=len(cells)
    def vec(A):return tuple(A[v] for v in cells)
    def view(d):return dict(zip(cells,d.row_view)),dict(zip(cells,d.column_view))
    def counts(d):
        x,q=view(d)
        assert all(0<=z<=U for z in d.row_view+d.column_view)
        assert sum(x[0,j] for j in range(b+C))==1
        assert all(sum(q[i,j] for i in range(3))==H for j in range(b))
        used=[sum(x.get((i,j),0) for j in range(b+C)) for i in range(3)]
        assert all(z<=r for z,r in zip(used,problem.row_sums))
        rr=tuple(problem.row_sums[i]-used[i]+C*L for i in (1,2))
        cc=tuple(J-q[0,j]+2*L for j in range(b,b+C))
        assert sum(rr)==sum(cc) and 0<=rr[0]<=min(cc)
        return comb(rr[0]+C-1,C-1),(rr,cc)
    def adjacent(d,e):
        dz=[x-y for x,y in zip(e.row_view,d.row_view)]+[y-x for x,y in zip(e.column_view,d.column_view)]
        return sorted(x for x in dz if x)==[-1,1]
    residuals={};weights={}
    def weight(d):
        if d not in weights:weights[d],residuals[d]=counts(d)
        return weights[d]
    def accepted(d,e):
        rd,cd=residuals[d];re,ce=residuals[e]
        dr=[y-x for x,y in zip(rd,re)];dc=[y-x for x,y in zip(cd,ce)]
        change=[[dr[0]-sum(dc[1:]) if i==j==0 else dc[j] if i==0 else dr[i] if j==0 else 0 for j in range(C)] for i in range(2)]
        assert max(abs(v) for row in change for v in row)<=1
        # Row2 entries always positive: col capacity minus entire row1 > 0.
        assert all(v-rd[0]>=2*L-1 for v in cd)
        k=sum(max(0,-v) for v in change[0])
        return comb(rd[0]-k+C-1,C-1)
    balanced=[];profiles={};place={};lookup={}
    for P in range(b+C):
        for y in product(*(range(H-int(j==P)+1) for j in range(b))):
            A={v:0 for v in cells};A[0,P]=1
            for j,z in enumerate(y):A[1,j]=z;A[2,j]=H-int(j==P)-z
            d=PhysicalState(vec(A),vec(A));weight(d);balanced.append(d);profiles[d]=A;place[d]=P;lookup[d.row_view]=d
    repair={};db=defaultdict(dict)
    for A in balanced:
        cat=BalancedNeighborCatalog.from_problem(problem,A,U=U,L=L)
        for rank in range(cat.degree):
            d=cat.unrank(rank);weight(d)
            c=accepted(A,d);assert c==accepted(d,A)
            assert c>=F(weights[A],2) and c>=F(weights[d],2)
            db[A][d]=c
            if rank<cat.counts[0]+cat.counts[1]:
                if d in repair:assert repair[d]==A
                repair[d]=A
    defects=sorted({d for ns in db.values() for d in ns})
    assert set(defects)==set(repair)
    assert all(sum(d in ns for ns in db.values())<=2 for d in defects)
    nu={A:sum(weights[d] for d in defects if repair[d]==A) for A in balanced}
    W=comb(T1+C*L+C-1,C-1)
    for A in balanced:
        assert delta*W<=weights[A]<=W and F(b*b*weights[A],2)<=nu[A]<16*b*b*weights[A]
    grid=[];dd={};endpoint_charge=Counter();jumps=[];jump_degree=Counter();jump_nodes=set()
    def inverse(A,s,t):
        q=profiles[A];x=dict(q);y=dict(q);v=(t[0],s[1])
        x[t]+=1;y[s]+=1
        if v in q:x[v]-=1;y[v]-=1
        return PhysicalState(vec(x),vec(y))
    for A in balanced:
        av=profiles[A]
        for j in range(b):
            if av[1,j]==0:continue
            q=dict(av);q[1,j]-=1;q[2,j]+=1;B=lookup[vec(q)]
            we=min(weights[A],weights[B]);grid.append((A,B,we))
            src=[inverse(A,(0,j),(1,k)) for k in range(b)]
            tgt=[inverse(B,(0,j),(2,k)) for k in range(b)]
            for d in src:assert repair[d]==A;endpoint_charge[d]+=1
            for d in tgt:assert repair[d]==B;endpoint_charge[d]+=1
            for d in src:
                for e in tgt:
                    assert adjacent(d,e)
                    c=accepted(d,e);assert c==accepted(e,d) and c>=we/2
                    key=tuple(sorted((d,e)));assert key not in dd;dd[key]=c
        P=place[A]
        if P>=b:continue
        for c in range(b,b+C):
            for r in (1,2):
                q=dict(av);q[0,P]-=1;q[0,c]+=1;q[r,P]+=1;B=lookup[vec(q)]
                x=dict(av);y=dict(av);x[0,P]-=1;x[0,c]+=1;y[0,P]-=1;y[r,P]+=1
                d=PhysicalState(vec(x),vec(y))
                assert d not in jump_nodes;jump_nodes.add(d)
                assert repair[d]==A and d in db[A] and d in db[B] and adjacent(d,B)
                we=min(weights[A],weights[B]);assert db[B][d]>=we/2
                jumps.append((A,B,we,d));jump_degree[B]+=1
    assert max(endpoint_charge.values())==1 and max(jump_degree.values())<=2*b
    records=[]
    for mode in range(4):
        g={d:(F((i%7)-3,1+i%3) if mode==0 else F(profiles[repair[d]][1,0]) if mode==1 else F(place[repair[d]]>=b) if mode==2 else F(sum(d.row_view[idx[1,j]] for j in range(b)))) for i,d in enumerate(defects)}
        Fcenter={A:sum(weights[d]*g[d] for d in defects if repair[d]==A)/nu[A] for A in balanced}
        N=sum(weights[d]*(g[d]-Fcenter[repair[d]])**2 for d in defects)
        Hcenter={A:sum(c*g[d] for d,c in db[A].items())/sum(db[A].values()) for A in balanced}
        star=sum(c*(g[d]-Hcenter[A])**2 for A in balanced for d,c in db[A].items())
        edd=sum(c*(g[d]-g[e])**2 for (d,e),c in dd.items())
        eg=sum(we*(Fcenter[A]-Fcenter[B])**2 for A,B,we in grid)
        ej=sum(we*(Fcenter[A]-Fcenter[B])**2 for A,B,we,d in jumps)
        egu=sum((Fcenter[A]-Fcenter[B])**2 for A,B,we in grid)
        eju=sum((Fcenter[A]-Fcenter[B])**2 for A,B,we,d in jumps)
        vn=variance([nu[A] for A in balanced],[Fcenter[A] for A in balanced])
        vunit=variance([1]*len(balanced),[Fcenter[A] for A in balanced])
        vd=variance([weights[d] for d in defects],[g[d] for d in defects])
        assert vd==N+vn and N<=2*star
        assert eg<=F(6,b*b)*edd+F(3,b)*N
        assert ej<=(6+F(24,b))*star
        assert vunit<=F(U*U,2)*egu+F(3,2*b)*eju
        assert vn<=F(8*b*b*U*U,delta)*eg+F(24*b,delta)*ej
        assert vd<=100*b*U*U*(star+edd)
        records.append(dict(observable=mode,variance_D=str(vd),repair_noise=str(N),variance_nu=str(vn),star_energy=str(star),DD_bridge_energy=str(edd),grid_center_energy=str(eg),jump_center_energy=str(ej)))
    return dict(checks='passed',scope='One finite literal bridge/count/charge fixture with four exact observables; arbitrary-parameter all-observable derivation is separate, no runtime claim',
                schema_version=1,
                normalization='Raw ordinary completion weights and unordered accepted energies; no successful-move conditioning or clock rescaling',
                evidence_limits='No dense completion enumeration, full DD matrix, eigensolver, all-observable finite certificate, Lean compilation, or runtime benchmark. Half acceptance is checked at one concrete reference corner; the derivation uses the parameter-wide reference-independent theorem.',
                rows=problem.row_sums,cols=problem.column_sums,U=U,L=L,p=p,balanced=len(balanced),defects=len(defects),DB_incidences=sum(len(ns) for ns in db.values()),grid_center_edges=len(grid),parallel_DD_edges=len(dd),jump_shared_defects=len(jumps),max_endpoint_charge=max(endpoint_charge.values()),max_incoming_jump_degree=max(jump_degree.values()),exact_observables=records,
                created_utc=datetime.now(timezone.utc).isoformat(),
                target_law='ordinary_uniform_completion_cardinalities',
                upstream_pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
                source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
                source_sha256={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in ['docs/thin-parallel-comparison.md','experiments/thin_parallel_comparison.py','src/contingency115/general_neighbors.py','src/contingency115/ideal_chain.py']})
if __name__=='__main__':
    if not __debug__:raise SystemExit('run without -O')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'.local/reports/thin-parallel-comparison.json')
    out=parser.parse_args().output
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(run(),indent=2)+'\n');print(out)
