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
    b=C=2;U=4;h=2;H=U-1;L=7;delta=F(41,42);K_h=(h+1)**2//4
    T1=42*C*(b*H+1)+U;J=T1+C*L+h+1;T2=b*H+C*J-h-T1
    problem=TableProblem((h,T1,T2),(H,)*b+(J,)*C)
    cells=tuple((i,j) for i in range(3) for j in range(b+C) if i==0 or j<b)
    idx={v:i for i,v in enumerate(cells)};p=len(cells)
    def vec(A):return tuple(A[v] for v in cells)
    def view(d):return dict(zip(cells,d.row_view)),dict(zip(cells,d.column_view))
    def counts(d):
        x,q=view(d)
        assert all(0<=z<=U for z in d.row_view+d.column_view)
        assert sum(x[0,j] for j in range(b+C))==h
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
    def compositions(total,parts):
        if parts==1:
            yield (total,)
        else:
            for z in range(total+1):
                for rest in compositions(total-z,parts-1):
                    yield (z,)+rest
    for vv in compositions(h,b+C):
        for y in product(*(range(H-vv[j]+1) for j in range(b))):
            A={v:0 for v in cells}
            for j,z in enumerate(vv):A[0,j]=z
            for j,z in enumerate(y):A[1,j]=z;A[2,j]=H-vv[j]-z
            d=PhysicalState(vec(A),vec(A));weight(d);balanced.append(d);profiles[d]=A;place[d]=sum(vv[b:]);lookup[d.row_view]=d
    compositions_h=tuple(compositions(h,b+C))
    slice_sizes=Counter(tuple(profiles[A][0,j] for j in range(b+C)) for A in balanced)
    coupling_lengths=set();coupling_edges=0
    for vv in compositions_h:
        count=1
        for j in range(b):count*=U-vv[j]
        assert slice_sizes[vv]==count and F(U**b,2)<=count<=U**b
        for j in range(b):
            if vv[j]==0:continue
            n=U-vv[j];coupling_lengths.add(n)
            target=[F(0)]*(n+1)
            for y in range(n):
                target[y]+=F(n-y,n*(n+1))
                target[y+1]+=F(y+1,n*(n+1))
            assert target==[F(1,n+1)]*(n+1)
            coupling_edges+=C
    directed_flow=defaultdict(F);bip_edges=set()
    def transfer(vv,i,j):
        z=list(vv);z[i]-=1;z[j]+=1;return tuple(z)
    for vv in compositions_h:
        for i in range(b+C):
            if vv[i]==0:continue
            for j in range(b+C):
                if i==j:continue
                target=transfer(vv,i,j)
                if (i<b)!=(j<b):
                    bip_edges.add((vv,target));continue
                for k in range(b,b+C) if i<b else range(b):
                    mid=transfer(vv,i,k)
                    directed_flow[vv,mid]+=F(2,b)
                    directed_flow[mid,target]+=F(2,b)
    assert set(directed_flow)<=bip_edges
    assert max(directed_flow.values())<=F(4*(b-1),b)
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
        for P in range(b):
            if av[0,P]==0:continue
            for c in range(b,b+C):
                for r in (1,2):
                    q=dict(av);q[0,P]-=1;q[0,c]+=1;q[r,P]+=1;B=lookup[vec(q)]
                    x=dict(av);y=dict(av);x[0,P]-=1;x[0,c]+=1;y[0,P]-=1;y[r,P]+=1
                    d=PhysicalState(vec(x),vec(y))
                    assert d not in jump_nodes;jump_nodes.add(d)
                    assert repair[d]==A and d in db[A] and d in db[B] and adjacent(d,B)
                    we=min(weights[A],weights[B]);assert db[B][d]>=we/2
                    jumps.append((A,B,we,d));jump_degree[B]+=1
    assert max(endpoint_charge.values())==1 and max(jump_degree.values())<=2*b*min(b,h)
    records=[]
    for mode in range(4):
        g={d:(F((i%7)-3,1+i%3) if mode==0 else F(profiles[repair[d]][1,0]) if mode==1 else F(place[repair[d]]) if mode==2 else F(sum(d.row_view[idx[1,j]] for j in range(b)))) for i,d in enumerate(defects)}
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
        assert ej<=(12+F(24*min(b,h),b))*star
        assert vunit<=F(U*U,8)*egu+F(5*K_h,b)*eju
        assert vn<=F(2*b*b*U*U,delta)*eg+F(80*b*K_h,delta)*ej
        assert vd<=751*b*U*U*(star+edd)
        records.append(dict(observable=mode,variance_D=str(vd),repair_noise=str(N),variance_nu=str(vn),star_energy=str(star),DD_bridge_energy=str(edd),grid_center_energy=str(eg),jump_center_energy=str(ej)))
    return dict(checks='passed',scope='One h=2,U=4,b=2 focused exact fixture with four observables; all-parameter all-observable derivation is separate, no runtime claim',
                schema_version=1,
                normalization='Raw ordinary completion cardinalities and unordered accepted energies; unchanged physical clock',
                evidence_limits='No dense completions, full DD matrix, all-observable finite matrix certificate, Lean compilation or runtime benchmark. The inclusion-process theorem is a separate finite-state mathematical proof, not inferred from this fixture.',
                created_utc=datetime.now(timezone.utc).isoformat(),
                target_law='ordinary_uniform_completion_cardinalities',
                upstream_pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
                source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
                slice_law_check=dict(compositions=len(compositions_h),min_slice_size=min(slice_sizes.values()),max_slice_size=max(slice_sizes.values()),uniform_coupling_source_lengths=sorted(coupling_lengths),coupled_composition_edges=coupling_edges,directed_bipartite_edges=len(bip_edges),max_within_part_path_energy_charge=str(max(directed_flow.values()))),
                rows=problem.row_sums,cols=problem.column_sums,h=h,U=U,L=L,p=p,balanced=len(balanced),defects=len(defects),DB_incidences=sum(len(ns) for ns in db.values()),grid_center_edges=len(grid),parallel_DD_edges=len(dd),jump_shared_defects=len(jumps),max_endpoint_charge=max(endpoint_charge.values()),max_incoming_jump_degree=max(jump_degree.values()),exact_observables=records,
                source_sha256={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in ['docs/thin-row-extension.md','experiments/thin_row_extension.py','src/contingency115/general_neighbors.py','src/contingency115/ideal_chain.py']})
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'.local/reports/thin-row-extension.json')
    args=parser.parse_args()
    if not __debug__:parser.error('run without -O: exact assertions must remain enabled')
    out=args.output
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(run(),indent=2)+'\n')
    print('Focused thin-row fixture passed; result written to the requested output.')
