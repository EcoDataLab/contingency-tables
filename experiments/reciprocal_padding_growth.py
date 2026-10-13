"""Exact rational padding-growth and thin-family obstruction checks."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb,prod,isqrt
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from contingency115.tables import ExactTableSampler,TableProblem

def comps(total,parts):
    if parts==1:
        yield (total,)
        return
    for head in range(total+1):
        for tail in comps(total-head,parts-1):yield (head,)+tail

@lru_cache(None)
def count(rows,cols):return ExactTableSampler(TableProblem(rows,cols)).count()

def increment(rows,cols,i,j):
    r=list(rows);c=list(cols);r[i]+=1;c[j]+=1
    return tuple(r),tuple(c)

def one_step(rows,cols,i,j):
    old=count(rows,cols)
    r,c=increment(rows,cols,i,j)
    new=count(r,c)
    m,n=len(rows),len(cols)
    assert new*(rows[i]+1)*(cols[j]+1)<=old*(rows[i]+n)*(cols[j]+m)
    alpha,beta=F(n-1,rows[i]+n),F(m-1,cols[j]+m)
    assert F(new-old,new)<=alpha+beta-alpha*beta
    return new, F(rows[i]+n,rows[i]+1)*F(cols[j]+m,cols[j]+1)

def finite_fibers():
    checks=0
    for m,n in [(2,2),(2,3),(3,2)]:
        for total in range(5):
            for r in comps(total,m):
                for c in comps(total,n):
                    for i,j in product(range(m),range(n)):
                        one_step(r,c,i,j);checks+=1
    paths=[]
    for rows,cols,U,L in [((2,2,1),(2,2,1),2,1),
                          ((4,4,1),(4,4,1),4,2),
                          ((3,3,3),(2,7),3,2),
                          ((3,1,1),(3,2),3,1),
                          ((0,2,2),(0,2,2),2,1),
                          ((1,1),(2,0),2,7),
                          ((0,0),(0,0,0),2,7)]:
        original=count(rows,cols);r,c=rows,cols
        R=[i for i,v in enumerate(r) if v>=U]
        C=[j for j,v in enumerate(c) if v>=U]
        product_bound=F(1)
        for i,j in product(R,C):
            for _ in range(L):
                _,factor=one_step(r,c,i,j)
                product_bound*=factor
                r,c=increment(r,c,i,j)
        m,n=len(rows),len(cols);q=len(R)*len(C)*L;H=U+1;s=m+n-2
        explicit_row=prod((F(rows[i]+k+n-1,rows[i]+k)
                           for i in R for k in range(1,len(C)*L+1)),start=F(1))
        explicit_col=prod((F(cols[j]+k+m-1,cols[j]+k)
                           for j in C for k in range(1,len(R)*L+1)),start=F(1))
        assert product_bound==explicit_row*explicit_col
        frozen=(F(H+n-1,H)*F(H+m-1,H))**q
        amgm=F(2*H+s,2*H)**(2*q)
        ratio=F(count(r,c),original)
        assert ratio<=product_bound<=frozen<=amgm
        paths.append(dict(rows=rows,columns=cols,U=U,L=L,block=(len(R),len(C)),
                          actual_ratio=str(ratio),successive_product=str(product_bound),
                          frozen_bound=str(frozen),amgm_bound=str(amgm)))
    normalized=[]
    for rows,cols,i,j in [((0,0),(0,0),0,0),((1,1),(1,1),0,0),
                          ((2,2),(2,2),0,1),((2,0,1),(1,2),0,1),
                          ((0,2,2),(0,2,2),1,1)]:
        original=count(rows,cols);r,c=increment(rows,cols,i,j);enlarged=count(r,c)
        bounds=[[min(a,b) for b in c] for a in r];bounds[i][j]=0
        actual_zero=ExactTableSampler(TableProblem(r,c,upper_bounds=bounds)).count()
        assert actual_zero==enlarged-original
        alpha,beta=F(len(cols)-1,rows[i]+len(cols)),F(len(rows)-1,cols[j]+len(rows))
        normalized.append(dict(rows=rows,columns=cols,marked=(i,j),
                               original_count=original,enlarged_count=enlarged,
                               zero_count=actual_zero,zero_probability=str(F(actual_zero,enlarged)),
                               zero_probability_bound=str(alpha+beta-alpha*beta),
                               positive_probability=str(F(original,enlarged))))
    return dict(one_unit_checks=checks,padding_paths=paths,normalized_count_cases=normalized)

def dimension_scales():
    cases=0
    for m,n in [*product(range(2,31),repeat=2),(2,1000),(1000,3),(100,100)]:
        d=10+(m+1)*(n+1);s=m+n-2;U=11*d*s;H=U+1
        assert 3*s+13<=d
        for R,C in [(1,1),(m,n),(m-1,n),(m,n-1)]:
            q=7*R*C
            assert 47*q*s<=32*H
            assert U>=14
            assert 32*d**4*U**2==3872*d**6*s**2
            assert 9*(3872*d**6*s**2)<=3872*d**8
            assert 3872*d**6*s**2<=431*d**8
            cases+=1
    return dict(scalar_cases=cases,cutoff='U=11*d*(m+n-2),L=7',
                rational_gap='3872*d^6*(m+n-2)^2',
                bounded_aspect='3872*A*d^7, if (m+n-2)^2<=A*d')

def compositions_count(total,N):return comb(total+N-1,N-1)

def thin_lower(N,U,L):
    H,K=U-1,U+N*L
    B=(U+2*L)//2
    D=lambda t:compositions_count(t,N)
    tail=lambda t:F(D(t-B-1),D(t)) if t>=B+1 else F(0)
    excluded=N*(tail(H)+tail(K))
    volume=F(D(K),D(U))
    lower=max(F(0),1-excluded)*volume
    # Every retained pair of compositions has x_i,y_i<=B, and hence
    # x_i+y_i<=U+2L. It is an ACTUAL padded table in the thin family.
    assert (U-1)+U+((N-2)*U+1)==N*U
    assert 2*B<=U+2*L
    bernoulli=1+F((N-1)*N*L,U+N-1)
    assert volume>=bernoulli
    if U>=2*N*L:
        coarse=2*N*F(3,4)**(N-1)
        assert excluded<=coarse
    return dict(N=N,U=U,L=L,original_columns=(U-1,U,(N-2)*U+1),
                excluded_fraction_upper=str(excluded),
                unrestricted_volume_ratio=str(volume),
                padded_over_original_lower=str(lower),
                padded_over_original_lower_float=float(lower))

def thin_exact(N,U,L,check_count=False):
    # Make all row caps vacuous for the first two column compositions, both
    # before and after padding the N-by-2 large block.
    T=2*U+N*L;rows=(T,)*N
    columns=(U-1,U,N*T-2*U+1)
    original=compositions_count(U-1,N)*compositions_count(U,N)
    padded=compositions_count(U-1,N)*compositions_count(U+N*L,N)
    if check_count:
        assert count(rows,columns)==original
        assert count(tuple(x+2*L for x in rows),
                     (columns[0],columns[1]+N*L,columns[2]+N*L))==padded
    ratio=F(padded,original)
    lower=1+F((N-1)*N*L,U+N-1)
    assert ratio>=lower
    necessary_cutoff=(N-1)*(N*L-1)
    if U<necessary_cutoff:assert ratio>2
    return dict(N=N,U=U,L=L,rows=rows,columns=columns,
                original_count=original,padded_count=padded,ratio=str(ratio),
                bernoulli_lower=str(lower),necessary_cutoff_for_ratio_at_most_two=necessary_cutoff,
                independent_dp_count_checked=check_count)

def run():
    thin=[thin_lower(N,N*isqrt(N),7) for N in [16,25,36,64,100,144,256]]
    assert all(F(x['padded_over_original_lower'])>2 for x in thin)
    exact_thin=[thin_exact(N,U,L,True) for N,U,L in
                [(3,2,1),(3,3,7),(4,4,2),(5,5,1),(6,2,7)]]
    exact_thin += [thin_exact(N,N*isqrt(N),7) for N in [16,25,64,256]]
    return dict(checks='passed',finite=finite_fibers(),scales=dimension_scales(),
                thin_obstruction=thin,exact_thin_obstruction=exact_thin,
                source_checkout_base_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
                source_sha256={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in
                    ['experiments/reciprocal_padding_growth.py',
                     'research/constant-padding/formal/Research/ReciprocalZero.lean',
                     'formal/Math115/PaddingGrowth.lean','formal/Math115/PaddingGrowthAlgebra.lean',
                     'research/retained-root/formal/Research/GrowthScalar.lean']},
                scope='Exact counts on small fibers; exact rational upper/lower certificates, not fits or runtime claims')

if __name__=='__main__':
    if not __debug__:raise SystemExit('run without -O so exact assertions remain enabled')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'.local/reports/reciprocal-padding-growth.json')
    out=parser.parse_args().output
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(run(),indent=2)+'\n')
    print(out)
