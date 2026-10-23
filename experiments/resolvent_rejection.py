"""Exact rational resolvent and finite absorption checks; no floating spectra."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import json


def dot(x,y): return sum(a*b for a,b in zip(x,y))
def tv(x,y):
    assert sum(x)==sum(y)
    return sum(abs(a-b) for a,b in zip(x,y))/2
def mv(P,x): return tuple(dot(row,x) for row in P)
def evolve(mu,P): return tuple(sum(mu[i]*P[i][j] for i in range(len(mu))) for j in range(len(mu)))
def matmul(P,Q): return tuple(tuple(sum(P[i][k]*Q[k][j] for k in range(len(P))) for j in range(len(P))) for i in range(len(P)))


def solve(M,b):
    n=len(b)
    rows=[list(row)+[b[i]] for i,row in enumerate(M)]
    for col in range(n):
        pivot=next(i for i in range(col,n) if rows[i][col])
        rows[col],rows[pivot]=rows[pivot],rows[col]
        factor=rows[col][col]
        rows[col]=[v/factor for v in rows[col]]
        for i in range(n):
            if i!=col:
                factor=rows[i][col]
                rows[i]=[a-factor*b for a,b in zip(rows[i],rows[col])]
    return tuple(row[-1] for row in rows)


def check(pi,Q,rho,accept,mode):
    n=len(pi)
    assert all(sum(row)==1 and min(row)>=0 for row in Q)
    assert evolve(pi,Q)==pi
    assert all(pi[i]*Q[i][j]==pi[j]*Q[j][i] for i in range(n) for j in range(n))
    f=tuple(1-a for a in accept)
    s=dot(pi,accept)
    assert s>0
    if mode=='identity':
        A=tuple(tuple(a*F(i==j) for j in range(n)) for i,a in enumerate(accept))
    else:
        A=tuple((a*F(i,n-1),a*(1-F(i,n-1))) for i,a in enumerate(accept))
    Y=len(A[0])
    nu=tuple(sum(pi[i]*A[i][j] for i in range(n))/s for j in range(Y))
    w=solve(tuple(tuple(F(i==j)-Q[i][j]*f[j] for j in range(n)) for i in range(n)),(F(1),)*n)
    assert min(w)>=0 and w==tuple(1+x for x in mv(Q,tuple(a*b for a,b in zip(f,w))))
    assert dot(pi,tuple(a*b for a,b in zip(accept,w)))==1
    m=dot(pi,w)
    assert m<=1/(s*(1-rho))
    variance=dot(pi,tuple((x-m)**2 for x in w))
    assert variance<=rho**2*m*m*s*(1-s)/(1-rho)**2
    infinity=tuple(sum(pi[i]*w[i]*A[i][j] for i in range(n)) for j in range(Y))
    bias=tv(infinity,nu)
    bound=rho/(2*(1-rho)**2)
    assert bias<=bound
    assert bias*bias<=s*variance/4
    assert 4*(1-rho)**4*bias*bias<=rho*rho*(1-s)
    lam=1-(1-rho)*s
    finite=[]
    for R in (1,2,8):
        survivor=pi
        output=[F(0)]*Y
        for mark in range(R):
            for j in range(Y): output[j]+=sum(survivor[i]*A[i][j] for i in range(n))
            survivor=tuple(x*y for x,y in zip(survivor,f))
            if mark+1<R: survivor=evolve(survivor,Q)
        failure=sum(survivor)
        assert failure<=(1-s)*lam**(R-1)<=lam**R
        output[0]+=failure
        assert sum(output)==1
        assert tv(output,nu)<=bias+failure<=bound+lam**R
        finite.append({'marks':R,'failure':failure,'failure_bound':lam**R,'TV_target':tv(output,nu)})
    return {'stationary':pi,'acceptance':accept,'output_mode':mode,'success':s,
            'centered_contraction':rho,'target':nu,'infinite_output':infinity,
            'infinite_TV':bias,'bias_bound':bound,'expected_marks':m,'finite':finite}


def mixture(pi,alpha,t):
    rho=alpha**t
    return tuple(tuple(rho*F(i==j)+(1-rho)*p for j,p in enumerate(pi)) for i in range(len(pi))),rho


def anisotropic(rare,t):
    pi=(1-2*rare,rare,rare)
    def product(i,j):
        if i==j==1: return (1-rare)/rare
        if (i==1)!=(j==1): return F(-1)
        return rare/(1-rare)
    E=tuple(tuple(pi[j]*product(i,j) for j in range(3)) for i in range(3))
    assert matmul(E,E)==E and all(sum(row)==0 for row in E)
    rho,u=F(3,4)**t,F(1,2)**t
    Q=tuple(tuple(pi[j]+u*(F(i==j)-pi[j])+(rho-u)*E[i][j] for j in range(3)) for i in range(3))
    P=tuple(tuple(F(i==j,2)+pi[j]/2+E[i][j]/4 for j in range(3)) for i in range(3))
    assert all(row[i]>=F(1,2) for i,row in enumerate(P))
    actual=tuple(tuple(F(i==j) for j in range(3)) for i in range(3))
    for _ in range(t): actual=matmul(actual,P)
    assert actual==Q
    return pi,Q,rho,u


def cold_example(length):
    pi=tuple(F(2**i,2**(length+1)-1) for i in range(length+1))
    P=[]
    for i in range(length+1):
        row=[F(0)]*(length+1)
        row[min(i+1,length)]+=F(1,3)
        row[max(i-1,0)]+=F(1,6)
        row[i]+=F(1,2)
        P.append(tuple(row))
    assert evolve(pi,P)==pi
    assert all(pi[i]*P[i][j]==pi[j]*P[j][i] for i in range(length+1) for j in range(length+1))
    tau_c=F(0)
    for mask in range(1,2**(length+1)-1):
        subset=[i for i in range(length+1) if mask>>i&1]
        mass=sum(pi[i] for i in subset)
        flow=sum(pi[i]*P[i][j] for i in subset for j in range(length+1) if j not in subset)
        tau_c=max(tau_c,mass*(1-mass)/flow)
    assert tau_c<=6
    mu=(F(1),)+(F(0),)*length
    for t in range(length):
        assert mu[length]==0 and tv(mu,pi)>=pi[length]>F(1,2)
        mu=evolve(mu,P)
    return {'length':length,'pi_min':pi[0],'largest_state_mass':pi[-1],
            'exact_flow_parameter':tau_c,'uniform_relaxation_allowance':288,
            'point_start_TV_before_length_steps':'>1/2'}


def run():
    pi=(F(1,2),F(1,3),F(1,6))
    configurations=[(F(1,3),F(1,2),F(1)),(F(0),F(1,2),F(1)),
                    (F(1),F(0),F(1)),(F(1),)*3,(F(1,30),F(1,20),F(1,10))]
    cases=[]
    for t,accept,mode in product((1,2,4),configurations,('identity','mixed')):
        Q,rho=mixture(pi,F(1,2),t)
        cases.append(check(pi,Q,rho,accept,mode))
    rare_cases=[]
    for rare in (F(1,100),F(1,1000),F(1,1000000)):
        pi,Q,rho,u=anisotropic(rare,8)
        result=check(pi,Q,rho,(F(0),F(1),F(1)),'identity')
        exact=(1-2*rare)*(rho-u)/(2*((2-rho-u)-2*rare*(1-rho)))
        assert result['infinite_TV']==exact
        result['rare_weight']=rare
        result['TV_divided_by_contraction']=exact/rho
        rare_cases.append(result)
    return {'evidence':'exact finite matrices/resolvents; no numerical eigenvalue estimates',
            'ordinary_case_count':len(cases),'cases':cases,'rare_hit_counterexamples':rare_cases,
            'cold_start_counterexamples':[cold_example(n) for n in (2,4,8)],
            'checks':'density orientation, visit/success normalization, nonconstant/zero/one acceptance, randomized outputs, finite-R failure and output bounds passed'}


def jsonable(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {k:jsonable(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [jsonable(v) for v in x]
    return x


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    if not __debug__:
        parser.error("run without -O so the exact checks remain enabled")
    args=parser.parse_args()
    rendered=json.dumps(jsonable(run()),indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(rendered)
        print(f'Wrote {args.output}: 33 exact resolvent configurations passed.')
    else: print(rendered,end='')
