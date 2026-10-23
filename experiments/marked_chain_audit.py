"""Exact small weighted-Markov audit of the one-burn spaced-mark lemma.

No physical backend or numerical eigenvalue routine is used. This checks a
reversible reset-mixture chain with analytically known centered eigenvalue1/2.
"""
import argparse
from fractions import Fraction as F
from pathlib import Path
import json


PI = (F(1,2), F(1,3), F(1,6))
ACCEPT = (F(1,3), F(1,2), F(1))
TARGET = (F(1,3),)*3
SUCCESS = sum(x*a for x,a in zip(PI,ACCEPT))


def tv(a,b):
    assert sum(a) == sum(b)
    return sum(abs(x-y) for x,y in zip(a,b))/2


def evolve(mu,steps):
    rho = F(1,2**steps)
    mass = sum(mu)
    return tuple(rho*x+(1-rho)*mass*pi for x,pi in zip(mu,PI))


def marked(initial, *, marks, spacing, check_survivors=False):
    mu = initial
    output = [F(0)]*3
    max_block_tv = F(0)
    for j in range(marks):
        for y,a in enumerate(ACCEPT):
            output[y] += mu[y]*a
        mu = tuple(x*(1-a) for x,a in zip(mu,ACCEPT))
        if check_survivors:
            g = tuple(x/pi for x,pi in zip(mu,PI))
            mass = sum(mu)
            assert all(0<=v<=1 for v in g)
            variance = sum(pi*(v-mass)**2 for pi,v in zip(PI,g))
            assert variance<=mass*(1-mass)<=F(1,4)
        if j+1 < marks:
            mixed = evolve(mu,spacing)
            if check_survivors:
                comparison = tuple(sum(mu)*pi for pi in PI)
                distance = tv(mixed,comparison)
                assert distance<=F(1,4*2**spacing)
                max_block_tv = max(max_block_tv,distance)
            mu = mixed
    failure = sum(mu)
    output[0] += failure
    assert sum(output)==1
    return tuple(output), failure, max_block_tv


def infinite_stationary_output(spacing):
    rho = F(1,2**spacing)
    raw = tuple(pi*a/(1-rho*(1-a)) for pi,a in zip(PI,ACCEPT))
    out = tuple(x/sum(raw) for x in raw)
    visits = tuple(x/a for x,a in zip(out,ACCEPT))
    survivors = tuple(x*(1-a) for x,a in zip(visits,ACCEPT))
    continued = evolve(survivors,spacing)
    assert visits == tuple(pi+x for pi,x in zip(PI,continued))
    return out


def run():
    assert SUCCESS==F(1,2)
    assert tuple(pi*a for pi,a in zip(PI,ACCEPT))==tuple(SUCCESS*x for x in TARGET)
    P = [evolve(tuple(F(i==j) for i in range(3)),1) for j in range(3)]
    assert all(row[i]>=F(1,2) for i,row in enumerate(P))
    assert all(PI[i]*P[i][j]==PI[j]*P[j][i] for i in range(3) for j in range(3))
    cases=[]
    for marks,spacing in [(1,0),(2,4),(8,0),(8,1),(8,4),(8,8)]:
        out,failure,max_tv=marked(PI,marks=marks,spacing=spacing,check_survivors=True)
        independent = tuple((1-(1-SUCCESS)**marks)*x+(1-SUCCESS)**marks*F(y==0)
                            for y,x in enumerate(TARGET))
        hybrid = F(marks-1,4*2**spacing)
        assert tv(out,independent)<=hybrid
        assert abs(failure-(1-SUCCESS)**marks)<=hybrid
        assert tv(out,TARGET)<=(1-SUCCESS)**marks+hybrid
        cases.append({'initial':'stationary','marks':marks,'spacing':spacing,
                      'output':out,'TV_target':tv(out,TARGET),'failure':failure,
                      'independent_stationary_failure':(1-SUCCESS)**marks,
                      'hybrid_output_TV':tv(out,independent),'hybrid_bound':hybrid,
                      'largest_actual_block_TV':max_tv})
    for point in range(3):
        initial=tuple(F(i==point) for i in range(3))
        burned=evolve(initial,4)
        delta=tv(burned,PI)
        out,failure,_=marked(burned,marks=8,spacing=4)
        stationary_out,_,_=marked(PI,marks=8,spacing=4)
        assert tv(out,stationary_out)<=delta
        assert tv(out,TARGET)<=delta+F(1,256)+F(7,64)
        cases.append({'initial':f'point{point}','burn':4,'marks':8,'spacing':4,
                      'burn_TV':delta,'output':out,'TV_target':tv(out,TARGET),
                      'initial_error_charged_once':True})
    unspaced,_,_=marked(PI,marks=8,spacing=0)
    assert unspaced==(F(385,768),F(85,256),F(1,6))
    assert tv(unspaced,TARGET)==F(43,256)>F(1,256)
    assert infinite_stationary_output(0)==PI
    assert infinite_stationary_output(1)==(F(9,23),F(8,23),F(6,23))
    return {'evidence':'exact finite weighted Markov checks; no sampling simulation',
            'stationary':PI,'acceptance':ACCEPT,'stationary_success':SUCCESS,
            'target':TARGET,'centered_eigenvalue':F(1,2),
            'counterexample':{'stationary_start_unspaced_8_marks_output':unspaced,
                              'TV':tv(unspaced,TARGET),'incorrect_iid_exhaustion_bound':F(1,256),
                              'infinite_one_step_output':infinite_stationary_output(1),
                              'infinite_one_step_TV':tv(infinite_stationary_output(1),TARGET)},
            'cases':cases,
            'checks':'survivor domination, centered variance, same-mass block bound, hybrid output/failure, initial burn error passed'}


def jsonable(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {k:jsonable(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [jsonable(v) for v in x]
    return x


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    rendered=json.dumps(jsonable(run()),indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(rendered)
        print(f'Wrote {args.output}: exact marked-chain checks passed.')
    else:
        print(rendered,end='')
