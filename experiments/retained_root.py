"""Retained-root stencil and mode-anchor transport: exact finite checks.

Physical contexts use actual completion weights and effective-width encoding.
The general theorem and its hypotheses are in docs/retained-root-transport.md.
"""
import argparse
from fractions import Fraction as Q
from pathlib import Path
from random import Random
import json

def check_abstract_case(z,cs,K,mode):
    N=len(z)-1
    xis=[Q(1,z[l-1])+Q(1,z[l])+Q(2*cs[l],z[l-1]*z[l])
          -Q(cs[l-1],z[l-1]**2)-Q(cs[l+1],z[l]**2) for l in range(1,N+1)]
    for seq,cseq,m in ((z,cs,mode),(z[::-1],cs[::-1],N-mode)):
        S=0;base=Q(0);correction=Q(0)
        for l in range(1,m+1):
            a,b=seq[l-1:l+1];S+=a
            base+=S*(Q(1,a)+Q(1,b))
            correction+=S*(Q(2*cseq[l],a*b)-Q(cseq[l-1],a*a)-Q(cseq[l+1],b*b))
        assert base<=m*(m+1)
        if m:
            collected=-Q(seq[0]*cseq[0],seq[0]**2)
            for j in range(1,m):
                a,b=seq[j-1:j+1];Sj=sum(seq[:j])
                D=-Q(Sj*(a-b)**2,a*a*b*b)+Q(b-a,a*b)
                assert D<=Q(b-a,b*b)
                assert cseq[j]*D<=K
                collected+=cseq[j]*D
            a,b=seq[m-1:m+1];Sm=sum(seq[:m])
            Dend=Q(2*Sm,a*b)-Q(Sm-a,a*a)
            assert Dend<=Q(Sm+a,a*b)
            assert cseq[m]*Dend<=K*(m+1)
            collected+=cseq[m]*Dend-Q(Sm*cseq[m+1],b*b)
            assert collected==correction
        assert correction<=2*K*m
        assert base+correction<=m*(m+1)+2*K*m
    return min(xis)>=0


def completion_count(R,P):
    assert sum(R)==sum(P)
    if min(R+P)<0:return 0
    return max(0,min(R[0],P[0])-max(0,P[0]-R[1])+1)

def fiber(rows,cols,cutoff,L,width,a,t=None):
    root_q=a+(t is not None)
    if a<0 or root_q<0 or a>width or root_q>width:return (0,0)
    remaining_x=rows[0]-a
    remaining_q=cols[0]-root_q
    if min(remaining_x,remaining_q)<0:return (0,0)
    mass=weighted=0
    for x01 in range(remaining_x+1):
        for q10 in range(remaining_q+1):
            x=[a,x01,remaining_x-x01,q10,remaining_q-q10]
            q=list(x);q[0]=root_q
            if t in (1,2):q[t]-=1
            elif t in (3,4):x[t]+=1
            if min(x+q)<0 or max(x+q)>width:continue
            assert all(r>=cutoff for r in rows[1:])
            assert all(c>=cutoff for c in cols[1:])
            R=[rows[1]-x[3]+2*L,rows[2]-x[4]+2*L]
            P=[cols[1]-q[1]+2*L,cols[2]-q[2]+2*L]
            w=completion_count(R,P)
            mass+=w
            if t is not None:weighted+=w*x[t]*(width+1-x[t])
    return mass,weighted

def anchor_certificate(z,xis):
    assert len(xis)==len(z)-1
    assert min(xis,default=Q(0))>=0
    S=[Q(0)]
    for xi in xis:S.append(S[-1]+xi)
    anchors=[]
    for m in range(len(z)):
        left=sum((z[i]*(S[m]-S[i]) for i in range(m)),Q(0))
        right=sum((z[i]*(S[i]-S[m]) for i in range(m+1,len(z))),Q(0))
        anchors.append(max(left,right))
    best=min(range(len(z)),key=lambda m:anchors[m])
    return best,anchors[best]

def case(rows,cols,U,L=1):
    assert rows[0]<U<=min(rows[1:]) and cols[0]<U<=min(cols[1:])
    assert sum(rows)==sum(cols)
    V=max(rows[0],cols[0])+1
    M=min(rows[0],cols[0])
    z=[fiber(rows,cols,U,L,V,j)[0] for j in range(M+1)]
    assert min(z)>0
    cs=[sum(fiber(rows,cols,U,L,V,j,t)[1] for t in range(1,5)) for j in range(-1,M+1)]
    K=4*((V+1)**2//4)
    xis=[]
    for ell in range(1,M+1):
        left,right=z[ell-1:ell+1]
        B=cs[ell-1:ell+2]
        assert 0<=B[1]<=K*max(left,right)
        xi=Q(1,left)+Q(1,right)-Q(B[0],left**2)+Q(2*B[1],left*right)-Q(B[2],right**2)
        xis.append(xi)
    anchor,gamma=anchor_certificate(z,xis)
    mode=max(range(len(z)),key=lambda i:z[i])
    assert z[:mode+1]==sorted(z[:mode+1])
    assert z[mode:]==sorted(z[mode:],reverse=True)
    theorem_bound=M*(M+1)+2*K*M
    assert gamma<=theorem_bound
    return dict(rows=rows,cols=cols,U=U,L=L,V=V,p=5,z=z,xis=list(map(str,xis)),
                anchor=anchor,gamma=str(gamma),gamma_over_pV2=str(gamma/(5*V**2)),
                gamma_over_pV3=str(gamma/(5*V**3)),theorem_bound=theorem_bound)


def run():
    rng=Random(115)
    count=3000
    positive_xi=0
    for _ in range(count):
        N=rng.randrange(1,25)
        mode=rng.randrange(N+1)
        peak=rng.randrange(1,10001)
        z=sorted(rng.randrange(1,peak+1) for _ in range(mode))+[peak]
        z+=sorted((rng.randrange(1,peak+1) for _ in range(N-mode)),reverse=True)
        K=rng.randrange(0,10001)
        cs=[rng.randrange(0,10001)]
        cs += [Q(rng.randrange(0,101),100)*K*max(z[l-1],z[l]) for l in range(1,N+1)]
        cs += [rng.randrange(0,10001)]
        positive_xi+=check_abstract_case(z,cs,K,mode)
    cases=[case((M,U,U),(M,U,U),U,L)
           for U in (9,17,33,65,129)
           for M in (1,(U-1)//4,(U-1)//2,U-1)
           for L in (1,3*39)]
    return dict(checks="passed", abstract_cases=count, nonnegative_xi_cases=positive_xi,
                physical_contexts=len(cases), cases=cases,
                scope="Exact scalar and actual weighted-context checks; arbitrary-parameter proof is separate.")

if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    if not __debug__:
        parser.error("run without -O so the exact checks remain enabled")
    args=parser.parse_args()
    report=run()
    rendered=json.dumps(report,indent=2)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(rendered)
        print(f"Wrote {args.output}: all retained-root exact checks passed.")
    else:
        print(rendered,end="")
