# A general junction comparison using the actual repair law

11 October 2026. Independent AI mathematical/source review passed. This
compares one actual family of table moves with the balanced-star energy;
it is not a general inverse-gap theorem or a compiled Lean result.

Use ordinary unrestricted equal-total natural margins, m,n>=2,U>=2,
canonical source capacity as in the [physical trace](physical-defect-trace.md),
and actual directed half acceptance at L>=7. More generally a strong capacity
must exclude no full residual completion satisfying the original partial
constraints. Structural zeros, restrictive cell bounds and alternative
weights are outside this argument. Here SS means small row/small column,
LS large row/small column, and SL small row/large column.

Let B range over positive balanced centers, D over ALL positive defects,
rho be the literal selected repair, nu_B=sum_(rho(d)=B)w_d, F_B its conditional
w-mean of g, and H_B the actual accepted-star harmonic mean. Use zero
at a zero-mass center. Put

    N=sum_d w_d(g_d-F_(rho(d)))^2,
    Rerr=sum_B nu_B(F_B-H_B)^2,
    E_star=sum_(B,d) c_Bd(g_d-H_B)^2.

Finite centering in each repair fiber gives

    sum_(rho(d)=B) w_d(g_d-H_B)^2
      =sum_(rho(d)=B) w_d(g_d-F_B)^2+nu_B(F_B-H_B)^2.

Sum over B and retain designated incidences with c_(rho(d),d)>=w_d/2.
This proves the JOINT inequality N+Rerr<=2E_star.
All measures and energies here are raw, with unordered edges counted once.

## Actual junctions and their shared defect

A junction A->B removes one SS entry v=(i,j), adds one LS entry s=(r,j),
and one SL entry t=(i,c), with i,j small and r,c large:

    A_v>0, B=A-e_v+e_s+e_t.

Require both centers positive. The original target row r and column c are
active at A; padded residual positivity is not a substitute. Its shared
physical defect is

    d: X=A-e_v+e_t=B-e_s, Q=A-e_v+e_s=B-e_t.

It has ordered labels s,t and designated repair A. The selected crossing
v is positive, so its row-X and column-Q totals and FULL dense completion
set equal A's. Thus w_d=w_A. Its A-d repair edge is actual; B-d is an actual
doubled-coordinate exchange. For mu_AB=min(w_A,w_B), half acceptance gives
c_Bd>=mu_AB/2. Different junctions have different shared defects: rho and
its ordered labels recover A,B,v,s,t. No projected-weight equality across
A and B, intrinsic LL acceptance substitution, or duplicate edge is used.

## True incoming congestion is at most nu_B

At B, every incoming junction uses a positive LS entry and positive SL
entry. Let hL,hS count those positive entries. There are at most
N4(B)=hL*hS incoming junctions, each with mu_AB<=w_B. The [literal five-family catalog](../src/contingency115/general_neighbors.py)
gives

    N0=sum_(v selected,B_v>0) [rowSelectedSize(v)*colSelectedSize(v)-1].

Write a,b for the small row/column counts and R,C for the large ones.
If hL,hS are both positive then a,b>=1, hL<=Rb and hS<=aC. Since
m=a+R,n=b+C,

    bm-1>=Rb>=hL,  an-1>=aC>=hS,
    N0>=hL(bm-1)+hS(an-1)>=hL^2+hS^2>=2hL*hS>=N4.

If either count vanishes, N4=0. For each positive selected origin, its
family0 inverse labels are the selected-column and selected-row labels,
excluding the equal pair at that origin. All these distinct defects repair
to B and have the same full completion set and weight w_B. Consequently

    sum_(junctions A->B) mu_AB <=N4(B)w_B
                                  <=N0(B)w_B<=nu_B.             (1)

This avoids the looser Rb times the number of occupied large places. It
needs no positive lower bound on LL activity or a normalized tilt. Empty LS
or SL sets give zero incoming load; if nu_B=0, (1) forces zero load without
performing division. The bound requires the full repair law; retaining only selected repair
labels would invalidate it.

## Energy inequality

Define E_J,mu(F)=sum_(junctions A->B) mu_AB(F_A-F_B)^2. For each junction expand

    F_A-F_B=(F_A-g_d)+(g_d-H_B)+(H_B-F_B).

The three-term square bound, mu_AB<=w_d, distinct shared defects and distinct
B-d incidences, c_Bd>=mu_AB/2, and (1) imply

    E_J,mu(F) <=3N+6E_star+3Rerr
                <=12E_star.                                  (2)

The last step uses the joint N+Rerr bound, rather than spending its two
parts separately. All source weights and accepted conductances are literal.
The unit branch has no junctions when either large side is absent; other
empty-label cases also contribute zero.

Equation (2) holds for EVERY defect observable with F its actual conditional
repair mean. It does not bound arbitrary center observables using DD edges alone,
and does not prove a Poincare inequality for nu. It supplies the family4 star comparison component
for general masks and removes an artificial h-congestion loss from the
restricted growing-row extension.

The [extension and review record](growing-row-extension-review.md) binds the
reviewed sources and their public adaptation. The proof uses the exact
neighbor catalog and [accepted conductance](../research/physical-defect-trace/formal/Research/PhysicalAcceptedConductance.lean)
interfaces already used by the physical trace. The general result here is
the junction energy comparison; weighted center transport remains open.
