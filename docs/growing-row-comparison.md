# A one-token comparison with a growing number of large rows

11 October 2026. The parameter-wide argument and its row-DD copy lemma
have independent AI mathematical/source review. This is a restricted
ordinary-margin family result, without Lean formalization or outside human
review. Its exact finite fixture is supplemental evidence.

The explicit comparison gives inverse gap at most `29040A d^5` when
`s^2<=Ad`. The classical refinement below gives
`47916(C_Z+1)A^2d^4`, where `C_Z` is an unextracted universal constant
from Morris's zero-range theorem. Both dimensions may grow; the specified
margins and the one-token small row remain essential.

## Literal family and same-chain bound

Let R,b,U,L be integers with R>=2,b>=2,U>=R,L>=7. Put H=U-1,
m=R+1,n=2b, and choose integer J as follows:

    T=42(R-1)b(bH+1)+U,   S=T+bL,
    J>(R-1)S+1,
    Tlast=bH+bJ-1-(R-1)T.

Take rows (1,T,...,T,Tlast), with R-1 copies of T, and columns
(H,...,H,J,...,J), b of each. The totals match. There is one small row,
b small columns, R large rows, b large columns, and p=b(R+2) selected cells.
Every large row and column has STRICT ORIGINAL selected slack at every
balanced profile: the first R-1 rows have selected mass<=bH<T, the last has
Tlast>bH, and every large column has selected mass<=1<J. All large margins
are above U. Keep the [actual physical graph and trace](physical-defect-trace.md), ordinary
completion cardinalities, and literal reference accepted counts. With original
total M and d=10+(m+1)(n+1), use canonical large capacity M+dL+U+2.
It exceeds every full source residual total M+RbL+1 and excludes no dense
completion. There are no structural zeros, extra cell caps, inverse-factorial
weights or arbitrary supplied weight laws in this result.

The conclusion for every defect observable g is the RAW inequality

    Var_w,D(g) <=30 p U^2 [E_DD(g)+E_star(g)].                    (A)

For the SAME canonical rational trace, beta=1/[2(4p-3)], this gives

    K_rational<=60(4p-3)pU^2<=240p^2U^2.                       (B)

At the chosen shape-aware cutoff U=11ds, d=10+(R+2)(2b+1), s=R+2b-1,
(B) is at most 29040d^4s^2, and under the explicit aspect certificate
s^2<=Ad it is at most 29040A d^5. No clock is changed. A next-power-of-two
slot clock has at most twice these allowances; a legacy clock must use its
own beta. These are inverse-gap bounds, not encoded runtime or sampling
schedule certificates.

## Exact cap-vacuous dense counts

For a balanced center A, let ell_i be its selected mass in large row i.
The first R-1 dense row totals are S-ell_i, with 0<=ell_i<=bH. Each large
column's dense total is at least J+RL-1, strictly above (R-1)S. Therefore
choose the first R-1 rows independently as arbitrary weak compositions
among the b large columns; the forced last row is nonnegative in every
column. Its row total is automatically correct. Canonical source capacity
contains every such full completion.

Thus, with N_b(t)=binom(t+b-1,b-1),

    w_A=product_(i=1..R-1) N_b(S-ell_i),  W=N_b(S)^(R-1).

For a literal active LL inverse defect, its source dense row r and column c
are each reduced by one. At most one first-row total becomes S-ell_i-1;
when r is the last row no first total changes. The minimum column total is
then J+RL-2, still at least (R-1)S because integer J>(R-1)S+1 and L>=7.
The same independent-row counting argument remains valid. This is exact
full completion counting, not projected-weight equality or a claim that the
intrinsic repair is the actual accepted reference translation.

For 0<=q<=bH+1,

    N_b(S-q)/N_b(S)=product_(h=1..b-1) [1-q/(S+h)].

Across all R-1 factors there are (R-1)(b-1) terms. The finite product
inequality product(1-x_i)>=1-sum x_i and the choice of T show every relevant
balanced and LL count lies between delta W and W, delta=41/42. Counts for
the selected-crossing inverse defects in the G/J bridges equal their own
balanced center's weight exactly. No equality across different centers is
used.

All R*b LL crossings are original-active. Each has b donor small-column
choices and one receiver small-row choice. [Directed reverse half acceptance at L>=7](constant-padding.md)
and the intrinsic completed-repair injection give the safe load lower bound

    nu(A)>= (R b^2/2) w_A.

The [fixed-label completed repair injection](aggregate-incidence.md) gives nu(A)<=p(p-1)w_A<=p^2W. Both laws
include every positive defect and both ordered label directions.

## Classical complete-graph composition gap, with exact clock

For weak compositions eta of M among R colors, use rates
eta_i(1+eta_j) for each ordered i!=j. These rates are symmetric between
neighboring configurations, so the stationary count law is uniform.
For M>=1 the spectral gap is exactly R; M=0 has zero variance.

A self-contained mean-field proof uses M tagged particles. Each particle
mutates to EACH color at rate one (total mutation clock R), and each ordered
(target,source) particle pair copies the source color at rate one. Its count
projection has the displayed rates. Couple two tagged configurations by the
same mutation/copy events. Let D be their number of unequal tags. Copying
has zero drift on D: its sum of increments is sum_(a,b)(D_b-D_a)=0. Mutation
has drift -R D. Hence E[D_t]=exp(-Rt)D_0. Neighboring counts admit tagged
representations with D_0=1, and count graph distance is at most D_t.

For a nonconstant count eigenfunction, take an adjacent pair achieving its
maximum edge Lipschitz constant. Semigroup decay at its eigenvalue, combined
with this coupling, forces that eigenvalue to be at least R. The centered
linear function eta_i-M/R has eigenvalue R, proving equality. This argument
uses only finite reversible spectral theory and an explicitly stated clock.

The primary paper [Kim and Sau, *Spectral gap of the symmetric inclusion
process*, equations (1.1)–(1.2) and Corollary 1.2](https://arxiv.org/pdf/2303.16607v2)
independently confirms the inclusion/random-walk gap identity at alpha=1.
In its generator normalization, complete-graph conductances one give gap R;
conductances 1/R would instead give gap one. The gap identity is classical;
the finite coupling above proves the required special case directly. The
physical bridge comparison is its application here, rather than a new
composition-gap claim.

For a unit transfer, its rate eta_i(eta_j+1) is at most (M+1)^2/4. Therefore
raw uniform composition variance is at most (M+1)^2/(4R) times RAW UNIT-edge
energy. Our column totals are M=H or H-1, so each conditional product slice
has allowance at most U^2/(4R).

## Exact Polya restoration couples place means

Let M_R(t)=binom(t+R-1,R-1), the COLUMN composition count among R large
rows; it is different from the dense-row count N_b. The small row has one
token at a place P in its 2b selected cells. A large place slice has
Bbig=M_R(H)^b profiles, and a small-place j slice has
Bsmall=M_R(H-1)*M_R(H)^(b-1). Their ratio is

    Bsmall/Bbig=H/(H+R-1)>=1/2,

using U>=R. Other column compositions are independent and uniform.

To move from small place j to large place c, restore its missing column
particle to large row r with probability

    (eta_r+1)/(H+R-1),

where eta is a uniform composition of H-1. The target composition of H is
EXACTLY uniform: for target z, the total incoming probability is
sum_r z_r/[(H+R-1)M_R(H-1)]=1/M_R(H). Thus both coupled slice marginals are
uniform; no extra slice-variance or density-loss term is needed.

The resulting actual balanced comparison moves are

    G: transfer one in a small column between any two large rows,
    J: A->A-e_(0,j)+e_(0,c)+e_(r,j).

Every J target is source-feasible because all original large-line slacks
remain positive. Jensen bounds each squared place-mean contrast by its J
unit energy divided by Bsmall. The unit K_b,b place graph has raw variance
allowance 1/b; replacing its vertex masses by at most Bbig contributes
Bbig/Bsmall<=2. Product-slice tensorization therefore gives, for any center F,

    Var_unit,B(F)<= [U^2/(4R)] E_G,unit(F)+(2/b) E_J,unit(F).      (1)

All these are raw measures and unordered edge energies. Evaluating Var_nu
at the uniform balanced mean, then using nu<=p^2W and edge weights
mu_AB=min(w_A,w_B)>=delta W, yields

    Var_nu(F)<= [p^2U^2/(4R delta)] E_G,mu(F)
                  +[2p^2/(b delta)] E_J,mu(F).                  (2)

This carries the actual repair law, rather than normalizing away its mass.

## Actual G copies, J shared defects, and bounded charges

Let F_A be the w-weighted mean of g in rho's repair fiber, and
N=sum_d w_d(g_d-F_(rho(d)))^2. Exact decomposition is
Var_w,D(g)=N+Var_nu(F), and designated half acceptance gives N<=2E_star.

The actual row-DD construction is as follows. Orient a G move as
B=A-e_(r,j)+e_(rprime,j), with A_(r,j)>0. For each receiver s=(i,j),
i=0,...,R, and donor pair t=(r,k),tprime=(rprime,kprime), k,kprime
in the b small columns, use

    d_A: X=A+e_t-e_(r,j), Q=A+e_s-e_(r,j),
    d_B: Xprime=A-e_(r,j)+e_tprime, Qprime=Q.

Exclude s=t or s=tprime, the cases making an endpoint balanced. Selected
entries of balanced A and B are below U, so all inverse +1 entries fit.
Each endpoint preserves its repaired center's row-X and column-Q selected
totals; its dense residual margins and full completion set therefore equal
those of that center. The two X views differ by one literal unit exchange,
and Q is unchanged, so each pair is an actual DD edge. Actual directed half
acceptance gives accepted conductance at least mu_AB/2.

For receiver rows other than r,rprime there are b^2 copies; at each of the
two exceptional rows the diagonal exclusion leaves b(b-1). Hence the exact
number of copies is

    Lrow=(R-1)b^2+2b(b-1)=b((R+1)b-2)>=R b^2.

The unique ordered endpoint labels recover the receiver and two donors,
and their repairs recover the balanced G move. Thus copies are distinct
within each move and different unordered moves have disjoint DD edge sets.
An endpoint defect determines its receiver column j, donor row r, donor
column k and repair A. It can appear in at most R-1 row-transfer moves,
with at most b partner copies in each. Its total pair charge is therefore
at most b(R-1). Averaging the three-term squared center contrast over the
Lrow copies yields

    E_G,mu(F)<= (6/Lrow) E_DD,G(g)
                         +[3b(R-1)/Lrow] N.                    (3)

The source and target inverse weights are exactly w_A,w_B, not one common
constant. The conductance bound is the actual directed half acceptance.

For a J edge, the actual shared defect is

    d: X=A-e_(0,j)+e_(0,c), Q=A-e_(0,j)+e_(r,j).

Its designated repair is A, its dense residual margins equal A's, and its
weight is w_A. The added A-d repair edge has zero residual translation and
c_Ad=w_A. It is also adjacent to B by a literal doubled-coordinate exchange,
with actual c_Bd>=mu_AB/2. Different J moves have different shared defects.

At a large-place B there are at most Rb incoming J moves. Since
nu(B)>=Rb^2 w_B/2, their incoming mu sum divided by nu(B) is at most 2/b.
Expand F_A-F_B through g_d and harmonic H_B, using the three-term square
bound, the actual accepted star energy and
nu(B)(F_B-H_B)^2<=2E_star,B. This gives

    E_J,mu(F)<=3N_small +(6+12/b)E_star,large
               <=(6+12/b)E_star<=12E_star.                     (4)

The small/large subscripts are PLACE slices, not a new state law or clock.
The incoming acceptance is not replaced by the intrinsic LL count map.

## Safe constant and exact normalization

Insert (3),(4) into (2), then add N. Because p=b(R+2), Lrow>=Rb^2 and R>=2,

    [p^2U^2/(4R delta)]*(6/Lrow) <=(6/delta) U^2,
    [p^2U^2/(4R delta)]*[3b(R-1)/Lrow]
                                      <=[3/(2delta)]pU^2.

Also R+2<=R^2<=U^2, so the J coefficient after (4) is at most
(24/delta)pU^2. Applying N<=2E_star leaves

    Var_w,D(g) <=(6/delta)U^2 E_DD,G
                    +[2+(27/delta)pU^2]E_star
                 <=30pU^2(E_DD+E_star),

since delta=41/42 and pU^2>=1. This proves the reviewed raw inequality (A). It is mathematical/source
review, without Lean verification.

For the unchanged actual trace, Var_chain=Var_w,D/Z_D and
E_chain=beta(E_DD+E_star)/Z_D, with positive defect mass. The LL inverse states
supply nonempty D in this family. Thus the same-chain coefficient is
30pU^2/beta, giving (B). At U=11ds use p<=d for 29040d^4s^2. If s^2<=Ad,
this is the stated integer-power 29040A d^5 bound.

The family is not restricted to R=2: R and b may grow together. Its very
large ordinary margins, cap-vacuous product dense counts, one-token small
row, and complete-graph conditional compositions are substantive hypotheses.
No extension to all masks, arbitrary margin weights, or higher h is asserted.

## Classical zero-range refinement

[Morris, Theorem 3](https://arxiv.org/pdf/math/0405161) supplies a sharper
asymptotic composition comparison. The complete-graph constant-rate
zero-range process attempts each directed transfer from an occupied color
at rate `1/(R-1)` and has uniform composition law. Its relaxation time is
at most `C_Z(1+M/R)^2`, for a universal constant `C_Z` that is not numerically
extracted here. Our raw unit-edge generator runs `R-1` times faster, so
its variance allowance for totals at most `H` is

    Gamma=C_Z(1+H/R)^2/(R-1)<=8 C_Z U^2/R^3.

The last inequality uses `U>=R>=2`; a zero-particle slice has zero variance
separately. This rescales the auxiliary comparison only. The physical
trace keeps exactly its previous proposal clock.

Replace `U^2/(4R)` in (1) and (2) by Gamma. The dense counts, Polya
restoration, G copies, J shared defects and repair law are unchanged.
Before simplifying, the coefficients of the raw defect energies are

    DD:   6p^2 Gamma/(delta Lrow),
    star: 2+6p^2 Gamma b(R-1)/(delta Lrow)+24p^2/(b delta).

Use `Lrow>=Rb^2`, `p=b(R+2)` and

    2R^3-(R+2)^2(R-1)=(R-2)^2(R+1)>=0.

The DD coefficient is at most `192 C_Z U^2/(delta R^2)`; the G contribution
to the star coefficient is at most `96 C_Z bU^2/(delta R)`. The J
contribution remains at most `96bR^2/delta`. Since `delta=41/42`,
`bR>=4` and `bR^2>=8`, both full coefficients are at most

    99b(C_Z U^2/R+R^2).

In particular the additive two is absorbed because
`99-96/delta=27/41>1/4`. Multiplying by the SAME physical inverse clock
`2(4p-3)<=16Rb` gives

    K_rational<=1584b^2(C_Z U^2+R^3).                          (C)

The `R^3` term is the place-comparison contribution and must be retained
for freely chosen `U`. At `U=11ds`, however, `d>=4R` and `s>=R` imply
`U>=44R^2`, hence `R^3<=U^2`. Under `s^2<=Ad`, also `4b^2<=s^2`, giving

    b^2 U^2<=(121/4)A^2d^4,
    K_rational<=47916(C_Z+1)A^2d^4.                           (D)

This is a reviewed asymptotic `O(d^4)` allowance at fixed aspect, with an
unextracted constant. The explicit numerical `29040A d^5` allowance remains
available; neither a finite-instance crossover nor an executable numerical
schedule follows from (D) alone. The structured margins make the comparison analyzable; this result chiefly
identifies losses in the generic defect-chain proof. It establishes no
practical speed advantage.
The classical theorem and this application are not Lean-formalized here.

## Reproducible finite evidence and review

The [focused checker](../experiments/growing_row_comparison.py) reuses the
[five-family catalog](../src/contingency115/general_neighbors.py),
[physical state and literal reference translation](../src/contingency115/ideal_chain.py),
repository bounded compositions and the published thin variance helper. It
does not create a separate physical-chain implementation.

    PYTHONDONTWRITEBYTECODE=1 python3 experiments/growing_row_comparison.py \
      --output reports/growing-row-comparison.json

The [saved report](../reports/growing-row-comparison.json) retains the requested
R=3,b=2,U=3,L=7 fixture: 108 balanced profiles, 4,194 defects, 5,706 DB
incidences, 306 grid-center edges and 3,672 distinct DD bridges, with exactly
12 bridges per grid edge. Endpoint-list and pair charges are at most 2 and 4.
There are 216 distinct shared jump defects, with maximum incoming degree 4.
The exact Polya restoration has target probability 1/6 on each of six
column compositions. Four chosen dense contexts are counted directly,
including one DD reference-translation acceptance in both directions.
These direct counts match the cap-vacuous formulas.

Four rational observables check variance decomposition, actual star noise,
unit and weighted center comparisons, G/J transport inequalities and
raw30pU^2 against the star and chosen DD bridge subset. This is not an
all-observable finite matrix certificate, complete DD adjacency audit,
all-state dense-fiber enumeration or runtime benchmark. The parameter-wide
conclusion rests on the displayed mathematical proof. The
[source-review record](growing-row-comparison-review.md) binds its reviewed
sources and their public adaptation, including a separate review of the
Morris refinement. The finite fixture checks the explicit comparison; it
does not extract or numerically validate the classical constant.
