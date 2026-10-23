# Parallel DD energy in a thin mixed family

11 October 2026. This family theorem has independent mathematical review
and an exact finite check; its physical inequality has not been assembled
in Lean. The unrestricted general exponent remains 8.
It uses literal physical edges, actual completion/accepted counts and the
same defect-trace normalization. No clocks or successful-move conditions
are changed.

## Exact scope and raw conclusion

Take b>=2,U>=3,L>=7,C=b,H=U-1 and define margins

    T1=42 C(bH+1)+U, J=T1+CL+1,
    T2=bH+CJ-1-T1,
    rows=(1,T1,T2), columns=(H repeated b, J repeated C).

The mask has one small row, b small columns, two large rows and C=b large
columns; p=4b. Use the [actual physical graph and rational defect trace](physical-defect-trace.md),
ordinary completion weights, and selected capacity U. With original total M
and d=10+(m+1)(n+1), use canonical large capacity M+dL+U+2. It dominates
every full ordinary source completion: the padded full total is at most
M+2bL+1<=M+dL+1. Thus all weights below are actual ordinary completion
cardinalities under the source cap, rather than a supplied weight oracle.
No structural zeros,
additional cell caps, factorial-weight law or arbitrary oracle law is covered.
Let D be ALL positive physical defects, w their hard-completion counts,
and Etrace=E_star+E_DD the raw unordered accepted trace energy. For EVERY
real defect observable g,

    Var_w,D(g) <=100 b U^2 Etrace(g).

For any actual physical proposal beta, the same-chain defect trace has
normalized inverse-gap allowance 100bU^2/beta. In particular the frozen
rational clock beta=1/[2Q],Q=4p-3 gives

    K_rational<=200 Q b U^2<=200p^2U^2.

The corresponding next-power-of-two slot clock gives at most double.
At U=11d(2b+1),d=8b+14, this yields the conservative family bound
1513d^6 rational or 3026d^6 dyadic: p<d/2 and
2b+1=(d-10)/4<d/2 imply 200p^2U^2<(3025/2)d^6<=1513d^6.
The exact 200QbU^2 is sharper. This is not a theorem for every 3-by-2b input.
The legacy d^2 proposal clock must instead use its own beta. There is no
claim about other masks, algorithm runtime, or full-sampler implementation.

## Counts, designated partition and star noise

Every balanced selected profile has one first-row entry 1 at a place P in 0..2b-1.
Each small column splits H minus that first-row entry between large rows.
All large selected budgets remain slack. Put Rbase=T1+CL,
W=binom(Rbase+C-1,C-1),delta=41/42. Cap-vacuous first dense-row compositions,
including LL inverse defects at dense total r-1, give

    delta W<=w_A<=W

for all balanced profiles and every defect in the designated partition.
Here is the complete count argument. If y is large row 1 selected mass,
its padded dense total is r=Rbase-y. Every large-column residual exceeds
Rbase, so all weak compositions of r into C entries fit; the second dense
row is then forced and nonnegative. Thus w_A=binom(r+C-1,C-1). For any
designated inverse defect the first dense row total lies in
[Rbase-bH-1,Rbase] and every large-column residual is at least Rbase,
so the same formula applies. For k<=bH+1, the ratio to W is

    product_(q=1..C-1) [1-k/(Rbase+q)]
      >=1-(C-1)k/(Rbase+1)>=41/42.

The product inequality follows by induction from (1-x)(1-y)>=1-x-y
for x,y in [0,1]. This proves the uniform count bounds, including LL sources.

All original large-line slacks are positive. For any large row r and
large column c, each of the b donor columns in row r and the unique
small-row receiver in column c produces an inverse defect
x=A+e_t,q=A+e_s. Its dense residual row r and column c are reduced by 1.
The intrinsic map Z->Z+e_(r,c) bijects its source completions with A
completions whose crossing is positive. This count map is not in general
the literal reference-star acceptance translation. Actual directed
[half acceptance at L>=7](constant-padding.md) implies its source count
is at least w_A/2, since the accepted count out of A is at least w_A/2
and at most the defect source count. Summing over 2b^2 distinct ordered
labels gives nu(A)>= b^2w_A; the weaker b^2w_A/2 is enough below.

The fixed-label completed repair injection, with explicit
[full-table LL reconstruction](aggregate-incidence.md), gives

    nu(A)=sum_(rho(d)=A) w_d <=p(p-1)w_A<16b^2 w_A.

Let F_A be the w-weighted mean of g in the deterministic repair fiber.
Set N= sum_A sum_(rho(d)=A) w_d(g_d-F_A)^2. Exact variance decomposition:

    Var_w,D(g)=N+Var_nu(F).

Let H_A be the accepted-incidence harmonic balanced mean used in the actual
Schur star energy. Directed half acceptance on designated repair edges
implies

    N <=sum_A sum_(rho(d)=A) w_d(g_d-H_A)^2 <=2 E_star.

Also nu(A)(F_A-H_A)^2<=2E_star,A. This is not an assumption that the
literal LL repair accepts every completion. LL counting bijections and
reference-star acceptance translations are kept distinct.

## Elementary balanced-profile comparison graph

Use two kinds of balanced center edges solely as an auxiliary comparison:

G: keep P fixed and transfer1 in a small column between the large rows;
J: move P from small column j to large column c, and add1 in that small
column to either large row r, restoring its original column total.

The G moves are product-grid edges. A large-place slice has U^b profiles;
a small-place slice has H U^(b-1). For ANY real balanced function F,

    Var_unit,B(F)<= (U^2/2) E_G,unit(F) + [3/(2b)] E_J,unit(F).       (1)

Here is a full elementary proof, including slice-mean comparisons. Uniform
path variance on q points is at most q^2/8 times its unit-edge energy:
Cauchy-Schwarz in the pair-variance formula charges edge k by
k(q-k)/2<=q^2/8. Tensorization gives U^2/8 for every conditional product
slice. Let m_j,m_c be small/large-place slice means. Couple a uniform small
slice j to large slice c by choosing either restoration row r uniformly.
The changed coordinate has target mass1/(2H) at endpoints and1/H inside,
whose density relative to the uniform U-point coordinate is at most
U/H<=3/2. Thus

    (m_j-m_c)^2 <=E_J,(j,c)/[H U^(b-1)]
                      +3 Var_unit,large-c(F)/U^b.

The complete bipartite K_b,b place graph has unit variance coefficient1/b:
its energy is b times each side's within-side variance plus b^2 times
the side-mean contrast. Actual slice masses are at most U^b. Summing the
last display and using that coefficient bounds the place-mean variance by
[U/(bH)]E_J+3 sum_large-c Var_unit,c. Adding conditional variances gives
at most4 times the conditional term and U/(bH)<=3/(2b), proving (1).

Give each comparison edge weight w_e=min(w_A,w_B)>=delta W. Evaluating
Var_nu at the unit-balanced mean and using nu<=16b^2 w_A<=16b^2W proves

    Var_nu(F) <= [8b^2U^2/delta] E_G,w(F)
                      +[24b/delta] E_J,w(F).                    (2)

## b^2 parallel actual DD copies of every G edge

Orient A->B in a small column j with A_(1,j)>0 and
B=A-e_(1,j)+e_(2,j). Fix receiver s=(0,j). For EACH donor column k and k',
let t=(1,k),t'=(2,k'), v=(1,j),v'=(2,j). Define

    d_A: x=A+e_t-e_v, q=A+e_s-e_v,
    d_B: x'=B+e_t'-e_v'=A-e_v+e_t', q'=q.

These are actual defects with rho(d_A)=A,rho(d_B)=B, weights w_A,w_B
respectively. The small-row q entry is at most2<=U and current small-column
positivity ensures the subtracted crossing entries are valid. Their X views
differ by ONE unit exchange, so they are literal DD neighbors. Directed
half acceptance implies accepted conductance c>=w_e/2. Every G edge has
b source and b target defects, hence b^2 such DD bridges.

Distinct G edges charge distinct DD edges. Moreover each selected endpoint
defect occurs in at most ONE G edge's b-element endpoint list: its receiver
column j and negative donor row determine the unique grid direction and
repair A. Let E_DD,G be their actual accepted energy. Jensen followed by
the three-term square bound gives

    E_G,w(F) <=[6/b^2] E_DD,G(g)+[3/b] N.                       (3)

The factor3/b in the noise term follows from averaging the b^2 bridges:
each endpoint defect occurs b times in the pair average, and w_e<=w_A,w_B.
The global endpoint-list disjointness gives the single N charge. No
completion equality across DIFFERENT grid centers is assumed.

## Actual shared defects for every J edge

Let A have its first-row entry 1 in small column j. For each large column c and
large row r, the J target is

    B=A-e_(0,j)+e_(0,c)+e_(r,j).

The physical defect

    d: x=A-e_(0,j)+e_(0,c), q=A-e_(0,j)+e_(r,j)

has designated repair A, unchanged dense residual margins and weight w_A.
It is adjacent to B by the literal doubled exchange increasing x_(r,j)
and q_(0,c). Thus it is a shared defect with DB accepted conductances
c_Ad=w_A and c_Bd>=w_e/2. The latter uses the ACTUAL reference-star
half-acceptance theorem; its intrinsic completion counting map is not
substituted for the literal translation. Different J edges have different d.

For each B in a large-place slice there are at most 2b incoming J edges.
Therefore sum_incident w_e<=2b w_B and, using nu(B)>=b^2w_B/2,
sum_incident w_e/nu(B)<=4/b. Expanding a center contrast through g_d and
H_B, with a three-term square bound, yields

    E_J,w(F) <=3[N_small +2 E_star,large +(8/b)E_star,large]
             <=6 E_star,small +(6+24/b)E_star,large
             <=(6+24/b)E_star.                                (4)

The first noise sum is over distinct designated defects at small-place
centers and is bounded by N_small<=2E_star,small. The second uses
w_e<=2c_Bd. The third uses
nu(B)(F_B-H_B)^2<=2E_star,B and the incoming-weight ratio above.
No DD or star edge is normalized by a successful-move probability.

## Combine with explicit safe constants

Insert (3),(4) in (2), then use N<=2E_star:

    Var_w,D(g)
      <= [48U^2/delta] E_DD,G
        +[2+(48bU^2+144b+576)/delta] E_star.

For b>=2,U>=3,144b<=16bU^2 and576<=32bU^2. Also
1+96/delta=4073/41<100. Since2<=bU^2, the last coefficient is at most
100bU^2, and the DD coefficient is smaller. Retaining all other actual
DD edges proves the stated full raw trace inequality.

This identifies a real mechanism: the p^2 repair-law load is canceled by
b^2 parallel DD bridges within product slices, while complete bipartite
place geometry supplies a b spectral factor for the remaining center
changes. The star's own fiber mixing alone was insufficient. Extension
to arbitrary masks/weights requires a corresponding actual center graph
and bounded-charge bridges; near-uniform dense counts and the first-row
single token are substantive hypotheses here.

## Physical sources and exact check

The [graph reference](../src/contingency115/ideal_chain.py) implements the
actual doubled exchanges, designated repair and reference-star translation.
The [five-family catalog](../src/contingency115/general_neighbors.py) enumerates
exact DB incidences without dense-state enumeration.
[Constant-padding](constant-padding.md) supplies directed half acceptance;
[physical-defect-trace](physical-defect-trace.md) fixes the Schur energy and
clock. The present parallel center comparison is reviewed mathematics,
not a new Lean closure or an encoded sampler implementation. This is
independent AI mathematical and source review, without a human review claim.
See the [source review](thin-parallel-comparison-review.md).

    PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=src python3 experiments/thin_parallel_comparison.py \
      --output reports/thin-parallel-comparison.json

The [saved finite report](../reports/thin-parallel-comparison.json) is one
rescaled b=2,U=3,L=7 fixture. It checks 30 balanced profiles, 806 defects,
1,024 DB incidences, 38 grid center edges, 152 parallel DD edges and 48 shared
jump defects. Accepted counts use the literal reference-star translation
and exact cap-vacuous ordinary counts. Four observables check the variance
identity and intermediate energy inequalities. These are finite certificates;
the arbitrary-parameter derivation above establishes the family theorem.
No dense completion enumeration, eigensolver, machine-runtime benchmark or
physical-gap lower bound is inferred from the fixture.
