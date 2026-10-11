# Effective small-mask width on the unchanged weighted physical graph

The subsequent [shape-aware move count](shape-aware-defect.md) improves this same-width allowance from `32p^4V^4` to `16p^4V^4` rational, and from `64p^4V^4` to `32p^4V^4` dyadic. The graph/width argument and scalar Lean receipt below are unchanged; their earlier valid normalization is retained for reproducibility.

11 October 2026. Mathematical derivation reviewed by a separate AI agent, with
exact finite checks and a [compiled scalar coefficient](../research/effective-width/).
The graph equivalence and complete trace theorem still need physical Lean
assembly; no measured speedup or new uniform worst-case dimension exponent is claimed.

## Result

For the actual unrestricted source graph at cutoff U>=2 and padding L, let
S={(i,j):min(r_i,c_j)<U}, p=|S|. If S is nonempty define

    V=max(2, 1+max_{(i,j) in S} min(r_i,c_j)).

Then V<=U and the weighted graph, source accepted conductances, and all output
joint fibers are unchanged up to a canonical complement-coordinate encoding
map when the proof cutoff/capacity is reduced from U to V. Consequently the
existing certified refined physical variance coefficient can be bounded by

    C(p,V)<=p^3 V^4  (p>=2,V>=2),

and the general accepted-conductance defect trace derived previously satisfies

    K <= 2(16p-14) C(p,V) <= 32 p^4 V^4.

For the EXISTING full physical chain, whose dyadic proposal depends only on d,
the same pullback also gives reference/selected K<=128 d^2 p^3 V^4 and unit
K<=64 d^2 p^3 V^4 via the existing C/beta or 2C/beta formulas. This does not
require the new trace kernel, although the capacity equivalence still needs
formal assembly to become a compiled bound.

The dyadic TRACE proposal version has at most twice the displayed trace coefficient. The trace still
requires D nonempty. Zero-margin graph identity is allowed, but the positive-
margin output correction retains its existing scope.

This is an instance-dependent result on the SAME chain, not insertion of
variable capacities into an old formula. In particular, at original ideal
U=5d^3, L=3d, the bound is at most 20000 p^4 d^12. If p=O(d^theta) and V=O(d^sigma),
the resulting gap allowance is O(d^(4theta+4sigma)). A weighted rectangular
family with m,n=Theta(sqrt(d)) and O(1) small rows/columns has p=O(sqrt(d)),
so even V<=5d^3 yields O(d14). If those small margins are bounded, V=O(1)
and the same genuine nonempty-completion family instead has O(d2).

## 1. Actual state bounds justify the capacity change

Use x for the row view and q for the column view. A positive physical
state/completion pair satisfies the source ordinary, unpadded inequalities

    sum_{small cells in row i} x_ij <= r_i,
    sum_{small cells in column j} q_ij <= c_j.

Therefore x_ij<=r_i and q_ij<=c_j. Balance or a single ordered defect implies
|x_ij-q_ij|<=1. For every small cell,

    x_ij,q_ij <= min(r_i,c_j)+1 =: B_ij <= V.

The +1 is necessary: actual fixtures attain q=3 or x=3 when min(r_i,c_j)=2.
At balance, the stronger bound x=q<=min(r_i,c_j) holds.

These facts come from actual source CompletionFibre inequalities, not from an
assumed ordinary balanced-table bound on defects. The definitions are in
.upstream/openai-math/lean/OAI/Combinatorics/ContingencyTables/Sampling/
PhysicalCompletionFibres.lean: CompletionFibre and SmallGraphProfiles.lean:
Balanced/SingleDefect.

## 2. The small CELL mask is identical

Every selected cell has min(r_i,c_j)<=V-1, so is selected at V. Every excluded
cell has min(r_i,c_j)>=U>=V, so remains excluded. Thus S(U)=S(V).

If the original large rectangle is nonempty, both cutoff-defined large-side
sets are identical too: an old large column has margin >=U, so every old small
row margin is seen as min(r_i,c_j) at one selected cell and is <V. Similarly
every old small column is <V. Old large margins stay >=U>=V.

In the UNIT/empty-rectangle branch, individual cutoff-defined large-row or
large-column sets can change. Example: U=9, rows(2,2), columns(3,1), V=3 adds
a cutoff-large column while the large-row set remains empty. The large CELL
mask remains empty and the physical graph remains identical. Do not claim
identical compressed residual tuple shapes in this branch. Use full supported
residual tables or the unique empty completion for the equivalence.

## 3. Canonical profile map and edge preservation

For the original doubled profile z=(x,U-q), map it to z'=(x,V-q). This leaves
x,q unchanged and translates every complement coordinate by a fixed constant.
The bound in section 1 makes the new complement nonnegative and <=V. Conversely
any new positive state yields an old state by the reverse encoding, since its
views are <=V<=U and its residual constraints are the same.

Balance/single-defect patterns are preserved: occupancies shift from U to V
at each cell while the difference x-q remains unchanged. A doubled-coordinate
unit exchange remains EXACTLY the same coordinate difference after translation.
Both endpoints are positive states under the equivalence, so physical exchange
edges correspond in both directions. There are no newly created feasible edges.

The designated repair depends on defect labels and crossing
(row(t),col(s)), both preserved by the map. In views it is x-e_t+e_cross when
the crossing is small, or x-e_t when the crossing is large. The small mask
is unchanged. Thus repair edges correspond as well, including edge overlaps.
The full graph is the same union of exchange and repair edges.

The finer heterogeneous encoding (x,B_ij-q) is also a safe state/edge encoding
map, provided one uses the corresponding variable-capacity balance/defect
predicate. However the existing localized physical exposure theorem requires
UNIFORM small capacity. It does not yield a sum-of-cell-width coefficient merely
from this finer map. The uniform effective V is what permits reuse of the
existing certified theorem.

## 4. Completion weights and accepted conductances are EXACTLY preserved

Because x,q and the small CELL mask are unchanged, full padded residuals are
unchanged:

    R_i=r_i-sum_small_row(x)+rowLargeCount(S,i)*L,
    P_j=c_j-sum_small_column(q)+columnLargeCount(S,j)*L.

The full supported residual completion rectangle and its margins are identical.
Large source capacities at U and V are respectively

    M+dL+U+2 and M+dL+V+2,  M=sum_i r_i.

Either exceeds every possible dense entry: the dense residual total is at most
M+|large cells|L<=M+dL. Thus reducing the paper large cap removes NO completion.
This is exactly the source capacity-excludes-none premise; no bounded-cell
completion law or external weights are introduced. See CompletionCounts.
paperCapacity/paper_capacity_excludes_none and PhysicalResidualMargins.
physical_weight_completions in the upstream source.

The joint completion sets therefore agree, not just their counts. Weights w(z)
are equal. In a nonempty rectangle choose the same reference row/column, whose
cutoff-side sets are identical by section 2. Reference rows/columns are
reindexings of those same residual margins; their signed between-star
translation is the same. Its accepted subset of uniform source completions is
therefore the same, so acceptedCount c_xy is exactly preserved in BOTH directions.
In the empty branch the completion is unique and every valid proposal accepts.

Weighted variance, min-weight graph energy, accepted-conductance graph energy,
normalized full-chain law, and weighted harmonic defect trace all pull back
unchanged. The general trace kernel can retain the original U in its actual
encoding and use the improved V bound only in its proof/schedule.

The designated completion-retaining terminal repair also preserves the dense
completion (small crossing) or adds one to the same dense cell (large crossing).
Its output fibers and unpadding test are unchanged. Individual small-side
counts a,b used by a UNIT-branch lower bound may be represented differently at
V; use the original known unit formula there. For a nonempty rectangle a,b and
the general joint load D0+abuv are identical.

## 5. Source hypotheses: V>=2, not V>=2L

formal/Math115/PhysicalRepairRefinement.lean: state_variance_refined takes ONLY
2<=V (besides finite types/order), with the actual paper capacity. Its generic
hcap is discharged by paper_residual_capacity for arbitrary L and cutoff.
The refined accepted completion comparison needs L>=3e (sufficiently L>=3d)
and source capacity-excludes-none. Neither theorem assumes 2L<=V.

IdealOracleScales.threshold_at_least_twice_padding proves 2L<=U for the old
ideal cutoff. That arithmetic is not a premise of the parameterized variance
or shape-aware acceptance theorem. The width reduction can have V<2L, and the
exact weighted U4->V2,L78 fixture does.

For completion accuracy/cost, retain the EXISTING original-U completion
family at U=5d^3,L=3d and transport only the gap certificate. Its residuals and
accepted subsets are unchanged; no new completion interface at V is needed.
The already compiled dilation/rounding completion and existing encoded sampler
remain proved. NEW trace finite-word composition and encoded integration remain
separate obligations.

Likewise retain the original ideal P<=2N padding proof. The large CELL mask and
actual padded margins are unchanged, and original marked large margins still
exceed 5d^3. Do not replace its ideal large-margin premise by the much smaller V.

## 6. Scalar coefficient C(p,V)<=p^3 V^4

Let

    CT=V(V+1)/2 * [2+(p-1)(V+1)^2/2],
    C=CT+(sqrt(p^2 CT)+1)^2
      =(1+p^2)CT+2p sqrt(CT)+1.

For V>=2, V(V+1)/2<=3V^2/4 and (V+1)^2<=9V^2/4, giving

    CT<=3V^2/2+(27/32)(p-1)V^4
      <=[(27p-15)/32]V^4 = A V^4.

For p>=3, A<=p^2, so sqrt(CT)<=pV^2. Since V^2<=V^4/4 and 1<=V^4/16,

    C <= [(1+p^2)A+p^2/2+1/16] V^4 <= p^3 V^4.

The last coefficient inequality is exactly

    5p^3-p^2-27p+13 >=0.

For t=p-3>=0 its left side is 58+102t+44t^2+5t^3, so is positive.
For p=2, A=39/32<=25/16, sqrt(CT)<=5V^2/4. Hence

    C<= [5*(39/32)+5/4+1/16]V^4=(237/32)V^4 <8V^4=p^3V^4.

The exact p-based inequality avoids replacing p by d. The earlier general
trace normalization is 2C/beta, beta^-1=16p-14, yielding K<=32p^4V^4.
No state-normalizer or weight perturbation factor appears.

## 7. Limits and a degree obstruction

This does NOT improve the uniform worst-case d16 envelope: V can equal the
original ideal U, and p can be Theta(d). Example families with selected small
margins U-1 have V=U. Nor does the heterogeneous encoding change the actual
neighbors, so it cannot by itself improve proposal normalization.

There are genuine mixed-block instances with V=2 and DD degree Theta(p).
Take m=n=N even, a=b=N/2 small rows/columns of margin1, and the other rows and
columns of margin U=5d^3. Let V=2 and L=3d. A balanced small profile puts one unit
on each matched small-row/small-column diagonal and zero on its LS/SL cells.
Choose v on that SS diagonal, s in a large row of column(v), t in row(v) of a
large column; form x=A+e_t-e_v, q=A+e_s-e_v.

This defect has exactly

    (n-1)+(m-1)+(a*(n-b)-1)+((m-a)*b-1)
      =m+n+a*(n-b)+(m-a)*b-4

DD neighbors: pure x redistributions within its fixed small row; pure q
redistributions within its fixed small column; and the two mixed-increase
cancellation families. All are positive feasible source states. With a=b=N/2,
the count is 2N+N^2/2-4=Theta(p), p=3N^2/4. Already at N=6 it is26, exceeding the unit proposal degree bound
2(m+n-2)=20; at N=8 it is44 versus28. Direct doubled-exchange enumeration verifies
the count at N=4,6,8,10.

At L=3d, existing directed acceptance gives c_xy>=w(x)/2 for all these edges.
Thus the accepted trace's off-diagonal row rate is at least DDdegree/2=Theta(p).
Any common scalar normalization of these SAME conductances that is half-lazy
needs beta=O(1/p). Replacing p by m+n in general is therefore impossible by
capacity trimming or better slot enumeration alone. This is an obstruction to
that normalization step, not a lower bound on every possible sampling method.

## Evidence and reproduction

[effective_width.py](../experiments/effective_width.py) compares the actual
finite physical builder at U and V across seven fixtures. States, cell mask,
completions, neighbors, accepted counts, matrices, stationary law, original
stationary output law, and successful joint repair fibers agree exactly.
Weighted fixtures include completion counts 159/160/161 at V=2<2L, and four
distinct weights at U=8, V=3. A zero-total case keeps the empty defect branch
explicit. Entries attain the required min-margin-plus-one boundary.

The same script checks the degree obstruction at N=4,6,8,10 by enumerating
local exchanges and checking unrestricted residual feasibility, without
counting or enumerating completions. These fixtures use the original ideal
U=5d^3, L=3d and effective V=2. The [saved report](../reports/effective-width.json)
retains every input and count.

```sh
python3 experiments/effective_width.py --output .local/reports/effective-width.json
```

The exact scalar inequality in Section 6 is also freshly compiled in the
[effective-width packet](../research/effective-width/), with its own environment
audit. That receipt verifies the numerical coefficient, not the unassembled
physical graph equivalence or weighted trace. Historical default-target and
Comparator scopes are unchanged.
