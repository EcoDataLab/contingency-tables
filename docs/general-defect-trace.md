# General weighted defect trace: mathematical derivation

The [shape-aware refinement](shape-aware-defect.md) now halves the general allowance below to `10000d^16` rational / `20000d^16` dyadic. Its bounded transition implements the actual compact proposals, completion calls and capped star exits. The derivation below retains the earlier valid, looser normalization and its original evidence. Full physical Lean and encoded integration remain open.

The later [effective-width result](effective-defect-width.md) sharpens this
same chain's instance-dependent inverse-gap allowance to `32p^4V^4`, or twice
that for the dyadic proposal. It does not lower the uniform worst-case `d^16`
exponent. The scalar coefficient is compiled; physical assembly remains open.

11 October 2026. A mathematical derivation reviewed by a separate AI agent,
with exact finite checks. The changed accepted-conductance trace has inverse gap
at most **20000d^16** at the ideal scales, including nonempty completion blocks.
Its physical geometry and trace have not been assembled into a Lean theorem or
installed in the compiled sampler.

## Scope and existing inputs

Use unrestricted ordinary equal-total nonnegative integer margins, m,n>=2,
U>=2, source small cells S={(i,j): r_i<U or c_j<U}, p=|S|, source capacities,
and source padding L. Let w(z)>0 be the actual completion-fiber count. Retain
only positive physical states. Partition these into balanced B (x=q) and defects
D (q-x=e_s-e_t, s!=t in S). Assume D is nonempty; then p>=2. If D is empty,
this defect chain is undefined and a separate direct/completion branch is
needed. For the convenient local sampler below, the source large capacity
must dominate the full padded residual total, as the existing paper capacity
already does. No additional cell bounds, structural zeros, or arbitrary
weights are covered.

The already checked full-variance input is the UNNORMALIZED inequality

    Var_w,full(H) <= C E_min(H),  C <= d^3 U^4,
    d=10+(m+1)(n+1),  p<=d,

where E_min sums min(w(x),w(y)) times squared contrasts over unordered actual
physical graph edges. See [PhysicalRepairRefinement.lean](../formal/Math115/PhysicalRepairRefinement.lean) and
[ReducedAllSmallChain.lean](../formal/Math115/ReducedAllSmallChain.lean): graphEnergy_empty checks the unit
specialization and ordered-sum/2 normalization.

For the actual source completion translation, write c_xy for acceptedCount.
It is symmetric by the source translate/backward bijection; 0<=c_xy<=w(x).
The existing theorem
[ReferenceEdgeAcceptance.lean](../formal/Math115/ReferenceEdgeAcceptance.lean): reference_edge_acceptance_reduced
proves, on EVERY DIRECTED valid physical edge,

    c_xy >= w(x)/2

when L >= 3e, e=(number large rows-1)(number large columns-1), and the source
capacity premise holds. This is stronger than merely c_xy>=min(w(x),w(y))/2.
It supplies E_min <= 2 E_c and a >=1/2 per-neighbor completion acceptance
probability. L=3d is sufficient. A diagnostic fixture with smaller L checks
geometry but does NOT by itself check this acceptance premise.

## No balanced-to-balanced edges

Every small cell has either a small row or a small column. The corresponding
x row margin or q column margin is fixed, because that entire row or column
contains small cells and no large completion entry. This holds for defects too.

At balance, a unit exchange of two x coordinates or of two q coordinates
cannot remain balanced: the other view stays unchanged. A mixed doubled
exchange can remain balanced only if its two view coordinates belong to the
same cell. Such a move increments or decrements x and q together there, and
violates its fixed small-row or small-column margin. Hence no physical exchange
joins two balanced states. Added designated repair edges always join a defect
to a balanced state. Thus the induced graph on B has no edges.

Every balanced small entry is STRICTLY below U, since it lies in a fixed small
row or small column. Incrementing it once can reach U but never U+1. This fact
is used in the balanced neighbor sampler.

## Defect full degree is at most 8p-7

In doubled profile z=(x,U-q), its cell occupancy is U except that s has U-1
and t has U+1. A same-cell mixed-view exchange preserves these occupancies,
but violates the fixed small-row or small-column margin, so cannot be feasible.
For exchanges between distinct cells, remaining balanced or single-defect
requires either the receiver cell to be s, or the donor cell to be t. There
are at most

    (2 receiver views at s)(2(p-1) donor coordinates)
      +(2 donor views at t)(2(p-1) receiver coordinates) = 8(p-1)

candidate exchanges. Their overlap only reduces this upper bound. A given
ordered doubled-coordinate exchange uniquely specifies its nontrivial target.
The full graph adds at most ONE additional designated repair neighbor to a
fixed defect, so its degree is <=8(p-1)+1=8p-7. This bound counts DD and DB
neighbors together, and includes invalid/capacity-blocked candidate slots as
holds when used for proposals.

A canonical slot implementation owns an overlap (receiver at s AND donor at
t) once and treats its duplicate slot as a hold. If the designated repair is
already a unit-exchange neighbor, its extra repair slot also holds. Therefore
one may use Q=8p-7 labeled slots, each actual neighbor appearing exactly once,
plus empty slots. This is O(p) candidates and O(p) straightforward local work;
no table enumeration is required. Checking positive-weight feasibility uses
fixed margins, ordinary row/column slack, and unrestricted equal-total padded
residual feasibility.

## At most two balanced neighbors per defect

The only four possible exchange-balanced targets from q-x=e_s-e_t are
q, x, x+e_s (=q+e_t), and x-e_t (=q-e_s), plus designated repair R.
Their necessary margin conditions respectively are:

* rows(s)=rows(t), or both rows are large;
* cols(s)=cols(t), or both columns are large;
* row(s) large and col(t) large;
* row(t) large and col(s) large.

The third condition forces s to be large-row/small-column (LS) and t to be
small-row/large-column (SL). All other exchange-balanced candidates are then
forbidden, leaving this target plus R. The fourth forces s SL and t LS; its
crossing is large-large and this target IS R. If neither mixed target is
feasible, both pure-view targets can coexist only when rows coincide and both
columns are large, or columns coincide and both rows are large. In either case
one of those two pure-view targets IS R. (Both rows and both columns large is
impossible for small-cell labels, and identical row+column would give s=t.)
Thus every defect has at most two balanced neighbors, and not necessarily one.
The 2x2 fixture in the [finite report](../reports/general-defect-trace.json) explicitly attains two.

## Five disjoint balanced-neighbor families

For a balanced profile A, let a=#small rows, b=#small columns. Let h_i be the
number of small cells in row i (n for a small row; b for a large row), and k_j
be the number in column j (m for a small column; a for a large column). Let

    rho_i = r_i - sum_{(i,j) in S} A_ij,
    gamma_j = c_j - sum_{(i,j) in S} A_ij

be ORDINARY, unpadded residual slacks on the large rows/columns. They are
nonnegative. A large row/column is active if its respective slack is positive.
The exact full neighbor set of A partitions as follows:

1. Small crossing inverse repairs. For each supported v=(i,j) in S, choose
   s in its small-cell column and t in its small-cell row, excluding s=t=v.
   Set x=A+e_t-e_v, q=A+e_s-e_v. Count

       N0 = sum_{v in S: A_v>0} (h_row(v) k_col(v)-1).

   Row sums of x and column sums of q are unchanged, so residual completions
   are unchanged and every candidate is feasible. Both views are bounded by U.

2. Large crossing inverse repairs. Choose s in SL whose large column is
   active, and t in LS whose large row is active; set x=A+e_t, q=A+e_s.
   Count

       N1 = (a * number active large columns)
              * (b * number active large rows).

   Exactly these slack conditions make the original row/column inequalities
   hold. Padded residual totals still agree and are feasible.

3. Pure x transfers between DISTINCT large rows. Choose a positive donor small
   entry in a large row, and a receiver in an active different large row and
   any small column. Count

       N2 = b * sum_{positive LS donor s}
                       (number active large rows - 1_{row(s) active}).

4. Pure q transfers between DISTINCT large columns. The symmetric count is

       N3 = a * sum_{positive SL donor s}
                       (number active large columns - 1_{col(s) active}).

5. Simultaneous decreases. Choose positive s in LS and positive t in SL;
   x=A-e_s, q=A-e_t. Count

       N4 = (number positive LS entries)(number positive SL entries).

Why complete: a pure x move either stays in a row, in which case it belongs
to family 1, or goes between distinct large rows, family 3. A pure q move
similarly belongs to family 1 or 4. Mixed increases are family 2; mixed
decreases are family 5. Same-cell mixed exchanges are forbidden. All additional
repair edges are exactly the inverse repairs in families 1 and 2.

Why no multiplicity: ordered defect labels identify every inverse repair
uniquely, with their crossing determining its v. Families 1 and 2 have R(z)=A,
with small versus large crossings. In family 3 or 4, the different large lines
force R(z)!=A. In family 5 the repair is A-e_s-e_t+e_v, which cannot equal A
since s!=t. Family 3 changes only x, family 4 only q, and family 5 decreases
both; they are mutually disjoint and cannot overlap family 2, which increases
both. Within each family, the nonzero increments/decrements identify its
ordered labels uniquely.

N0,...,N4 and the required weighted choice lists are computed by O(p) scans.
Choose a family in proportion to these counts. Family 1 chooses v weighted by
h_i k_j-1, then chooses the crossing ordered pair uniformly, skipping v,v.
Families 2 and 5 use independent choices from their two factor sets. Family 3
chooses donor weighted by the number of active receiver rows other than its
row, then receiver row uniformly with that exclusion and its small column
uniformly. Family 4 is symmetric. This gives a uniform VALID physical neighbor
of A, with local O(p) work and O(p) memory using simple scans, not O(p^2) list
construction. Counts are geometry counts, not completion counts.

The [exact checker](../experiments/general_defect_trace.py) intentionally
enumerates these families for finite evidence. The new
[BalancedNeighborCatalog](../src/contingency115/general_neighbors.py) stores
aggregate choices and implements rank, unrank, and one uniform integer draw
without enumerating neighbors or completions. Prepared rank/sample work and
metadata are O(p). Each catalog construction reads ordinary margins and builds
geometry in O(m+n+p); `from_problem` additionally validates its full bound
matrices in O(mn). That validation is per construction, with no global cache.
There is no claim that repeatedly constructing catalogs realizes O(p) complete
star transitions on every asymmetric input. Fixed geometry reuse remains an
implementation optimization.

The catalog checks and snapshots both physical views. Exhaustive tiny graph
comparisons cover all five families, asymmetric and transposed inputs, zero
slacks, capacity boundaries, and mutable-input regression. Its exact integer
RNG interface is a reference law, not a bounded fair-bit realization. Accepted
completion retries and a full general trace transition remain separate.

## Weighted harmonic trace and normalization

For a function g on D, define each balanced center's harmonic value by

    H(b)=sum_{x~b} c_bx g(x)/S_b,  S_b=sum_{x~b} c_bx.

If S_b=0 use an arbitrary value; no visited center can have S_b=0. Since there
are no BB edges, each center minimizes independently. The trace conductance is

    t_xy = c_xy 1_{x~y in DD} + sum_{b in B} c_xb c_by/S_b

for distinct x,y in D. Its unordered-edge energy equals the full accepted
energy of H, by the weighted-star identity. Its row sum obeys

    sum_{y!=x} t_xy
      <= sum_{y~x in DD} c_xy + sum_{b~x} c_xb
      <= w(x) degree_full(x) <= (8p-7) w(x).

The first inequality includes returns to x in each star; their omitted self
mass only makes the inequality stronger. Different balanced stars sharing a
defect cause their conductances to ADD, exactly as in this formula.

Define beta=1/[2(8p-7)] and

    P_D(x,y)=beta t_xy / w(x),  x!=y,
    P_D(x,x)=1-sum_{y!=x}P_D(x,y).

This is half-lazy, reversible with stationary law w(x)/Z_D, Z_D=sum_D w(x).
Its energy is beta E_trace/Z_D and normalized variance is Var_w,D/Z_D.
Restriction of the minimizing-centered variance gives

    Var_w,D(g) <= Var_w,full(H)
                <= C E_min(H) <= 2C E_c(H)=2C E_trace(g).

There is no factor Z_full/Z_D and no additional factor two from star
elimination. Hence inverse gap <=2C/beta. Using p<=d and U=5d^3:

    2C/beta = 2(16p-14)C <=32 d^4 U^4 = 20000 d^16.

A dyadic slot probability `2^-ceil(log2(2(8p-7)))` gives at most twice this
allowance, namely **40000d^16**. Both are mathematical derivations requiring
new formal geometry/trace proofs.
If one instead uses min-weight conductances directly, the bound is 10000d^16,
but realizing the min-weight transitions requires weight ratios/count access;
the accepted-conductance construction above avoids that extra oracle.

## Ideal-oracle implementation and its price

One trace transition starts with a half-hold and a Q-slot uniform defect
proposal. For a valid neighbor y, draw an exact uniform completion of x and
apply the existing source translation acceptance. DD targets finish directly.
For a balanced target b, repeatedly:

1. draw a uniform valid neighbor y of b with the five-family local sampler;
2. draw a fresh exact uniform completion of b;
3. accept y if the source translation passes; otherwise retry.

Each trial succeeds with probability >=1/2 by the existing directed acceptance
theorem. The successful neighbor law is c_by/S_b, because its unconditioned
successful mass is c_by/[degree(b) w(b)]. Thus the resulting off-diagonal
kernel is exactly P_D above, with no completion-count or star-sum normalizer.
A star exit uses <=2 expected trials/dense-oracle calls. The initial accepted
proposal uses at most one dense-oracle call. Given a prepared catalog,
uniform-neighbor sampling takes O(p) work per trial; catalog setup has the
separate per-construction costs stated above.
Completion matrix construction is charged to its oracle; the existing
reference implementation scans the dense rectangle for translation acceptance.
A sparse implementation can inspect only changed reference-star entries, but
that optimization is not implemented here. This does not lose an extra factor d merely
because some balanced stars have quadratic degree.

Expected retries are unbounded in the worst case. Cap a star exit after q
trials to obtain failure probability <=2^-q, then map its cap failure to a
hold or explicit failure and add that error for every trace transition. Uniform
geometry integer draws may themselves use fair-bit rejection and also need
caps or finite dyadic approximation. Approximate completion calls require their
own coupled-draw errors. The complete schedule must budget the number of
possible calls (one plus q per trace transition), not its expected number.
Version correction after checking current HEAD: the OLD direct dense interface
still does not meet its sufficient scales at U=5d^3, but the current repository
has resolved completion accuracy via dilation/rounding and compiled a bounded
encoded sampler at those smaller scales (docs/completion-dense-law.md,
docs/completion-sampler-program.md, docs/outer-sampler-compiler-checkpoint.md).
This NEW trace construction must budget/couple calls to that proved completion
family and receive its own encoded integration; it does not reopen the existing
compiler theorem. At U=47d^5, the same trace gap arithmetic has exponent 24,
again without automatically transferring any existing sampler runtime claim.

## One-side-small extension

If all rows are small OR all columns are small, the dense rectangle is empty.
Its residual total is zero on the empty side, so nonnegative residuals and
equal totals force the other side's q/x margins exactly too. Hence both views
have the prescribed margins, even if margins on the other side reach/exceed U.
All physical weights are one, there is no BB, each defect has exactly one
balanced neighbor, and DD degree is <=2(m+n-2).

The inverse repair formula remains feasible iff A_v>0: x preserves its small
row or q preserves its small column; the other view can increment a balanced
entry once, reaching U, which is ALLOWED. Its fiber has exactly
(p-1)support(A) defects, so the original efficient refresh and terminal support
correction extend unchanged. Fixtures (2,2)/(3,1), U=3 and its transpose
explicitly attain q=U and x=U, respectively. For positive margins, the same
2500d^16 bound and dimension inverse-success guarantee apply in this whole
unit branch. For bounded aspect ratio, the exact coefficient is
625[4(m+n)-6]d^15, giving O(d^15.5), rather than the dimension-only d16 envelope.

## Output law and evidence boundary

In the general weighted trace, the stationary law is proportional to w on D.
The original balanced-only output test would always fail, and the unit-branch
support correction is not justified by a weighted repair profile marginal.
A general terminal rule must reconstruct completions and check the resulting
joint repair fibers/rejection. The existing full-chain terminal law does not
automatically transfer to this restricted state law. The general d16 gap
therefore is not yet a complete uniform sampler statement.

The separate [joint repair terminal](general-defect-output.md) now provides
that correction for positive margins. Its successful inverse-fiber identity
has been independently reviewed and checked exactly on finite examples. At
the ideal scales its stationary success is at least `1/(8p)`. Finite trace
composition and encoded implementation remain open.

The [opt-in finite checker](../experiments/general_defect_trace.py) compares the
geometry and five-family partition with the actual reference graph, including
variable completion weights and a large-padding fixture. The
[report](../reports/general-defect-trace.json) distinguishes minimum-weight from
actual accepted-conductance calculations. Small-padding cases test geometry;
they do not establish the directed half-acceptance premise. Finite checks
supplement the arguments above; they do not prove them for all dimensions.

```sh
python3 experiments/general_defect_trace.py
```

A separate AI-agent check also verified the actual weighted harmonic energy,
variance restriction, detailed balance, normalized Dirichlet form and accepted
star-exit law. Remaining work is physical Lean assembly, bounded approximate
transition composition, formalizing the new joint terminal, and encoded implementation.
The existing general compiled sampler and its `80000d^17` schedule are unchanged.
