# Independent review of the third #115 refinements

Review date: 8 October 2026. Upstream is pinned to
openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
This continues the [second review](second-checkpoint-review.md). The publication
checkpoint through PhysicalLeafEnergy, the ordinary-table tails, and the
actual padding bridge is frozen there. This note records the next wave.

## 1. Path, exposure, and full physical variance integration

The review inspected PathVariance.lean, PathDistanceSum.lean,
PhysicalExposureVariance.lean, and PhysicalFullVariance.lean against the
unchanged upstream choice-fibre, repair, and support-encoding interfaces.
These are source-level assessments; a source review is not a completed build.
The path author reports a successful build of PathVariance and PathDistanceSum
and a thirteen-declaration audit containing only propext, Classical.choice,
and Quot.sound. The exposure and full-variance build status is tracked
separately by the main workflow. The exposure author subsequently reported a
successful targeted build (9026 jobs, 67 seconds for the target); its expanded
seven-declaration axiom audit also completed with only propext,
Classical.choice, and Quot.sound. The full-wrapper author subsequently
reported successful compilation and a two-principal-statement axiom audit
with only propext, Classical.choice, and Quot.sound.

The path proof uses the global no-valley inequality, not local log concavity
alone. Choosing a mode $m$ bounds each weighted deviation from its value by
$|r-m|$ times the whole path energy. The exact distance sum is
$U(U+1)/2-m(U-m)$, at most $T_U=U(U+1)/2$. This includes zero total mass
and uses the actual source child-minimum theorem to exclude support gaps.

The exposure draft connects arbitrary child moments through the unchanged
choice-fibre identity, then retains each prefix contribution in an exact
telescoping sum. Reindexing by canonical owners adds no depth or adjacent-level
factor. The full-variance draft applies the unchanged repair inequality to
the same unnormalized variance and symmetric graph energy. Its coefficient is

$$
 C_T=T_U\left[2+\frac{(p-1)(U+1)^2}{2}\right],\qquad
 C_{\mathrm{full}}=(1+2p^2)C_T+2,
$$

where $p-1$ is truncated at zero. This first integration retains the source's
factor-two repair estimate rather than asserting the sharper square-root
coefficient. The actual capacity hypothesis supplies repair weight domination;
positive-support encoding then transfers the inequality to every physical
state observable. No probabilistic normalization is inserted into these
unnormalized identities.

The remaining source interface is identification with the actual lazy-chain Dirichlet form
and discharge of the explicit capacity and scale hypotheses for the selected
construction. These drafts do not establish a complete revised sampler or a
runtime bound.

## 2. Independent blocks for the counting-weight oracle

The review inspected [block_budgets.py](../src/contingency115/block_budgets.py),
its exact finite-law tests, and [block-budgets.md](block-budgets.md). The new
schedule amortizes an initial bin-chain burn-in over correlated observations,
then amplifies accuracy with independent block medians. It is an estimator
change with conditional work allowances, not an implemented physical oracle.

For a fixed exact lazy reversible bin kernel with inverse gap at most $K$,
spacing $S=\lceil(7/10)Kr\rceil$ bounds centered lag correlation by
$\rho=2^{-r}$. Fresh conditional offset noise is essential: its randomness
must also be independent of future transitions. Under those hypotheses,
off-diagonal covariance of corrections equals covariance of their conditional
bin means, giving the block-mean bound

$$
 \frac{\operatorname{Var}(\overline Y)}{\mu^2}
 \le \frac{F_rv(a,b)}{N},\qquad
 F_r=\frac{2^r+1}{2^r-1},\qquad
 v(a,b)=\frac{(b-a)^2}{4ab}.
$$

Thus $N=\lceil F_rv/(p\sigma^2)\rceil$ gives block failure at most
$p\in(0,1/4]$ by Chebyshev. Independent block failures are dominated by
the binomial law even when their probabilities differ. The exact majority-tail
search uses a valid finite cap: $6L-5$ for $p\le1/4$, and
$\max(1,2L-3)$ for $p\le1/8$. Markov bounds on $3^X$ and $7^X$ prove
these caps, respectively. No numerical logarithm or empirical mixing estimate
enters that search. The default $p=1/8$ is a policy choice, not a universal
optimum.

Only independent block starts and scalar offset draws need coupling charges.
After coupled starts coincide, exact transitions driven by the same future
randomness keep their whole trajectories equal. This argument would fail for
an approximate transition kernel without a separate trajectory-error budget.
Independent medians need no unbiasedness: coordinatewise monotonicity of order
statistics transfers pointwise relative rounding error through means and
medians, leaving the same $j+2$ multiplicative-error allocation. The source
tolerance option satisfies the same bound with an inequality, while equality
in its final upper-error expression holds only for the product policy.

The code separately counts transitions, ratio and correction evaluations,
offset draws, mean operations, and median comparisons. Its exact report
replay matches all four tuples and five policies per tuple. On the displayed
$H=j=100$ tuple the default schedule has about 8.547 times fewer transition
allowances and 24.571 times more correction evaluations than the improved
independent comparator. The low-mixing-cost example actually increases both
categories. These are operation allowances under common hypotheses, not
measured time or a universal speedup.

All 13 block tests passed independently, including exact stationary two-state
laws with conditional noise, majority minimality, changed numerical ordering,
non-dyadic failure targets, narrow support, and $H=j=0$ with one correction
observation. Negative controls exercise shared offsets, shared block failures,
and reuse of future transition bits. The actual oracle program, revised Lean
estimator interface, source-to-input bit-length conversion, and any exact
tabulation of the changed random law remain separate obligations. Generic
kernel transition counts also require an exact bounded-work implementation
before they become full bit-cost bounds.

## 3. Exact sampling on cactus variable support

The review inspected [cactus.py](../src/contingency115/cactus.py), its tests,
[cactus-sampler.md](cactus-sampler.md), and the synthetic commuting example.
The algorithm correctly tests the graph after removing all cells whose
effective upper and lower bounds agree, including fixed positive cells.
Feasibility is checked by the existing integer Edmonds–Karp witness first.
An infeasible fiber may return zero without passing the graph test; a feasible
noncactus graph is rejected even when its particular fiber happens to be easy.

The spanning-forest argument gives an integer basis, not just a real nullspace.
Subtracting each non-tree-edge coefficient leaves a circulation on a forest,
which vanishes by removing leaves. Edge-disjoint fundamental cycles therefore
give independent integer interval coordinates. Cycles may share vertices:
each alternating perturbation already has zero margin at the shared vertex.
The orientation choice and sorting preserve this argument. All noncycle cells
are fixed across the fiber, whether or not their supplied bounds coincide.

Mixed-radix rank and unrank are inverse maps of this Cartesian product.
Uniform sampling uses one uniform integer rank, with a deterministic branch
for singleton fibers. Neither graph preparation nor these rank operations
enumerates the interval widths. The deterministic algorithm is polynomial in
the encoded input and output sizes within the cactus class; the random-bit
execution length retains the existing uniform-integer source assumption.

For product activities with or without factorials, each cell belongs to at
most one varying coordinate, so the weight factorization is exact. The code
uses full cell counts in factorials and includes fixed-cell contributions in
the normalizer. Zero activities restrict positive support before planning;
contradictory coordinate requirements and positive fixed counts at zero
activity correctly produce zero mass. Conditional uniformity of successive
integer draws is needed for the product sampling law.

The weighted planner bounds every retained rational mass, line normalizer,
cumulative integer coefficient, and final normalizer before any powers or
factorials. If raw line masses have numerator and denominator exponents
$A,B$ and line width $w$, a common denominator is at most $2^{wB}$ and
its integer cumulative total at most $w2^{A+wB}$. This justifies the
implemented storage allowance. It does not bound transient arithmetic or
Python object overhead. Weighted preparation still enumerates positive line
widths, so this part has no general polynomial-in-binary-input claim.

All 13 tests passed independently, including the complete $3\times3$ support
graph catalog, lower/fixed counts, disconnected and vertex-sharing cycles,
zero mass, a 401-bit fiber size, exact random-choice trees, and rejection before
weight arithmetic. A fresh standard-library-only example replay equals the
saved JSON report and its source hashes. The nine-table example has factorial
activity normalizer 3721. Its bounded, nonseparable conditional-Poisson law is
distinct from the ordinary urn baseline in workers.py. Neither its activities
nor its fictional commuting controls establish an empirical travel model.

## 4. The actual ideal-chain bridge and the remaining scale gap

Source-interface review of the uncompiled
[SmallChainGap.lean](../formal/Math115/SmallChainGap.lean) draft passes.
It uses the unchanged stationary law and the actual proposal-to-energy
comparison. With $Z=\sum_xw_x$ and source proposal $\beta_d$, those
identities are $\pi_x=w_x/Z$ and
$\mathcal E_{\rm chain}\ge\beta_d E_{\rm graph}/(2Z)$. Thus an
unnormalized full variance bound with coefficient $K_{p,U}$ implies the
normalized Poincare coefficient $2K_{p,U}/\beta_d$, with no lost or
duplicated normalizing factor. Positivity of the actual state weights and
nonempty state space justify division by $Z$.

The conservative arithmetic is valid even at $p=0$:

$$
 K_{p,U}\le8d^3U^4,\qquad
 \frac{2K_{p,U}}{\beta_d}\le1024d^5U^4
 \quad(1\le d,U,\ p\le d),
$$

using $\beta_d\ge1/(64d^2)$. The literal source paperSmallChain fixes
$U=d^{20}$ and $L=d^{12}$; the draft discharges its actual capacity
hypothesis and therefore targets $1024d^{85}$ for that chain. This is a
concrete stronger bound on the original ideal chain, conditional here on
successful compilation of the draft and its new variance dependencies.
The exact coefficient is retained separately from that conservative exponent.
For comparison, the source's displayed same-chain theorem uses $d^{160}$,
while its less weakened intermediate bound is already
$98{,}560d^6U^6=98{,}560d^{126}$. The new argument improves the actual
dependence from $d^6U^6$ to $d^5U^4$; it should not be presented merely as
removing the source's final coarse weakening.

The tighter scalar bound retains $(p-1)_+\le d-1$, so the transport's inner
factor is at most $2dU^2$ and $C_T\le2dU^4$. This also covers $p=0$.
The additional all-small draft uses the unchanged exact unit-chain energy
identity, not its weakened half-acceptance inequality. It consequently removes
that factor two and targets $512d^{85}$ when every cell is small. Source
inspection confirms the weight is identically one in precisely this branch.

An actual reparameterized chain needs a replacement for upstream
reference_edge_acceptance, which hardcodes $L=d^{12}$. The source energy
comparison cannot be reused at $L=32d^3$ merely by substituting the new $U$.
The new [ReferenceEdgeAcceptance.lean](../formal/Math115/ReferenceEdgeAcceptance.lean)
draft supplies that replacement and passes independent source-interface
review. Compilation and axiom audit remain pending.

Its counting route is precise. Unit decrements can reject only at zero source
entries. With at most two negative cells and all reference incident margins
at least $L$, the ordinary zero-entry bound gives rejection probability at
most $2e/(L+e)$, where $e=(m'-1)(n'-1)$ for the reference block. Hence
$L\ge3e$ guarantees half acceptance. The proposed $L=32d^3$ easily
satisfies this arithmetic. The draft identifies the actual source Accepted
predicate with the zero-entry union, partitions the actual table cardinality,
and converts to acceptedCount only at the final step. It handles all three
branches of physicalAdjacent: exchanges, designated repairs recovered from
their literal repairWord and labels, and inverse repairs using their own
elementary classification. It never infers Bounds(-D) from Bounds(D) alone.
The capacity, margin-padding, and target-total premises match the unchanged
source definitions. No assumed count bound or capped-fiber switching theorem
replaces these connections. Once compiled, this acceptance interface must be
instantiated in the actual reduced-scale chain; the separate padded-success
theorem and complete sampler implementation remain distinct obligations.

The late CompletionAdjustment additions handle the degenerate geometry
explicitly. For a singleton completion row or column, between equals the
entrywise difference of a source table and a supplied target table, so every
translation is nonnegative. For an empty rectangle, a nonempty ordinary fiber
has exactly one table; the actual positive physical weight supplies that
nonemptiness. Those draft interfaces are sound. The acceptance draft handles
$L=0$ in the raw zero-entry count by the elementary subtype bound, requires
$L+e>0$ before cancellation or division, and invokes the target-feasible
singleton argument when $e=L=0$. This resolves the threshold-one corner case
without an invalid $1\le0$ premise. Its separate accepted-translation
equivalence uses the actual forward and backward cellwise translations.

The additional repaired_profile_prefix draft preserves both doubled views of
every row-major prefix cell. The defect relation gives equality of the two
represented counts before the first defect; scalar repair preserves that
count, and the explicit upper bound justifies the natural-number complement
identity. Preserving only the uncomplemented coordinate would not have been
an adequate interface statement by itself.

## 5. Sequential padding gives a smaller sufficient threshold

The root agent proposed telescoping ordinary-table cardinalities instead of
union-bounding all failures in the final padded table. This improvement passes
independent review, including the conditioning and margin hypotheses.

Let $K$ be the marked cells, every one of whose original incident margins is
at least $U\ge0$. Add one unit at one marked cell at a time, for
$q=|K|L$ total additions. Let $N_s$ count all ordinary nonnegative tables
at the margins after $s$ additions. Adding one to the selected entry bijects
the previous fiber with the next fiber restricted to a positive entry there.
Both new incident margins are at least $U+1$, because all earlier padding
is nonnegative. The threshold-one switching bound therefore gives

$$
 N_{s+1}(U+1)\le N_s(U+1+e),\qquad
 e=(m-1)(n-1).
$$

No conditional large-block law is substituted here: every count is a full
ordinary-table count at its own margins. Multiplying the inequalities yields

$$
 N_q(U+1)^q\le N_0(U+1+e)^q.
$$

The successful final tables are exactly the image of adding $L$ at every
marked cell to an original table, so, when $N_0>0$,

$$
 \Pr(\text{unpadding succeeds})=\frac{N_0}{N_q}
 \ge\left(1+\frac e{U+1}\right)^{-q}.
$$

This remains one for $q=0$ or $e=0$. The denominator $U+1$ is positive
even at $U=0$. Keeping track of the selected cell's own earlier additions
gives the stronger product
$[\prod_{s=1}^{L}(U+s)/(U+s+e)]^{|K|}$, regardless of contributions
from previously padded cells in the same row or column.

A short rational certificate supports $U=47d^5$, improving the earlier
$64d^5$ sufficient threshold while retaining the same exponent. For
$x\ge0$ and $t=qx<3$, use
$\binom qk x^k\le t^k/k!$ and
$k!\ge2\cdot3^{k-2}$ for $k\ge2$ to obtain

$$
 (1+x)^q\le1+t+\frac{t^2}{2(1-t/3)}.
$$

The right side is increasing for $0\le t<3$. At $t=32/47$, its exact
value is $10147/5123<2$, with slack $99/5123$. Thus $qx\le32/47$
suffices for success greater than one half. With $L=32d^3$,
$|K|\le d$, $e\le d$, and $U=47d^5$, one has
$qe/(U+1)\le32/47$. This argument uses only finite binomial expansion,
factorial inequalities, and a rational geometric-series bound; logarithms or
exponentials are not required for its formalization.

The new PaddingGrowth and PaddingGrowthAlgebra drafts pass source review.
The former applies the actual shifted_card equivalence to each enlarged
ordinary fiber, then inducts over units in a cell and the marked finite set.
It does not divide by a fiber count, so its final natural-number theorem
includes empty fibers and $d=0$. The latter has an alternative direct finite
induction: with $E(t)=(t^2+4t+6)/(6-2t)$, the numerator of
$E(t+x)-(1+x)E(t)$ after multiplying by its two positive denominators is

$$
 2xt^3+x^2(2t^2+6t+18)\ge0.
$$

This proves the same finite-power envelope without even a series bound. The
equivalent-form lemma correctly excludes $t=3$, where Lean's division-by-zero
convention would otherwise make the two rational expressions unequal.
The author subsequently reported clean compilation of both modules with
Lean 4.34.1 and a nineteen-declaration axiom audit using only propext,
Classical.choice, and Quot.sound (some arithmetic declarations use subsets).

The implementation in [padding_growth.py](../src/contingency115/padding_growth.py)
also passes review. It rejects malformed arguments and rates at or above
three, distinguishes that analytic limitation from infeasibility, and handles
zero increments or donors with exact growth one. It explicitly requires the
original incident-margin hypothesis; numeric inputs do not certify a table
instance. Its shape threshold

$$
 U=\max\{2L,\;47d^3mn(m-1)(n-1)-1\}
$$

uses the full shape to avoid circular selection of marked cells, and attains
rate at most $32/47$. Singleton dimensions use $U=2L$ and give success one.
Five tests passed independently, including every marked subset of the
$2\times3$ fixture at two padding amounts: 128 actual full-fiber comparisons.
An independent standard-library replay exactly matches the saved report's
certificate, five dimension comparisons, seven shape comparisons, all 128
fiber checks, and all source hashes.

These count bounds do not by themselves reparameterize the sampler, remove
its edge-acceptance obligation, or certify a runtime improvement. Their
constant improvement is compatible with the earlier $\Omega(d^5)$ obstruction
for this construction.

## 6. A smaller repair cross-term coefficient

The derivation in [repair-cross-term-refinement.md](repair-cross-term-refinement.md)
also passes independent review under the actual finite repair hypotheses.
Center at the base weighted mean. Let $V$ be base variance, $A$ the weighted
defect-side squared displacement of repaired values from that mean, and $R$
the repair displacement energy. The typewise injection gives $A\le DV$.
Weighted Cauchy–Schwarz only on defects then yields

$$
 \operatorname{Var}_{\rm full}
 \le V+A+R+2\sqrt{AR}
 \le(1+D)V+R+2\sqrt{DVR}.
$$

For $V\le C_TE$, $R\le E$, and nonnegative $C_T,E$, the coefficient
can therefore be $C_T+(\sqrt{DC_T}+1)^2$. This improves the earlier
$[\sqrt{(1+D)C_T}+1]^2$ by keeping the base contribution outside the
cross term. It does not require transversal and repair edge sets to be
disjoint. Zero base mass forces all dominated defect weights to zero, and
other zero cases follow from nonnegative finite sums. The equivalent
parameterized square inequality has the stated optimal positive parameter
when $DC_T>0$. This remains a mathematical constant refinement, separate
from the currently integrated source repair theorem and unchanged exponents.

## Verification recorded for this wave

All 13 block-budget, 13 cactus, and five padding-growth tests passed independently.
A fresh exact call to the
report implementation matches reports/block-budget-comparison.json across
all four tuples and five policies per tuple. The cactus example also replays
exactly with site packages disabled, including its saved source hashes.
The padding-growth report likewise replays exactly with site packages disabled.
Physical, acceptance, padding-growth, and chain draft theorem interfaces
were inspected, but no independent Lean build was run during this review;
the main workflow schedules compilation and tracks its receipts.
