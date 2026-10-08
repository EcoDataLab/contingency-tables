# Independent review of the fourth #115 refinements

Review date: 8 October 2026. Upstream is pinned to
openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
This continues the [third review](third-checkpoint-review.md). It records
source-interface review separately from compilation and axiom-audit receipts.
No Lean build was launched by this reviewer.

## 1. Finite repair refinement

The local, uncompiled `RepairVarianceRefinement.lean` draft (deferred from
this publication checkpoint) matches the derivation in
[repair-cross-term-refinement.md](repair-cross-term-refinement.md).
Its assumptions are the unchanged finite repair assumptions: nonnegative base
and defect weights, domination of each defect weight by its repaired base
weight, and injectivity of the defect's repair label together with its repaired
state. The relevant multiplicity is the cardinality of the label type.

The parameterized square inequality has the correct orientation. Writing
$u=x-y$ and $v=y-a$, multiplying its difference by $\eta>0$ gives
$(u-\eta v)^2$. Applying it only to defects and leaving base variance outside
produces

$$
 \operatorname{Var}_{\mathrm{full}}
 \le[1+(1+\eta)D]V+(1+1/\eta)R.
$$

Here $D$ is the number of labels, $V$ is the source's unnormalized base
variance, and $R$ is the defect-to-repair energy. Choosing $\eta=1$ recovers
the source's factor-two repair inequality.

The square-root theorem is proved independently through finite weighted
Cauchy–Schwarz. With $\mu$ the base mean, let

$$
 A=\sum_dv_d(H_{R(d)}-\mu)^2,\qquad
 Q=\sum_dv_d(K_d-H_{R(d)})(H_{R(d)}-\mu).
$$

The actual source repair-center theorem gives $A\le DV$. Weighted Cauchy
applied to the two vectors multiplied by $\sqrt{v_d}$ gives
$Q\le\sqrt{AR}\le\sqrt{DVR}$. The expansion of the full centered sum
therefore yields

$$
 \operatorname{Var}_{\mathrm{full}}
 \le(1+D)V+R+2\sqrt{DVR}.
$$

All factors used in the square-root and product comparisons have explicit
nonnegativity. For nonnegative $C,E$ with $V\le CE$ and $R\le E$,
the draft proves

$$
 \operatorname{Var}_{\mathrm{full}}
 \le\left[C+(\sqrt{DC}+1)^2\right]E.
$$

In particular, the step $\sqrt{DCE^2}=\sqrt{DC}\,E$ uses the stated
$E\ge0$ premise. No disjointness of the repair and transversal edge sets is
assumed: both need only be bounded by the common graph energy. The proof does
not divide by $DC$, a variance, or a state weight, and therefore includes their
zero cases. When base mass is zero, domination and nonnegativity force every
defect weight to zero; the source's totalized mean definition causes no false
probabilistic assertion.

No mathematical or source-interface defect was found. At this review point,
the module is an uncompiled fourth-wave draft. Its physical-state wrapper and
any change to the reported chain constant require their own integration and
verification; this lemma alone is neither a changed chain nor a sampler.

## 2. Actual ideal chain at free cutoff and padding

The module [ReducedSmallChain.lean](../formal/Math115/ReducedSmallChain.lean)
passes semantic and source-interface review. It invokes the unchanged source
`completionChain` constructor with the new parameters in every relevant input:
the small-cell classification, capacity, state space, reference margins,
physical adjacency graph, and completion counts. Its proposal probability is
the source's unchanged dyadic $\beta_d$. This defines a new chain; it is not a
scalar substitution into `paperSmallChain` at its old parameters.

The capacity is $U$ on small cells and $N+dL+U+2$ on large cells. The unchanged,
generic `paper_residual_capacity` and `physical_paper_capacity` lemmas discharge
the two different capacity obligations: the residual tables needed by physical
variance fit the box, and every ordinary reference completion fits its large
block. The ordinary block count therefore equals the literal hard-marginal
weight. Positivity of the state weights and nonemptiness make their sum $Z$
strictly positive, giving the actual stationary law $\pi(z)=w(z)/Z$.

The source constructor's accepted translation is exactly the one counted by
`reference_edge_acceptance_reduced`. For a reference block its donor count is
$e=(m_{\rm large}-1)(n_{\rm large}-1)\le mn\le d$; the proof retains this
product bound rather than multiplying two separate bounds by $d$. Consequently
$L\ge3d$ discharges the proved half-acceptance condition $L\ge3e$, including
singleton blocks. The source accepted-count symmetry gives reversibility, and
the unchanged degree bound $5d^2+1$ and proposal allowance give a lazy chain.

The energy normalization was checked against `CompletionChainFlow` and
`CompletionEnergyComparison`. `graphEnergy` is half the oriented adjacency
sum with weight $\min(w_x,w_y)$, while the actual transition flow contains the
accepted-table count. Half acceptance therefore gives

$$
 \mathcal E_{\rm chain}(H)\ge\frac{\beta_d}{2Z}
 E_{\rm graph}(H).
$$

There is no missing factor of two in the resulting comparison with
unnormalized weighted variance. For $U\ge2$ and $L\ge3d$, the actual chain
has the proved bounds

$$
 \operatorname{Var}_{\pi}H
 \le\frac{2K_{p,U}}{\beta_d}\mathcal E_{\rm chain}(H)
 \le1024d^5U^4\mathcal E_{\rm chain}(H).
$$

The second bound uses $p\le mn\le d$, $K_{p,U}\le8d^3U^4$, and
$1/\beta_d\le64d^2$. The polynomial estimate permits $p=0$; the ideal-chain
theorem itself requires $U\ge2$. At $U=47d^5$, $L=32d^3$, this becomes
$1024\cdot47^4d^{25}$. The generic chain theorem works at smaller choices of
$U,L$ too. The stated specialization accompanies the separate padding and
dense-oracle scale obligations; it is not a claim that exponent 25 is optimal
among arbitrary ideal chains.

The explicit state-space nonemptiness assumption is consistent with the
source chain API. A generic discharge from equal original margin totals
appears available through existing constructions: take a
`GreedyFeasibleTable.reindexed` table, apply `paddedOriginal` at the new $L$,
then `jointOfTable` using `original_small_entry_le`, the two original-small
margin bounds, and generic `paper_residual_capacity`. Its retained completion
makes `hardMarginal_eq_fibre_card` positive, and `encodeProfile` packages the
balanced word into a state. The existing high-level `paperJointState` wrapper
is hardcoded to old scales, so it cannot simply be reused by substitution.
This is a precise proposed additional lemma, not a newly checked theorem.

Chosen large reference row and column remain explicit hypotheses. At the new
free parameters, the branch without such a rectangle needs a separate
unit-chain construction. Neither
this ideal-chain statement nor its noncomputable completion-count definition
supplies a finite-bit dense draw, complete sampler, output-law correction, or
end-to-end runtime at the new scales.

The reviewer subsequently read the clean direct-compile and axiom-audit
receipts for both chain modules. `SmallChainGap` completed with exit zero
(77.7 seconds); its six audited exports include the exact $2K/\beta$ comparison
and $1024d^{85}$ bound for the literal original `paperSmallChain`.
`ReducedSmallChain` completed with exit zero (68.8 seconds); its nine audited
principal exports include the actual chain definitions, stationary identity,
energy comparison, and $1024\cdot47^4d^{25}$ bound. Every listed declaration
uses only `propext`, `Classical.choice`, and `Quot.sound`.

These receipts establish the formal verification status of the two ideal-chain
results above. They are `.tools/formal-debug/small-chain-target.log`,
`small-chain-axioms.log`, `reduced-small-chain-target.log`, and
`reduced-small-chain-axioms.log`. The author separately reported successful
compilation of `PhysicalFullVariance` and an axiom audit of both principal
statements with the same three axioms. The finite-bit sampler and complete
runtime remain separate work.

The reviewer also read the subsequent `AllSmallChainGap` receipts:
`.tools/formal-debug/all-small-clean-target.log` records clean exit zero
(48.3 seconds), and `all-small-axioms.log` lists only the same three axioms
for its two exports. This companion concerns the literal original
`unitSmallChain` at $U=d^{20}$, $L=d^{12}$. The exact energy identity gives
$K_{p,U}/\beta_d$, with no half-acceptance loss, and hence $512d^{85}$.
The three chain modules now have seventeen audited principal exports in
total. This original-scale all-small companion does not silently supply a
unit chain at the reduced parameters.

## 3. Exact sampling over graph blocks

The implementation in [block_sampler.py](../src/contingency115/block_sampler.py)
and its [proof note](block-sampler.md) pass independent review. The
factorization follows from the classical integer-circulation decomposition.
After removing cells whose lower and upper bounds agree, the difference of
any two feasible tables is a circulation on the remaining bipartite graph.
Every simple cycle lies in one biconnected edge block. Consequently each
block's incident row and column totals are invariant, including at shared
articulation vertices; bridge values are invariant as well.

Conversely, replacing each block by any table with its invariant local
margins and original bounds preserves every global margin. The restrictions
and replacements are inverse, establishing a Cartesian product of fibers.
This is a proof for the whole bounded fiber, independent of the finite test
catalog. It permits fixed positive cells and nonzero lower bounds. Local
positions that are not block edges have bounds zero, so a fixed positive
global chord is counted only in the fixed factor.

A non-bridge biconnected simple graph has minimum degree two. If its number
of edges equals its number of vertices, every degree is two and the block is
a single cycle, justifying the code's cycle-versus-DP dispatch. Mixed-radix
rank and unrank use each factor's exact count; their ordering need not agree
with the whole-table DP ordering. For product-cell weights, the fixed factor
times the block normalizers is the exact global normalizer. Fixed weights
cancel from normalized probabilities. Factorial arguments remain the full
cell values, not values with their lower bounds subtracted.

The shared DP budgets charge both successful and failed factor work, and
the tighter shared/per-block allowance is passed to each local DP. A failed
preparation remains failed on later calls. Weighted cycle preparation uses
the existing planner's remaining global allowances. All required positive
normalizers are complete before sampling accesses the RNG. An exactly zero
factor may stop preparation because the whole product is then zero.
Malformed budgets, infeasible fibers, and feasible zero-mass laws remain
distinct cases.

The arithmetic limits are correctly qualified. Raw-cell preflight precedes
powers and factorials, but does not bound DP completion coefficients, the
product normalizer, or total memory. Cycle coefficient limits do not bound
DP caches or transient operands. The DFS traversal is linear; canonical
sorting, local materialization, max flow, and sampling arithmetic have
separate costs. No general polynomial-time or wall-clock speedup conclusion
follows from the recorded state/transition counters.

Review requested an explicit conditional RNG premise, now present in the
API and proof note. Each requested integer must be uniform conditional on
the previous calls. Uniform marginals alone do not make block draws
independent: the new exact negative control reuses one uniform rank across
two factors and produces only seven diagonal tables out of the 49-table
fiber. The default `SystemRandom` follows the intended interface; an arbitrary
custom source must satisfy the stated contract.

All thirteen temporary block-sampler tests passed independently with site
packages disabled. They include all 512 support graphs of shape $3\times3$
against a cycle-union partition oracle, every binary $2\times3$ support and
attainable margin pair, weighted and bounded comparisons with the whole-table
DP, and a complete random-choice tree for two complex factors. The
[benchmark](../examples/block_factorization.py) also replayed exactly against
[the saved report](../reports/block-factorization.json), including all four
source hashes, four block counts, and the huge-cycle/complex-block hybrid.

The synthetic family has $7^k$ tables, factorial-weight normalizer $(5/2)^k$,
and factor-DP preparation using $9k$ states and $14k$ transitions. These are
exact claims about the specified constrained fiber, not evidence for a fitted
commuting model or an ordinary unconstrained worker urn. This implementation
is mathematically reviewed and executable-tested; it has no Lean certification
or new-priority claim.

## 4. Defect-transport method obstructions

The research-only [defect-transport note](defect-transport-research.md) passes
source-interface and mathematical review. Its claims were checked against
the actual `Pattern`, `IsDefect`, `repairMatrix`, `repairWord`, and physical
adjacency definitions. All ordered distinct negative/positive labels are
allowed; the prefix-order condition used elsewhere is not a restriction on
the complete defect state space.

For equal square margins $M<U$, all cells are small, the completion block is
empty, and each feasible state has weight one. Both views are bounded by
$M$, so the capacity imposes no extra restriction. Replacing $U$ by a larger
value only translates the complementary $y=U-q$ coordinates and preserves
the graph. Padding has no effect because there are no large cells.

For a transversal $A$, negative cell $s$, positive cell $t$, and receiver
$v=(\operatorname{row}(t),\operatorname{col}(s))$, the inverse repair is
$x=A+e_t-e_v$, $q=A+e_s-e_v$. It is feasible exactly when $A_v>0$.
If $v=s$ or $v=t$, one subtraction cancels, but the other view still requires
that positivity. There are exactly $p-1$ ordered label pairs for each receiver,
so the inverse count is $(p-1)|\operatorname{supp}(A)|$. The source small-entry
bound at $M=8d^3$ proves average repair load at least $p(p-1)/2$ under the old
published scales. This family also satisfies $M<47d^5$, so its obstruction
persists at the new reduced cutoff.

The unique-transversal-neighbor argument matches the physical graph. Mixed
$x/y$ exchanges alter the fixed total of $x$ and are infeasible. A feasible
two-$x$ exchange stays in one row; reaching a transversal forces the new
table to be $q$, possible only when the defect labels share a row. The
two-$y$ case is its column counterpart. In both cases the neighbor is already
the designated repair; otherwise only the separately added designated edge
reaches a transversal. Averaging direct repairs therefore cannot introduce
new targets while retaining this graph.

The randomized-pushforward obstruction also holds for a centered quadratic
comparison. Summing it over all centered coordinate indicators gives a
necessary coefficient at least $|\mathcal D|/|\mathcal T|$, provided
$|\mathcal T|>1$. The trace calculation correctly handles nonuniform target
loads and does not infer a lower bound on the full graph's Poincare constant.

The missing within-type variance is explicit in the $2\times2$, margin-two
example. Each of twelve ordered defect types has two states; centering
$x_{11}$ within its type gives values $-1/2,+1/2$. Transversals have value
zero. Thus the full unnormalized variance is six, while its defect-mean
projection is identically zero. Defect-to-defect edges preserve these
centered values; the energy is six, entirely on edges to transversals.
This disproves control of the omitted term solely by defect-to-defect
energy, without excluding control by all physical energies.

The pinned #114 source already averages the four binary assignments by
their actual masses. Its observable projection retains transversal values
and replaces a defect type by its mean, so it does not supply the missing
within-type term for an arbitrary #115 observable. The note correctly treats
integer conditional transport, physical edge membership, weighted edge
multiplicity, and a within-type bound as separate unproved requirements.
Its four-slot auxiliary template really produces two negative and two
positive slots after removal; the note does not claim that template has
positive weight in a specific physical table instance.

A fresh standard-library-only call to
[defect_transport.py](../experiments/defect_transport.py) matched every field
of [the saved eight-case report](../reports/defect-transport-research.json).
The two state enumerations agree, and the selected literal doubled-coordinate
edge checks pass. These checks supplement the general repair-count and
neighbor proofs; they neither estimate eigenvalues nor establish a new
universal gap bound. No current verified theorem or sampler constant is
changed by this research assessment.
