# Review of OpenAI result #115: opportunities for iterative improvement

Prepared for Ben and an Astra Codex follow-up · 8 October 2026

**Reviewed repository:** `openai/math`, commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

**Primary papers:** [Exact Uniform Sampling of Contingency Tables with Arbitrary Margins][Sampling-PDF] and [An FPRAS for Cell-Bounded Contingency Tables][Counting-PDF]. The directory dates are September 24; this review uses the October 8 repository snapshot. Result numbering follows [the repository catalog][Catalog].

## Assessment and recommended starting point

There are concrete opportunities to improve #115. The strongest is a tighter analysis of the transport flows already constructed in the sampling paper. I derive a candidate inverse-gap bound of **\(O(d^{85})\)** using the published scales, compared with the paper's explicit **\(O(d^{126})\)** bound and its advertised allowance \(d^{160}\). A separate reanalysis of the scales, combined with that candidate, suggests **\(O(d^{33})\)**. These are bounds on the ideal small-state chain, not exponents for the complete algorithm's bit complexity.

Several less ambitious changes have clearer paths to completion: calculate walk lengths directly from the proved error bounds, reduce the precision used for exact correction, and replace a conservative inner-estimator schedule in the counting paper with logarithmic failure-probability dependence. These changes preserve the type of guarantee rather than establish a new counting or sampling theorem.

For practical implementation, I also found a reversible cycle heat-bath augmentation. Its stationary-law argument is elementary; five small exhaustive examples showed larger spectral gaps. That evidence supports prototyping, but does not establish a universal speedup or practical performance on LEHD data.

**Recommended first Astra assignment:** formalize the localized transport-energy argument in §3, retaining the existing scales and algorithm. It has the best combination of mathematical substance, a small conceptual change, and reusable Lean infrastructure. Follow with the scale audit in §4 and the schedule/correction work in §5. Keep implementation experiments as a separate deliverable.

### What was actually verified

I read all 15 main TeX sections across the two papers and inspected 18 selected Lean implementation/proof files, the unconditional theorem assembly, the Comparator challenge/configuration, and scope/verification documentation. The source manifest records their Git blob hashes. I examined the proof architecture and interfaces, not every transitive import in the much larger Lean library.

I wrote and ran `audit115.py`, which checks finite edge ownership, variance coefficients, probability budgets, residual-mixture identities, and small kernels. Integer/Fraction checks are exact; spectral and effective-resistance calculations use NumPy float64. **Lean was not installed in this environment, so no kernel compilation or Comparator run was performed.** None of the new mathematical claims in this report should be described as formally verified.

I did not find a demonstrated counterexample to the published results. The recommendations below concern slack, stronger quantitative bounds, and implementation opportunities. A scoped review is not a certification of the entire proof library.

| Priority | Proposed improvement | Evidence/status | Main obligation |
|---|---|---|---|
| 1 | Localize transport energy; use a sharper one-dimensional variance bound | Detailed derivation; exact edge checks; small weighted examples | Prove global disjointness and integrate the bound in Lean |
| 2 | Reduce padding, threshold, and bin scales together | Derived sufficient inequalities; finite adjustment checks | Reprove every dependent lemma with generic scales |
| 3 | Tighten error schedules and exact-correction precision | Direct consequences of displayed bounds | Re-tabulate the changed implemented law and verify machine cost |
| 4 | Improve bounded-counting inner estimator schedules | Standard concentration argument; exact budget checks | Preserve independent samples, coupling, and unconditional bit bounds |
| 5 | Adaptive cell caps and cycle heat-bath moves | Structural derivation; five spectral examples | Build a bounded-bit prototype and measure work per effective sample |
| Later | Weighted LEHD distributions; stronger capped sampling | Useful research directions, substantial additional work | Specify the target distribution and preserve the correct complexity model |

## 1. What the two papers establish—and how

Let \(\Omega(r,c)\) be the nonnegative integer matrices with prescribed row sums \(r\) and column sums \(c\). The sampling paper provides a feasible output on every execution of a bounded approximate sampler, with total-variation error at most \(2^{-k}\). Its exact sampler terminates almost surely and has polynomial expected bit cost. Both dimensions vary and margins are binary encoded. The exact result is for ordinary tables without input cell caps or forbidden positions. [Sampling introduction][S-Introduction]

The companion counts \(\Omega(r,c,b)\), where \(0\le X_{ij}\le b_{ij}\), allowing zero bounds. It gives relative error \(\varepsilon\) with failure probability \(\delta\), with a polynomial bound on every execution in encoded input length, \(\varepsilon^{-1}\), and \(\log\delta^{-1}\). Its flow corollary also gives feasible approximate samples, with cost polynomial in \(\tau^{-1}\); it does not assert exact bounded-flow sampling or logarithmic dependence on sampling error. [Counting introduction][C-Introduction]; [flow corollary][C-Flows]

### Sampling architecture

The main construction splits off a rectangle of large-margin rows and columns. Small cells have separate row and column views \(x_s,q_s\); balanced views represent a table. Additional states have one positive and one negative disagreement. A state's weight \(f(X)\) is the number of padded completions of the large rectangle.

The paper proves quadratic signature properties, constructs signed transport flows between conditional means, and obtains a Poincaré inequality for a graph of unit exchanges and repairs. An approximate dense-completion draw implements transitions without querying completion counts. In the ideal chain's stationary law, successful state/completion pairs have equal mass; unpadding returns an ordinary table. Accuracy of the implemented chain is proved by finite-time coupling, without assuming that its approximate transitions preserve that stationary law. [Model and graph][S-Model]; [signatures][S-Signatures]; [transport][S-Transport]; [algorithms][S-Algorithms]

The final exactness step is an explicit rare residual mixture. The algorithm tabulates the actual dyadic approximate output law, including fallback mass, on a very rare exhaustive branch. This is an expected-time construction. The catastrophic conditional cost of that branch does not disappear. [Sampling algorithms][S-Algorithms]

### Counting architecture

The companion first tightens cell ranges using flow feasibility and chooses a maximum-capacity spanning forest. Small cells are expanded into labeled binary pairs; factorial normalization cancels their multiplicity on transversals. Two distinct lifts provide omission and addition signatures. Soft penalties handle forest-boundary violations, annealing estimates a partition function, and learned defect multipliers balance the chain. The proof controls the observables and transversal trace used by the algorithm; it need not prove a full-chain gap controlling every fluctuation inside a defect type. [Scales][C-Scales]; [factorial lifts][C-Signatures]; [transport and trace][C-Transport]

This distinction matters for subsequent work: treating the two lifts as interchangeable, assuming arbitrary weight-estimate ratios are unbiased, or replacing the controlled-observable argument with an unproved full mixing assertion would change the proof.

## 2. Repository and formalization assessment

The reviewed solution assembly is [UnconditionalMain.lean][Lean-Main]. It exports the three statements `boundedSampling`, `exactSampling`, and `counting`. It discharges the finite-box Prékopa–Leindler, finite Cheeger, and Edmonds–Karp inputs using other repository theorems. Selected source files inspected here contain no `sorry`, `admit`, or axiom declarations; that observation does not audit their complete import closure.

The `by sorry` declarations in the [Comparator challenge][Comparator] are challenge placeholders, not the submitted solution. The [configuration][Comparator-Config] points to `UnconditionalMain` and permits `propext`, `Quot.sound`, and `Classical.choice`. It disables Nanoda; a follow-up should report exactly which checkers were run. The [scope note][Scope] describes the main sampling and counting claims, rather than only a supporting lemma.

The particularly useful discovery is in [IntegerLeafEnergy.lean][Lean-LeafEnergy]: the formalization already expresses recursive energy as the sum of actual leaf-clique edges before bounding it by the larger graph energy. [IntegerRootTransport.lean][Lean-RootTransport] uses that final relaxation. A tighter proof can try to preserve the earlier expression, rather than reconstruct transport flows.

Relevant layers for Astra:

| Layer | Existing file/theorem to inspect | Proposed change |
|---|---|---|
| Leaf support | `IntegerLeafEnergy.lean`: `recursiveEnergy_eq_leafEnergySum`, `leafEnergySum_eq_edges` | Retain this precise energy |
| Root transport | `IntegerRootTransport.lean`: `integer_root_graph_transport` | Export a localized-energy version |
| Physical context | `FirstPaperContextTransport.lean`: `context_transport` | Carry localization through prefix restriction and the hard limit |
| Child variance | `ContextChildVariance.lean` | Use the log-concave path inequality below |
| Global exposure | `FirstPaperExposureVariance.lean`, `FirstPaperTransversalVariance.lean` | Sum distinct edge charges across all contexts |
| Full variance | `FirstPaperFullVariance.lean` | Preserve repair comparison; substitute the new coefficient |
| Algorithm budgets | `FirstPaperOuterBudget.lean` | Derive parameters directly from the certified gap/error bounds |
| Exact precision | `ExactSamplingParameters.lean`, `ExactExpectedTime.lean` | Separate domination precision from rare-cost precision |

Preserve the committed dependency manifest and record tool versions when establishing the baseline. The repository's [Comparator instructions][Comparator-README] identify the required verification tools. The target comparison, from `lean/`, is:

```sh
lake env comparator ComparatorChallenges/ContingencyTables.json
```

First pass the unchanged baseline. Avoid updating dependencies during the comparison. Build focused modules before attempting the whole library.

## 3. Main mathematical opportunity: eliminate repeated energy charges

### 3.1 Published bound

With

\[
d=10+(m+1)(n+1),\qquad U=d^{20},
\]

the sampling paper proves

\[
Z_0\operatorname{Var}_{\mathcal T}H
\le 4d^2(U+1)^6 E(H),
\]

and then, using repair edges,

\[
\Lambda\operatorname{Var}_{f/\Lambda}H
\le \left[(1+2d^2)4d^2(U+1)^6+2\right]E(H).
\]

Here \(E\) sums minimum-endpoint-weight energy on unordered graph edges. The ideal transition comparison yields the explicit inverse-gap bound

\[
K_6=128d^2\left[(1+2d^2)4d^2(U+1)^6+2\right]
=O(d^{126}),
\]

which is subsequently replaced by \(d^{160}\). [Transport variance theorem][S-Transport]; [small-chain proposition][S-Algorithms]

There are two distinct sources of slack: the bound on a log-concave child sequence, and the repeated use of broad context energy.

### 3.2 Sharper variance bound for a log-concave sequence

Let positive child masses \(z_j\) have interval support within \(0,\ldots,U\), and let \(Z=\sum z_j\). I propose using

\[
Z\operatorname{Var}_{z/Z}(h_j)
\le U(U+1)\sum_j\min(z_j,z_{j+1})(h_j-h_{j+1})^2.
\tag{1}
\]

**Derivation.** Expand the variance into weighted pairs and telescope each difference:

\[
\frac1Z\sum_{a<b}z_a z_b(h_a-h_b)^2
\le\sum_j\frac{U L_jR_j}{Z}(h_j-h_{j+1})^2,
\]

where \(L_j=\sum_{a\le j}z_a\) and \(R_j=\sum_{b>j}z_b\). If \(z_j\le z_{j+1}\), log-concavity implies every earlier mass is at most \(z_j\), so \(L_j\le(U+1)z_j\). If \(z_j\ge z_{j+1}\), every later mass is at most \(z_{j+1}\), so \(R_j\le(U+1)z_{j+1}\). Since \(L_jR_j/Z\le\min(L_j,R_j)\), (1) follows. A one-point support has zero variance.

The paper already supplies interval support and log-concavity for these child masses. This replaces its pair-by-pair coarse aggregation, without changing the transport construction.

### 3.3 Localize each transport inequality

For context \(\sigma\), special slot \(s\), and adjacent children \(\ell-1,\ell\), define \(E_{\sigma,s,\ell}\) using only the union of leaf-clique edges in that transport construction. The existing flow proof appears to give

\[
\min(z_{\ell-1},z_\ell)(H_{\ell-1}-H_\ell)^2
\le A_0 E_{\sigma,s,\ell}(H),
\quad A_0=2+2d(U+1)^2.
\tag{2}
\]

The published statement replaces this local energy with \(E_\sigma\). To retain (2), stop the proof before that enlargement. The softened argument and finite hard-limit passage remain available; it is unnecessary to take a limit of the currents themselves.

### 3.4 Why the edge charges should be disjoint globally

Every leaf display \(D\) has occupancy \(U+1\) in exactly one slot \(s\), whose coordinates are \((\ell,U+1-\ell)\); every other slot has occupancy \(U\). A leaf edge joins \(D-e_i\) and \(D-e_j\), with distinct holes outside the fixed prefix.

The coordinatewise maximum of its endpoints recovers \(D\). From \(D\), recover the unique overfull slot \(s\), its coordinate \(\ell\), and all earlier balanced profiles, hence the context \(\sigma\). An edge can therefore belong to only one triple \((\sigma,s,\ell)\). This extends the paper's within-construction leaf uniqueness across adjacent-child contrasts and exposure depths.

Substitute (2) into (1), then sum the conditional variance decomposition over the whole exposure tree. The candidate result is

\[
Z_0\operatorname{Var}_{\mathcal T}H
\le U(U+1)\left[2+2d(U+1)^2\right]E(H).
\tag{3}
\]

There is no extra factor for the number of adjacent contrasts or exposure depths, because their localized edge sets are disjoint. Repair comparison then gives

\[
K_{\rm loc}=128d^2\left\{
(1+2d^2)U(U+1)\left[2+2d(U+1)^2\right]+2
\right\}=O(d^{85}).
\tag{4}
\]

This improves the explicit inverse-gap exponent by 41 with the original \(U=d^{20}\). It does not assert that the optimal gap has this order, or that the complete sampler has degree 85.

### Evidence, uncertainty, and acceptance test

Exact enumeration found zero repeated edge charges across 2,968 integer-slot leaf edges, including heterogeneous widths. The path inequality's sufficient cut coefficients passed on 896 positive integer log-concave sequences, with 3,957 cut checks. Three tiny physical examples with enumerated padded completions and unequal weights passed nine localized mean-contrast checks using numerical effective resistance.

The main unresolved obligation is a machine-checked global edge-ownership theorem after reindexing into physical profiles, including hard-zero weights. Preserve the unordered/oriented energy normalization. A successful follow-up should prove (1)–(4), retain the old theorem as a corollary, and pass the existing Comparator. If a flow uses edges outside the stated leaf union, or an edge acquires two owners, this proposal needs revision.

### Companion-paper consequence

A related argument may remove the exposure-depth factor from the bounded paper's

\[
C_{\rm p}=p(1+8pq^2),\qquad q=W^2,
\]

replacing it by \(1+8pq^2\). In the binary transport, the union of edge endpoints recovers a display with exactly one full original pair. In a deterministic adaptive exposure tree, that display can respect only one node that is about to expose that pair. Fixed and adaptive toy trees passed 5,120 exact edge checks through six pairs.

This is a secondary candidate, not a proved improvement to the whole FPRAS. The separate \(C_{\rm d}=8+32pq^3\) term and nested weight evaluation can still dominate. [Companion transport][C-Transport]

## 4. Second mathematical opportunity: reduce the scales together

The sampling paper fixes padding \(L=d^{12}\), small-margin threshold \(U=d^{20}\), dense bin scale \(B=d^8\), and penalty strength \(A=d^4\). A generic-parameter version of the proofs appears to permit much smaller values.

### 4.1 Sharpen the completion adjustment first

The reference-row/reference-column adjustment \(D_{XY}\) is bounded in the paper by entry magnitude \(10d\), with a union bound over up to \(d\) entries. Its actual structure suggests

\[
\|D_{XY}\|_\infty\le1,
\qquad |\operatorname{supp}D_{XY}|\le3.
\tag{5}
\]

For a unit exchange between two row-view coordinates, only two residual row margins change by opposite units; column margins do not change. The column-view case is symmetric. A row-to-column-view exchange changes one row and one column residual by the same signed unit. A repair with a small receiver leaves all large residual margins unchanged. A repair with a large receiver increases one row and one column residual by one; inverse repairs reverse the signs. Each case gives (5) under the displayed reference adjustment formula.

Thus the small-entry lemma gives rejection probability at most \(12d^3/L\), replacing \(40d^5/L\). In the three finite weighted examples, all 386 tested unit/repair adjustments had magnitude at most one and support at most three. The case argument, not those examples, must establish (5) for arbitrary instances and singleton rectangles.

### 4.2 Sufficient generic inequalities

The dense-bin and unpadding arguments appear to need the following sufficient conditions:

| Purpose | Sufficient condition |
|---|---|
| Nonzero integer bin widths | \(L\ge2B\) |
| Retain at least half the inner volume | \(B\ge8d^3\) |
| Within-bin density comparison | \(Ad/B\le1\) |
| Control the softened volume normalizer | \(2d^2/A+2d^3/B\le1/4\) |
| Small-chain acceptance at least one half, using (5) | \(12d^3/L\le1/2\) |
| Unpadding success comparison | \(U\ge8Ld^4\) |

These follow by retaining the actual expressions in the [dense proof][S-Dense] and [stationary-success argument][S-Model]. One candidate choice is

\[
A=16d^2,\quad B=16d^3,\quad L=64d^3,\quad U=512d^7.
\tag{6}
\]

All displayed conditions hold for \(d\ge14\); the acceptance bound is \(3/16\) and the unpadding bad-mass bound is at most \(1/2\). Exact rational checks cover five dimension values.

With (6), the unchanged conductance formula gives dense-bin inverse gap

\[
K_B=2(10^5d^2\cdot4B)^2=O(d^{10}),
\]

instead of \(O(d^{20})\). Its log minimum-mass allowance becomes \(O(d^3)\), rather than \(O(d^5)\). Substituting \(U=512d^7\) into the localized bound (4) gives

\[
K_{\rm loc}=O(d^5U^4)=O(d^{33}).
\tag{7}
\]

### What must be rechecked

This is a joint reparameterization, not a license to change one constant in isolation. Reprove bin containment, the interior-volume bound, the layer sum, local log-Lipschitz comparison, conductance, completion-translation acceptance, repair boxes, and unpadding success. Redefine \(C=N+dL+U+2\) and \(b=d+\lceil\log_2(C+2)\rceil\). Recheck the finite-law tabulation, denominator bounds, and physical machine schedules. The original Lean statements hard-code the old powers in multiple locations.

A conservative fallback avoids relying on (5): retain the original rejection estimate and choose \(L=128d^5\), \(U=1024d^9\), with the same reduced \(A,B\). Combined with §3, this suggests \(O(d^{41})\). It is useful as an intermediate milestone before the \(d^{33}\) candidate.

Even the new bounds remain very large. For \(d=19\), (6) has \(U\approx4.58\times10^{11}\), and (4) is about \(10^{55.75}\). This is a quantitative theorem project, not yet a practical worst-case algorithm.

## 5. Lower-risk improvements: error budgets and exact correction

### 5.1 Derive outer schedules directly from the error bound

For any certified inverse-gap bound \(K\), the published proof controls the approximate output error by

\[
e^{-J/[2(1+d^2)]}
+J(C+1)^{2d}e^{-T/K}
+J(T+1)2^{-h}.
\tag{8}
\]

Use integer ceilings and choose

\[
\begin{aligned}
J&=2(1+d^2)(k+2),\\
T&=\lceil K\rceil\left(2db+\lceil\log_2J\rceil+k+2\right),\\
h&=k+2+\lceil\log_2[J(T+1)]\rceil.
\end{aligned}
\tag{9}
\]

Since \((C+1)^{2d}\le2^{2db}\) and \(e^{-x}\le2^{-x}\), each term in (8) is at most \(2^{-k-2}\). This preserves the requested error with room to spare. It can first use the existing \(K_6\), without waiting for a stronger gap theorem. The fallback and fresh-randomness rules remain necessary. [Outer sampler and proof][S-Algorithms]

As an illustration, take the literal paper parameters for \(r=c=(3,3)\), so \(d=19,b=104\), and request \(k=20\). These are generic schedule sizes; direct enumeration of this tiny four-table example is trivial.

| Schedule | Outer trials \(J\) | Transitions per trial \(T\) | Requested dense precision \(h\) |
|---|---:|---:|---:|
| Published powers | 2,736,741 | approximately \(8.66\times10^{259}\) | 2,003,815,696 |
| (9), existing explicit \(K_6\) | 15,928 | approximately \(5.43\times10^{167}\) | 594 |
| (9), candidate localized \(K\), original scales | 15,928 | approximately \(1.01\times10^{115}\) | 418 |

These numbers are not measured runtimes or a complete bit-cost bound. They reveal slack in the prescribed schedules and the remaining impracticality of general guarantees.

### 5.2 Tighten the dense call similarly

The original dense proof bounds mixing error by \(\exp(4d^5-H/K_B)\), ideal failure by \((63/64)^{J_D}\), and offset discrepancy by a sum of dyadic errors. With the original scales, choose

\[
\begin{aligned}
J_D&=64(h+2),\\
\ell&=h+2+\lceil\log_2[J_D(1+d)]\rceil,\\
H&=\lceil K_B\rceil(4d^5+\ell).
\end{aligned}
\]

Use \(\lceil\log_2(w_{ij}+1)\rceil+\ell\) offset bits. Failure and the combined draw discrepancies are each at most \(2^{-h-2}\). This replaces \(d^{50}(h+1)^2\) by a bound of order \(d^{25}+d^{20}h\), with lower-order logarithms.

After reparameterization, use the generic allowance \(4Ad+d\lceil\log_2(4B)\rceil\) in place of \(4d^5\). It upper-bounds the natural log of inverse minimum bin mass and keeps the reasoning in integer arithmetic. [Dense schedules][S-Dense]

### 5.3 Separate the two jobs of exact-correction precision

The published exact sampler uses \(D=d^6b^2\), \(k=2D\), and rare-branch probability \(\delta=2^{-D}\). There are two independent requirements: pointwise domination and cancellation of exhaustive cost.

Suppose a certified tabulation/rare-branch cost is

\[
2^{a db}\operatorname{poly}(d,b,k)
\]

for a fixed integer \(a\). Let

\[
D=a db+1,\qquad k=D+db=(a+1)db+1.
\tag{10}
\]

Since \(M=|\Omega|\le2^{db}\), total variation \(\eta=2^{-k}\) implies

\[
p_k(z)\le 1/M+\eta,\qquad \eta\le\delta/M,
\]

so \((1-\delta)p_k(z)\le1/M\). The residual law remains nonnegative and sums to one. Meanwhile

\[
\delta\,2^{a db}=1/2.
\]

Thus the original published exponent \(a=500\) already permits a linear-in-\(db\) precision choice. On the illustrative input above, this changes \(k\) from **1,017,696,497,792** to **989,977** accuracy bits—a factor of about 1.03 million in the precision parameter, not a measured runtime factor.

The tabulation proof also states an arithmetic-operation count of \(2^{10db}\operatorname{poly}(d,b,k)\) and polynomial operand length. At that manuscript bit-operation level, an exponent 10 appears supportable. It would give \(k=11db+1\), or 21,737 on this input. **Audit compilation and public machine overhead before substituting 10 for the machine-level rare-cost exponent.** The conservative 500 choice is the immediate target. [Law tabulation and exact correction][S-Algorithms]

For the all-zero branch coin, stop reading gate bits at the first one, then use fresh bits for the ordinary branch. This preserves probability \(2^{-D}\) and reduces expected gate reads below two. The rare branch still needs all \(D\) zero bits.

### Exactness requires the changed law

The rare correction must tabulate the **actual revised** approximate sampler, including every shortened loop, dyadic rounding rule, ignored-bit convention, and fallback. Reusing the old \(p_k\) after changing the sampler would not establish exactness. The existing finite-law propagation design is reusable, but its schedule and denominator proofs must be updated.

The test script checks 100 outer parameter combinations, nine dense schedules, and 12 exact residual mixtures of biased dyadic laws. Those are implementation checks of the derivations, not substitutes for their proofs.

When adapting the Lean precision definitions, distinguish the capacity-based `smallBinaryLength` allowance from the public `marginBinaryLength` representation and prove the relevant conversion bounds. A source-level inequality is not automatically the cost bound of a compiled machine using a differently named parameter.

## 6. Improve the bounded-counting weight evaluator

The inner weight evaluator uses independent fresh bin walks for each sample. Ideal ratio observables are in \([1/2,1]\); the final population-correction observable is in \([1/8,4]\). The paper uses Chebyshev plus a union bound and prescribes

\[
N_{\rm in}=\left\lceil\frac{10^6(H+1)}{\theta\sigma^2}\right\rceil,
\quad \sigma=\frac{\xi_{\rm in}}{50(H+1)},
\]

and walk length containing \(16Q_{\rm in}/\theta\). These are conservative choices, not necessities imposed by its mixing bound. [Weight evaluation][C-Evaluation]

For the ideal correction, Hoeffding's inequality gives a relative-error tail at most

\[
2\exp\left(-\frac{2N\sigma^2}{961}\right),
\]

because its interval length is \(31/8\) and its mean is at least \(1/8\). Ratio observables satisfy a stronger bound. A sufficient common schedule is

\[
N_{\rm in}'=\left\lceil1024\sigma^{-2}
\left\lceil\log_2\frac{8(H+1)}\theta\right\rceil\right\rceil,
\quad Q_{\rm in}'=(d+1)(H+1)N_{\rm in}'.
\]

The union probability of ideal mean failures is then at most \(\theta/4\). From the paper's bin-mixing bound, it is also sufficient to use

\[
\ell_{\rm in}'=\left\lceil K_{\rm bin}
\left(H+dB+left\lceil\log_2\frac{8Q_{\rm in}'}\theta\right\rceil\right)\right\rceil.
\]

This gives per-draw TV error at most \(\theta/(8Q_{\rm in}')\). Keep the offset coupling, deterministic correction rounding, and output-range bounds. Twenty-four exact rational budget checks passed. [Hoeffding's original paper][Hoeffding]

The improvement is especially relevant because outer calls set \(\theta=\xi_{\rm in}\) to a very small tolerance. It removes one inverse-tolerance factor from sample count and replaces the walk's large inverse-failure allowance with a logarithm. It does not remove dependence on estimation accuracy, annealing height, or the number of calls.

Apply concentration to the independent ideal pairs, then couple the implementation as the source does. Do not apply independent-sample Hoeffding to the outer correlated trajectory. A persistent/noisy-weight Metropolis redesign would need its own stationary-law analysis.

## 7. Implementation opportunities with a clear mathematical boundary

### 7.1 Replace universal small-cell widths by actual caps

After removing zero-margin rows and columns and handling any resulting deterministic instance, consider

\[
B_s=\min(r_i,c_j)+1\quad\text{for a small cell }s=(i,j).
\]

A feasible defect has \(|x_s-q_s|\le1\), \(x_s\le r_i\), and \(q_s\le c_j\). Both views therefore fit within \(B_s\), and \(2\le B_s\le U\). Replacing \(y_s=U-q_s\) with \(y_s'=B_s-q_s\) is a coordinate translation; for positive margins, it should preserve the hard feasible graph and completion weights. The softened-box proof can use heterogeneous balanced widths, which the underlying signature machinery already supports.

A refined transport coefficient can retain the individual future-slot allowances, giving a candidate exposure factor

\[
\ell_\sigma(\ell_\sigma+1)
\left[2+2\sum_{t>s}(B_t+1)^2\right],
\]

where \(\ell_\sigma\) is the span of positive child support. Take a maximum over contexts when summing distinct energy charges. This can be much smaller for actual data while still bounded by the universal polynomial.

Do not simply cap views at \(\min(r_i,c_j)\): a defect may need the extra unit. Do not reorder cells arbitrarily by width: the conditional repair proof uses row-major order. Permuting rows/columns and then retaining row-major exposure is a safer way to explore order choices.

### 7.2 Add all-small cycle heat-bath transitions

Choose a fixed input-dependent catalog of cycles contained entirely in the small-cell set. On a four-cell rectangle, let \(v\) have alternating signs. Change both physical views by the same integer shift:

\[
x'=x+t v,\qquad q'=q+t v.
\]

Row sums of \(x\), column sums of \(q\), and the discrepancy pattern \(x-q\) do not change. Therefore the large residual margins, and \(f(X)\), stay constant. Box constraints determine a finite integer interval for \(t\); a uniform draw over that line is reversible because every endpoint has the same line and weight.

Lazify this heat-bath kernel \(H\), then use \(P'=(P+H)/2\). It preserves the target law, and

\[
\mathcal E_{P'}\ge\tfrac12\mathcal E_P,
\]

so any existing inverse-gap bound worsens by at most a factor two. Better mixing is an empirical possibility, not a consequence of that comparison.

The experiments enumerate complete all-small graphs, add repair edges, and use a common dyadic edge probability large enough to maintain laziness. They test a structural version of the chain with small caps; they do not execute the paper's literal \(U=d^{20}\) schedule or its dense routine. Every heat-bath detailed-balance equality was checked with rational arithmetic. Eigenvalues use float64.

| Margins: rows; columns | Graph states | Table states | Full-gap ratio, mixture/base | Transversal trace-gap ratio |
|---|---:|---:|---:|---:|
| (2,2); (2,2) | 27 | 3 | 2.47 | 4.91 |
| (3,3); (3,3) | 40 | 4 | 5.27 | 8.48 |
| (4,4); (4,4) | 53 | 5 | 9.17 | 13.08 |
| (3,3); (2,2,2) | 157 | 7 | 3.15 | 3.03 |
| (4,3); (2,3,2) | 183 | 8 | 4.72 | 3.73 |

These ratios exclude the extra arithmetic cost of a heat-bath step. Benchmark time per effective table sample before claiming a practical gain. A catalog may be empty; define the added kernel as a hold in that case. Longer allowed cycles are needed for some sparse supports.

Implement integer line draws with a fixed-bit dyadic approximation and charge their error, or use capped rejection with an explicit fallback. An uncapped exact rejection loop changes the all-execution runtime guarantee. For an exact sampler, re-tabulate this modified law.

The familiar cycle move is not claimed as a new idea. The opportunity is to integrate a residue-preserving heat bath with this paper's defect/completion construction and retain a rigorous comparison. Do not transfer a *uniform* line draw directly to the companion's factorial-lift chain: those lifted weights can vary along the line.

## 8. Relevance to LEHD, and what remains outside these theorems

Under the per-origin representation discussed in the LEHD work, fixed origin–destination counts and mode totals for that origin form a destination-by-mode table. Transpose it when useful so the small number of modes is the row dimension. Specialized fixed-row methods already exist and should be baselines; the companion's [historical discussion][C-History] identifies them. Exact dynamic programming for modest totals and direct enumeration for tiny fibers are also sensible routes. The general published schedule is not the first implementation I would deploy.

Additional bounds and forbidden destination/mode combinations fit the companion's capped model. Other overlapping demographic or geographic marginals may create a multiway fiber or a more general constrained system; flattening does not automatically turn every such constraint into a row sum, column sum, or cell cap. Reconcile the population, period, geography, integer rounding, and WFH interpretation before treating percentages as exact margins.

Uniform tables are one specified distribution over feasible aggregate tables. They are not automatically a realistic model of people's choices. For example, with row and column totals \((2,2)\), the three tables have uniform probabilities \((1/3,1/3,1/3)\). A conditional model of equally likely labeled assignments has probabilities \((1/6,2/3,1/6)\), because aggregation multiplicities differ. The script checks this example exactly.

Specify whether a weighted extension targets

\[
\pi(X)\propto\prod_{ij}w_{ij}^{X_{ij}},
\qquad\text{or}\qquad
\pi(X)\propto\prod_{ij}\frac{w_{ij}^{X_{ij}}}{X_{ij}!},
\]

or a different likelihood/prior. Row and column factors \(w_{ij}=a_i b_j\) cancel under fixed margins; only interaction information changes relative table weights. Uniform sampling followed by importance weighting can have severe weight concentration, so evaluate effective sample size and agreement with small exact posterior calculations.

Positive log-concave unary cell factors are a promising restricted extension because they fit the laminar signature model. Arbitrary likelihoods do not: even a multiplier producing child masses \((1,1,4)\) breaks log-concavity. Repair comparisons, dense weight evaluation, and bit complexity still need new proofs.

There is also an output-representation obstruction. A one-cell weighted table with margin \(R\) and weight 2 has partition function \(2^R\), whose explicit binary rational representation requires \(R+1\) bits although \(R\) is input in binary. A weighted FPRAS cannot simply inherit a polynomial-in-\(\log R\) explicit-output theorem. Logarithmic or scaled output conventions need to be specified.

For LEHD, I would first build a transparent small-fiber reference implementation, use actual caps and reversible cycle moves, and compare uniform versus conditional labeled/weighted ensembles. That applied work should proceed independently of any claim to have improved the universal theorem.

## 9. Astra work packages and completion criteria

### Package A — localized transport theorem

1. Reproduce the original Comparator baseline at the pinned commit.
2. Formalize (1) as a finite log-concave sequence lemma with interval support.
3. Export root/context transport with leaf energy, preserving the hard-limit argument.
4. Prove physical edge ownership by the coordinatewise maximum, across all contexts, slots, and adjacent contrasts.
5. Derive (3) and (4), prove the previous bound as a corollary, and rerun Comparator.

**Completion:** an admission-free focused proof, explicit coefficient, baseline/new comparison logs, and no change to the target distribution. Retain original statements while adding stronger ones. A disjointness counterexample is a valuable result; document it and adjust the proposal instead of weakening the claim silently.

### Package B — generic scales and schedules

1. Prove (5) by classifying unit, repair, and inverse-repair edges, including empty/singleton completion blocks.
2. Extract the sufficient inequalities in §4 into a parameter record and prove the dense/unpadding lemmas from it.
3. Validate the conservative \(d^{41}\) route, then the \(d^{33}\) candidate.
4. Implement (9) and the dense schedule using exact integer logarithms/ceilings.
5. Re-establish denominator and bit-cost bounds for the actual new program.

**Completion:** a complete dependency audit and a stated bound on the same mathematical quantities as the baseline. Do not present a gap exponent as the overall machine runtime exponent.

### Package C — exact correction and bounded counting

1. Prove the generic cost/domination lemma (10) using a certified rare-cost exponent, initially 500.
2. Update the dyadic-law tabulator for every sampler change; verify all fallbacks.
3. Audit whether the arithmetic exponent 10 survives machine compilation.
4. Replace the independent inner-estimator Chebyshev schedule and conservative walk allowance; preserve the unconditional output and work bounds.

**Completion:** exact probability-law identities and machine-level expected/all-execution guarantees as appropriate. Never infer infeasibility from a failed approximate count.

### Package D — practical prototype

Add actual caps, optional cycle heat baths, exact small-instance counts/distributions, and a fixed-row baseline. Benchmark balanced and skewed margins, rare categories, structural zeros, almost-forced cells, and mixed small/large regimes. Include singleton and infeasible cases, precision changes, and failure fallbacks. Measure wall time, arithmetic/weight calls, acceptance, autocorrelation, and effective sample size against exact distribution errors where enumerable.

**Completion:** reproducible results separating empirical performance from certified guarantees. Sparse/capped examples use the appropriate algorithm; do not silently apply the ordinary-table exact theorem to them.

### Suggested prompt for the next Astra thread

> Review the attached #115 report and reproduction bundle. Work from `openai/math` commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Treat the report's new bounds as candidates, not established facts. First reproduce the unchanged ContingencyTables Comparator, then pursue Package A: retain leaf-edge energy in integer root/context transport, prove the log-concave path variance lemma and global edge ownership, and derive the explicit stronger Poincaré bound. Preserve original theorem interfaces and use no new axioms or admissions. Run the provided finite checks and add focused checks only where a new failure mode warrants them. Report a counterexample if the proposal fails. If Package A succeeds, proceed to the generic-scale and schedule work; every program change must update the implemented dyadic law used in exact correction. Deliver a focused patch, proof/check logs, and an explicit account of which bounds improved and which remain unproved.

## 10. Reproduction bundle and evidence ledger

The accompanying archive contains this report, `audit115.py`, `audit115-results.json`, `source-manifest.json`, a README, and file hashes. It does not bundle the original manuscripts or Lean source tree; retrieve those from the recorded commit.

```sh
python3 audit115.py --output audit115-results-rerun.json
```

Dependencies: Python 3.10+ and NumPy. The recorded run used Python 3.14.3 and NumPy 2.4.4. No external data, network calls, or random seed are needed by the checks. Timing fields can differ between runs; float diagnostics may vary in their last digits.

| Evidence | Result | What it establishes |
|---|---|---|
| Outer probability budgets | 100 parameter cases passed | Integer choices meet the displayed sufficient inequalities |
| Dense budgets | 9 cases passed | Shortened mixing/offset/trial allocations are consistent |
| Log-concave paths | 896 sequences; 3,957 cut inequalities | Finite corroboration of (1), not a universal proof |
| Integer leaf ownership | 2,968 edge checks; zero collisions | Broad finite support check, including heterogeneous widths |
| Binary adaptive ownership | 5,120 edge checks; zero collisions | Finite corroboration of the companion consequence |
| Weighted physical transport | 9 positive adjacent contrasts passed | Numerical all-observable local-energy checks on 3 tiny completion models |
| Completion adjustment | 386 unit/repair cases passed | Finite corroboration of magnitude/support claim (5) |
| Joint reduced scales | 5 dimension values passed | Exact checks of the proposed sufficient inequalities |
| Residual mixtures | 12 biased dyadic examples passed | Nonnegative residual weights and exact mixture identities |
| Inner-counting budgets | 24 cases passed | Hoeffding/coupling allocations satisfy the stated bounds |
| Heat-bath kernels | 5 exhaustive graphs; exact detailed balance | Reversibility of those examples; numerical gap diagnostics |
| Negative controls | Support gap, non-log-concave weights, uniform/labeled distinction | Assumptions and distribution changes are not silently ignored |
| Lean/Comparator execution | Not run | No new formal-verification claim |

The strongest next result would be a verified refinement of the existing transport theorem, followed by a parameterized proof of the smaller scales. The most useful immediate LEHD result would be a small-instance-validated sampler with a clearly specified population model. Those are related workstreams with different success criteria.

## Source links

All repository links below are pinned to the reviewed commit. The manifest supplies individual blob hashes. Section labels in the discussion refer to source lemmas/propositions, avoiding dependence on PDF pagination.

- [Sampling manuscript][Sampling-PDF] and [counting manuscript][Counting-PDF]
- Sampling: [introduction][S-Introduction], [model/graph][S-Model], [signatures][S-Signatures], [transport][S-Transport], [dense routine][S-Dense], [algorithms/exact correction][S-Algorithms]
- Counting: [introduction][C-Introduction], [history][C-History], [scales][C-Scales], [integer signatures][C-Integer], [factorial lifts][C-Signatures], [transport/trace][C-Transport], [weight evaluation][C-Evaluation], [algorithm][C-Algorithm], [flow corollary][C-Flows]
- Formalization: [scope][Scope], [solution assembly][Lean-Main], [leaf energy][Lean-LeafEnergy], [root transport][Lean-RootTransport], [Comparator challenge][Comparator], [configuration][Comparator-Config], [verification instructions][Comparator-README]
- Concentration: Wassily Hoeffding, *Probability Inequalities for Sums of Bounded Random Variables*, JASA 58(301), 1963, [DOI][Hoeffding]. This supports the standard inequality used in §6; the schedules and derivations here are proposed adaptations.

[Sampling-PDF]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf
[Counting-PDF]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/main.pdf
[Catalog]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/CONTENTS.md
[S-Introduction]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/introduction.tex
[S-Model]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/model-and-graph.tex
[S-Signatures]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/signatures.tex
[S-Transport]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/transport.tex
[S-Dense]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/dense.tex
[S-Algorithms]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/algorithms.tex
[C-Introduction]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/introduction.tex
[C-History]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/history.tex
[C-Scales]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/scales.tex
[C-Integer]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/integer-signatures.tex
[C-Signatures]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/signatures.tex
[C-Transport]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/transport.tex
[C-Evaluation]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/evaluation.tex
[C-Algorithm]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/algorithm.tex
[C-Flows]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/flows.tex
[Scope]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/115.md
[Lean-Main]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/UnconditionalMain.lean
[Lean-LeafEnergy]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Transport/IntegerLeafEnergy.lean
[Lean-RootTransport]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Transport/IntegerRootTransport.lean
[Comparator]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/ComparatorChallenges/ContingencyTables.lean
[Comparator-Config]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/ComparatorChallenges/ContingencyTables.json
[Comparator-README]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/ComparatorChallenges/README.md
[Hoeffding]: https://doi.org/10.1080/01621459.1963.10500830
