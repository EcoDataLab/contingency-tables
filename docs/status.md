# Research status

Updated October 8, 2026 — third verified checkpoint.

The main result is now a **Lean-verified bound for an actual reduced-scale ideal chain**, rather than a conditional parameter substitution. The complete modified finite-bit sampler and its runtime are still open. All upstream comparisons use `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; the preserved [initial review](../115/115-contingency-tables-review.md) is unchanged.

## Verified mathematical results

Let `d=10+(m+1)(n+1)`. The [reduced-chain theorem](reduced-small-chain.md) constructs the source's actual completion chain at `U=47d⁵`, `L=32d³`, with its physical edges and dyadic proposal. It proves

$$
\operatorname{Var}_{\pi}H
\le 1024\cdot47^4d^{25}\,\mathcal E(H).
$$

The theorem assumes a nonempty positive-weight physical state space and chosen large reference row and column. Its capacity, ordinary completion counts, half-acceptance probability, stationary normalization, and energy comparison are discharged in the proof. The generic construction works for `U≥2`, `L≥3d`, with inverse-gap allowance `1024d⁵U⁴`. The displayed scales also meet the separate padding and dense-scale conditions; exponent 25 is not claimed optimal among arbitrary ideal chains.

For the literal original definitions at `U=d²⁰`, `L=d¹²`, the [original-chain theorem](small-chain-gap.md) proves `1024d⁸⁵`; its all-small unit-chain companion proves `512d⁸⁵`. The pinned source's completion-chain calculation gives `98,560d¹²⁶` before weakening to its exported `d¹⁶⁰` allowance. These are inverse-gap bounds, not full sampler bit-complexity exponents. The original all-small companion does not yet provide the corresponding branch at the new parameters.

The proof combines compiled path variance, global ownership of literal physical leaf energies, the boxed hard-weight limit, exposure variance, full physical repair, and actual reference-completion adjustment and acceptance. The current chain result retains the source's factor-two repair estimate. A separate sharper repair-coefficient draft is not included in this verified chain constant.

Two additional verified results improve the ordinary-table analysis:

- [Sharp entry bounds](small-entry-formalization.md): if both incident margins are at least `a` and `0≤t≤a`, then `P(X_ij<t) ≤ 1−∏_{k<t}(a−k)/(a+e−k) ≤ te/(a+e)` and `E[X_ij]≥a/(e+1)`, where `e=(m−1)(n−1)`. A weak-composition family attains the product and mean bounds. These statements concern uniform unrestricted tables.
- [Sequential padding](sequential-padding.md): telescope actual ordinary-table counts one added unit at a time, with both original margins incident to every padded cell at least `U`. The resulting count theorem gives at least half unpadding acceptance at `U=47d⁵`, improving the earlier `64d⁵` threshold. A shape-aware alternative is `U=max(2L,47d³mn(m−1)(n−1)−1)`, with `L=32d³`. Empty fibers and zero-donor cases are handled in the cardinality statements.

The [padding obstruction](padding-barrier.md) shows why the fifth-power threshold cannot fall merely by reducing `U` within the same fixed uniform padded-rejection construction. In a 2×n family, success is at most `(U+1)/(U+1+Ln(n−1))`; constant success requires `U=Ω(Ln²)`. This is a counting proof with exact witnesses, not a Lean theorem or a lower bound for all samplers.

The [defect-transport research](defect-transport-research.md) rules out another simple shortcut: actual all-small instances attain quadratic repair load, and each defect has only one transversal neighbor. A projected defect-mean bound also omits a real within-type variance term. These are reviewed method obstructions with exact synthetic examples; a better transport using all physical edges remains possible.

## Budgets and implemented tools

[Error-budget utilities](error-budgets.md) retain exact rational error allocations, sharper observable support, and the actual annealing index. [Independent-block median schedules](block-budgets.md) amortize burn-in over correlated observations under explicit kernel and fresh-randomness hypotheses. Their reports separate transition allowances from correction evaluations: reducing one can increase the other. They are mathematical work allowances, not timings of a completed revised oracle.

The [practical-use guide](practical-use.md) explains the target-law choice and application boundaries. Implemented tools include:

- [Exact uniform and weighted DP](sampler.md) for small bounded fibers, with structural zeros, lower bounds, feasibility checks, and resource failures.
- [Cactus coordinates](cactus-sampler.md) and [graph-block factorization](block-sampler.md): classical structural methods that avoid enumerating the full product fiber. Weighted preparation and complex-block DP have explicit limits.
- [Certified fixed cycle mixtures](cycle-mixtures.md): exact rational certificates beat every rectangle-only fixed mixture on one 42-table synthetic fiber and improve its gap by over 63%. This is not a general mixing or runtime theorem.
- [Linear metric bounds](linear-bounds.md) with checkable primal/dual and infeasibility certificates, requiring no table enumeration; [larger synthetic examples](commute-scaling.md) retain their stated limits and failures.
- [Ordinary worker allocation and moments](worker-baseline.md): a classical inverse-factorial law, integer sampling, and full-covariance linear metric moments. Its API excludes cell bounds, structural zeros, and interaction weights.

Uniform aggregate tables and conditional individual assignments are different laws. The public synthetic commuting example gives mean annual VMT of 18,700 under the first and about 16,158 under the second, with the same feasible range 9,460–25,080. This demonstrates sensitivity to the law, not empirical validity. CBEI/LEHD source reconciliation, uncertain controls, route evidence, and commute-versus-total-VMT scope remain separate requirements. No private client data or production CBEI changes are included.

## Verification and remaining work

The integrated third checkpoint passed **188 Python tests** in 3.071 seconds and **154 Lean declaration audits**: 148 focused plus six standalone, comprising 152 new declarations and two original source statements. All audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`, or subsets. Exact report replays and independent implementation checks supplement these tests; finite cases are not substituted for universal proofs.

The [formal ledger](formal-verification.md), [Lean receipts](../formal/results/), and [Python receipt](../reports/checkpoint-verification.json) identify the checked declarations, environments, and source hashes. The [third](third-checkpoint-review.md) and [fourth independent reviews](fourth-checkpoint-review.md) distinguish source review from compilation and audit receipts.

The [full original-theorem Linux run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847944509) succeeded at commit `5e5d6ef`; its three original exports passed the standard-axiom audit. Thor separately reproduced commit `b14082b` with 128 Python tests, 100 focused modules, and 68 declaration audits. These earlier snapshots do not cover later local refinements. [Linux verification records](linux-verification.md) preserve that distinction. Strict Comparator replay remains unverified: the tested hosted runner has Landlock ABI 7, while the pinned sandbox requires ABI 9. No weaker fallback was substituted.

Next work:

1. Carry the new scales and chain bounds through the actual finite-bit completion oracle, revised law tabulation, output correction, and complete machine-cost proof; supply the reduced-scale all-small branch.
2. Reproduce the changed checkpoint on Linux and complete strict Comparator replay on an environment meeting its sandbox requirements.
3. Develop a physical defect-transport argument that controls both type means and within-type variance, or identify other justified improvements.
4. Compare implemented methods on the same public or synthetic inputs and target law, including preprocessing, arithmetic costs, accuracy, and failures. Empirical competitiveness of the complete #115 sampler is unknown.

Community corrections, counterexamples, independent replication, and contributions are welcome. Updated claims should remain attached to their verification evidence.
