# Research status

Updated October 9, 2026 UTC — fourth verified checkpoint.

The main ideal-chain bound is now **`80,000d¹⁷`**, for all ordinary equal-total margins, with automatic choice of the reference-completion or empty-block unit branch. Here `d=10+(m+1)(n+1)`. Exact completion draws remain oracle operations at these scales; the complete modified finite-bit sampler and its runtime are still open. All upstream comparisons use `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; the preserved [initial review](../115/115-contingency-tables-review.md) is unchanged.

## Verified mathematical results

Two scale choices now have proofs for actual auxiliary chains:

| Scale choice | Cutoff `U` | Padding `L` | Reference/selected inverse-gap allowance | Empty-block unit branch |
| --- | --- | --- | --- | --- |
| Ideal oracle | `5d³` | `3d` | `80,000d¹⁷` | `40,000d¹⁷` |
| Dense compatible | `47d⁵` | `32d³` | `128·47⁴d²⁵` | `64·47⁴d²⁵` |

The [physical repair proof](physical-repair-refinement.md) keeps the transversal variance outside the defect cross term. With transversal coefficient `C_T`, it obtains `C_T+(sqrt(p²C_T)+1)²`, then proves this is at most `d³U⁴` for `d≥11`, `U≥2`, and `p≤d`. The source dimension allowance always meets `d≥11`. Combining this with the unchanged dyadic proposal gives `128d⁵U⁴` for the reference/selected chain and `64d⁵U⁴` for the unit branch. The eightfold reduction from the previous conservative coefficients combines the sharper repair inequality with tighter polynomial arithmetic; exact repair alone does not produce an eightfold gain.

The [automatic branch and feasibility proof](reduced-all-small-chain.md) handles missing large rows or columns and builds a positive physical state from equal ordinary totals, including zero margins and empty index types. Thus the final equal-total wrappers need neither supplied reference indices nor an external state-existence hypothesis. Capacity, ordinary completion counts, acceptance, stationary normalization, and chain energy remain part of the verified construction.

The [ideal-scale proof](ideal-oracle-scales.md) also proves the ordinary padded-table count ratio is at most two at `U=5d³,L=3d`. It does not turn that ratio into a half-success statement for the physical chain, which also contains defect states. A separate theorem shows the retained `DenseScaleConditions` interface forces `L≥32d³`; the smaller ideal padding cannot fit it by changing its other coefficients. This is an obstruction to that sufficient interface, not to every completion algorithm.

For the literal original definitions at `U=d²⁰`, `L=d¹²`, the earlier [original-chain theorem](small-chain-gap.md) remains valid at `1024d⁸⁵`, with `512d⁸⁵` for its all-small unit companion. The pinned source's completion-chain calculation gives `98,560d¹²⁶` before weakening to its exported `d¹⁶⁰` allowance. These are inverse-gap comparisons, not complete sampler bit-complexity exponents. The older exact coefficients and reduced-scale theorems retain their names and proofs.

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

The [bounded ideal-chain backend](ideal-chain-experiment.md) now implements the literal physical transition with exact finite completion counts, plus a separately labeled rescaled diagnostic mode. Its exhaustive construction is a reference oracle with explicit work limits. The [18-case same-law panel](sampler-benchmarks.md) includes DP, heat baths, supplied tuned mixtures, worker draws under their own law, and two tiny literal physical chains. Five physical runs exhaust their excursion budgets; failed runs and unavailable method medians remain visible.

The [exact 2×2 analysis](ideal-two-by-two.md) proves a block-graph decomposition for equal margins `(t,t)`, deriving `13t+1` states, a censored nearest-neighbor probability `32β/15`, and exact stationary variance inflation. At `t=1,2`, inflation is 7,679 and 15,359, compared with one for direct iid draws and the single-rectangle full-line heat bath. A harmonic Rayleigh witness gives an `Ω(U²)` inverse-gap obstruction for this free-cutoff chain family. This is an independently reviewed mathematical derivation with exact rational certificates and full backend comparisons for `t=1,...,6`; it is not a Lean theorem or a lower bound for all samplers.

Uniform aggregate tables and conditional individual assignments are different laws. The public synthetic commuting example gives mean annual VMT of 18,700 under the first and about 16,158 under the second, with the same feasible range 9,460–25,080. This demonstrates sensitivity to the law, not empirical validity. CBEI/LEHD source reconciliation, uncertain controls, route evidence, and commute-versus-total-VMT scope remain separate requirements. No private client data or production CBEI changes are included.

## Verification and remaining work

The integrated fourth checkpoint passed **230 Python tests** and **232 Lean declaration audits**: 226 focused plus six standalone, comprising 230 new declarations and two original source statements. All audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`, or subsets. Exact report replays and independent source reviews supplement these checks; finite cases are not universal proofs.

The [formal ledger](formal-verification.md), [Lean receipts](../formal/results/), and [Python receipt](../reports/checkpoint-verification.json) identify declarations, environments, and source hashes. The [fifth review](fifth-checkpoint-review.md) records independent checks of the physical repair integration, bounded ideal-chain implementation, benchmark accounting, and exact 2×2 argument.

The [full original-theorem Linux run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847944509) succeeded at commit `5e5d6ef`; its three original exports passed the standard-axiom audit. Thor separately reproduced commit `b14082b` with 128 Python tests, 100 focused modules, and 68 declaration audits. These earlier snapshots do not cover the new refinements. [Linux verification records](linux-verification.md) preserve that distinction. Strict Comparator replay remains unverified: the tested hosted runner has Landlock ABI 7, while the pinned sandbox requires ABI 9. No weaker fallback was substituted.

Next work:

1. Integrate the generic physical mass bound and successful state/completion-pair bijection at free `U,L`. These should transfer the ordinary padding ratio to stationary ideal success and a uniform conditional output law; that theorem is still pending.
2. Carry suitable scales and chain bounds through the actual finite-bit completion oracle, revised law tabulation, output correction, and complete machine-cost proof. The ideal-only `d¹⁷` path needs a different or stronger completion interface.
3. Reproduce this checkpoint on Linux and complete strict Comparator replay on an environment meeting its sandbox requirements.
4. Close the gap between the free-cutoff `U⁴` upper allowance and the explicit `Ω(U²)` chain obstruction, or improve the transition rule with a justified target law and cost.
5. Expand same-law tests to application-scale methods, including all setup and tuning costs. Empirical competitiveness of the complete #115 sampler remains unknown.

Community corrections, counterexamples, independent replication, and contributions are welcome. Updated claims should remain attached to their verification evidence.
