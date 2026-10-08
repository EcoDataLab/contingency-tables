# Research status

Updated October 8, 2026.

The second checkpoint adds compiled sharp tail/mean and padding-count theorems, a limit on further threshold reductions within the same padding construction, exact cycle-mixture certificates, and larger practical reference tools. The preserved [initial review](../115/115-contingency-tables-review.md) is unchanged. All upstream comparisons use `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Mathematical results

The strongest combined result is a **conditional O(d²⁵) upper bound on the ideal small-state chain's inverse spectral gap**. Here `d = 10 + (m+1)(n+1)`. The source's explicit estimate is O(d¹²⁶), weakened there to the displayed allowance d¹⁶⁰. These exponents concern an intermediate chain, not the complete sampler's bit complexity.

The deduction combines three steps:

1. [Localized transport](transport-localization.md) retains the literal leaf energies until global edge ownership removes repeated charges. Sharper path and root constants, followed by a tighter repair comparison, yield `K = O(d⁵U⁴)`. With the source's `U=d²⁰`, this gives O(d⁸⁵).
2. [All-donor switching and shifted fibers](small-entry-formalization.md) now prove, in Lean against the actual ordinary-table definitions, `P(X_ij<t) ≤ 1−∏_{k=0}^{t−1}(a−k)/(a+e−k) ≤ te/(a+e)` and `E[X_ij]≥a/(e+1)`, where `e=(m−1)(n−1)`, both incident margins are at least `a`, and `0≤t≤a`. A weak-composition family attains the product and mean bounds. These statements do not apply unchanged to cell caps, structural zeros, or nonuniform weights.
3. The [actual padding bridge](scale-formalization.md) permits `A=16d², B=16d³, L=32d³, U=64d⁵`, halving the first checkpoint's threshold. It also proves the successful-table count comparison at `U=max(2L,2Lmn(m−1)(n−1)−L−(m−1)(n−1))`. Both use each marked cell's own contribution to its enlarged margins. Exact polynomial certificates and Lean scale interfaces accompany the construction. Substitution in the localized comparison still gives O(d²⁵).

A separate AI agent [reviewed the first derivations](independent-review.md) and [the stronger second checkpoint](second-checkpoint-review.md). The remaining dependence on the upstream signature, recursion, repair, and physical-encoding results is explicit. Formal integration through the complete modified sampler is unfinished.

The [padding obstruction](padding-barrier.md) identifies a genuine limit of this construction. For the ordinary 2×n family with rows `(U,(n−1)U)`, columns all `U`, and padding `L` in every cell, success is at most `(U+1)/(U+1+Ln(n−1))`. Half-acceptance therefore requires `U≥Ln(n−1)−1`. Keeping `L=32d³` forces `U=Ω(d⁵)` in this family. This constrains the fixed uniform padded rejection construction, not all samplers, all padding choices, or the optimal spectral-gap exponent. The counting proof and finite witnesses are checked; this obstruction has not been formalized in Lean.

[Error-budget work](error-budgets.md) also sharpens mixing prefactors, conductance constants, counting-estimator sample allocations, offset precision, acceptance bits, and exact-correction precision. Its report uses the original scales unless stated otherwise, so it does not assume the new gap result. For the handoff's illustrative `d=19,b=104` example, the sufficient exact-correction precision falls from 1,017,696,497,792 to 988,002 bits when using the elementary count bound `M≤4` and the source's rare-branch cost exponent. This is a precision reduction, not a measured runtime speedup; the actual revised law and cost still need to be certified.

The new budget comparison also uses a larger product-error allowance, the source correction observable's tighter support `[9/20,10/9]`, and the actual annealing step where known. It keeps the old policies available for explicit comparisons. Its large reductions are in sufficient sample/transition bounds; they are not timings of a completed implementation.

The bounded-paper improvements control the source's specified observables and transversal trace. They do not establish a gap for arbitrary observables of the enlarged chain or extend ordinary-table exact-polynomial sampling to masked inputs.

## Implemented reference tools

- [Exact uniform and rational weighted sampling](sampler.md), with fixed margins, lower and upper cell bounds, structural zeros, feasibility checks, and explicit resource-limit failures. The dynamic program is for small fibers and has no general polynomial-time guarantee.
- [Exact full-line cycle heat baths and certified mixtures](cycle-mixtures.md). A sparse six-cycle example needs longer moves to connect its fiber. Equal weighting of all cycles slightly reduces the gap in the connected commuting example. Tuned rational mixtures instead improve it by at least 63.64% under uniform tables and 64.62% under the activity-weighted conditional-worker law. They beat **every** fixed rectangle-only mixture on this 42-table fiber. Exact positive-semidefinite and Rayleigh certificates establish those comparisons without trusting the numerical search.
- [Exact linear bounds](linear-bounds.md) using rational min-cost flow, integer witnesses, independently verified primal/dual certificates, and deficient-cut infeasibility certificates. This uses established optimization methods and requires no table enumeration.
- [Larger synthetic commuting bounds](commute-scaling.md): certified endpoints for 300 destinations and 41,328 workers, with a constructive lower bound exceeding 10²³⁶ feasible tables. Integer scaling of rational costs preserves exact certificates and improves the measured implementation time. A 750-destination case exceeds its work limit and reports no endpoints.
- [Ordinary conditional-worker sampling and moments](worker-baseline.md): a classical inverse-factorial law, exact integer urn sampling without table enumeration, and `O(mn)` rational-operation formulas for a linear metric's mean and full-covariance variance. Sampling still depends on the numeric worker total; moment evaluation does not. The API excludes cell bounds, structural zeros, and interaction weights.

All **128 Python tests pass**. The [independent implementation audit](independent-implementation-review.md) was rerun after the optimizer change: 160 constraint cases, 280 optimal endpoints and corresponding certificate mutations, 67 weighted kernels, all 512 binary 3×3 support catalogs, and the 204 simple cycles in complete 4×4 support. A second reviewer also matched the complete optimizer results against the prior Fraction implementation on 300 additional cases. Exact mixture replay verifies eight gap intervals, four bounds covering every fixed mixture in a catalog, and six strict comparisons. Floating-point search and display approximations are separate from those rational certificates.

The original audit also reproduces: 100 parameter cases, 896 path sequences, 2,968 integer leaf edges, and five spectral instances. All five archived bundle hashes and 38 pinned upstream Git blob hashes verify.

## CBEI and LEHD relevance

The [application note](cbei-use-cases.md) specifies the probability law, source universes, and current model boundaries before proposing a model change. In the public synthetic ten-worker example, the 42 feasible tables give annual commute-VMT means of 18,700 under uniform aggregate tables and about 16,158 under conditional individual-worker assignment. Both share the certified feasible range 9,460–25,080.

This is evidence that the choice of allocation law matters, not validation against observed commuting outcomes. Joint six-mode allocation would change the existing staged model. Source reconciliation, uncertain survey controls, missing routes, whole-table covariance, and commute-versus-total-VMT scope remain separate requirements. No private client data or production CBEI changes are included.

## Formal verification and next obligations

[Formal verification](formal-verification.md) is the authoritative ledger for exact compiled declarations, pinned dependencies, and compiler/axiom receipts. Supporting local statements are distinct from the complete exported sampling and counting theorems. The secure upstream Comparator requires Linux; the development host is macOS, and no full Comparator pass is claimed.

The focused Lean checks now include the quarter-coefficient, retained leaf-energy, heterogeneous-width and ownership refinements, actual-table all-donor incidence, shifted-fiber bijections, linear/product/mean bounds, dense-scale interfaces, and both improved padding-count comparisons. They also establish literal physical leaf-energy ownership, the boxed hard-weight limit, and the global adjacent-contrast sum with zero-child cases. All 68 audited declarations (66 new and two original) use only standard foundational axioms. The [verification receipt](../formal/results/verification.json) identifies exactly which declarations and source hashes were audited. These are components of the argument, not the combined O(d²⁵) theorem.

The fresh Linux focused job passed at public commit `5e5d6ef`; the full-original-theorem job at that commit is still running. Their scope excludes this checkpoint's later local refinements. The separate strict Comparator preflight failed on hosted Landlock ABI 7 because the pinned sandbox requires ABI 9. No sandbox fallback or successful Comparator claim was substituted. See the [Linux run record](linux-verification.md) for evidence and outcomes.

Next work, in priority order:

1. Complete the sharper path-variance and actual completion-adjustment proofs.
2. Use the completed physical energy ownership and adjacent-context transport in the full exposure-variance decomposition, repair comparison, and actual chain normalization.
3. Carry the generic scales through every dependent interface and update the actual finite-bit sampler, law tabulation, and machine cost proof.
4. Complete the applicable Linux verification path for the changed exported theorem.
5. Extend useful exact structural cases and correlated-sample schedules, and evaluate larger public or synthetic commuting problems with explicit target laws. Treat weighted and masked mixing guarantees as separate research problems.

Community corrections, counterexamples, independent replication, and formal contributions are welcome. A future change should update this ledger and its evidence together.
