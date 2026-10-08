# Research status

Updated October 8, 2026.

The first checkpoint strengthens the source-level ideal-chain bound and adds usable reference algorithms. The preserved [initial review](../115/115-contingency-tables-review.md) is unchanged. All upstream comparisons use `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Mathematical results

The strongest combined result is a **conditional O(d²⁵) upper bound on the ideal small-state chain's inverse spectral gap**. Here `d = 10 + (m+1)(n+1)`. The source's explicit estimate is O(d¹²⁶), weakened there to the displayed allowance d¹⁶⁰. These exponents concern an intermediate chain, not the complete sampler's bit complexity.

The deduction combines three steps:

1. [Localized transport](transport-localization.md) retains the literal leaf energies until global edge ownership removes repeated charges. Sharper path and root constants, followed by a tighter repair comparison, yield `K = O(d⁵U⁴)`. With the source's `U=d²⁰`, this gives O(d⁸⁵).
2. [All-donor switching](scale-audit.md) proves, for ordinary uniform tables and incident margins at least `a`, that `P(X_ij<t) ≤ te/(a-t+1+e)`, where `e=(m−1)(n−1)` and `1≤t≤a`. It is exact at `t=1` for equal-margin 2×2 tables. The argument does not apply unchanged to cell caps, structural zeros, or nonuniform weights.
3. A full manuscript scale audit permits `A=16d², B=16d³, L=32d³, U=128d⁵`. Nine exact polynomial certificates establish the identified arithmetic inequalities for every `d≥14`. Substitution in the localized comparison gives O(d²⁵).

A separate AI agent [reviewed these derivations](independent-review.md) and found no invalid step within their stated hypotheses. Their remaining dependence on the upstream signature, recursion, repair, and physical-encoding results is explicit. Formal integration through the complete modified sampler is unfinished.

[Error-budget work](error-budgets.md) also sharpens mixing prefactors, conductance constants, counting-estimator sample allocations, offset precision, acceptance bits, and exact-correction precision. Its report uses the original scales unless stated otherwise, so it does not assume the new gap result. For the handoff's illustrative `d=19,b=104` example, the sufficient exact-correction precision falls from 1,017,696,497,792 to 988,002 bits when using the elementary count bound `M≤4` and the source's rare-branch cost exponent. This is a precision reduction, not a measured runtime speedup; the actual revised law and cost still need to be certified.

The bounded-paper improvements control the source's specified observables and transversal trace. They do not establish a gap for arbitrary observables of the enlarged chain or extend ordinary-table exact-polynomial sampling to masked inputs.

## Implemented reference tools

- [Exact uniform and rational weighted sampling](sampler.md), with fixed margins, lower and upper cell bounds, structural zeros, feasibility checks, and explicit resource-limit failures. The dynamic program is for small fibers and has no general polynomial-time guarantee.
- Exact full-line cycle heat baths and finite-state diagnostics. A sparse six-cycle example needs longer moves to connect its fiber. In the connected commuting example, adding all simple cycles slightly reduces the measured spectral gaps; connectivity alone does not improve mixing.
- [Exact linear bounds](linear-bounds.md) using rational min-cost flow, integer witnesses, independently verified primal/dual certificates, and deficient-cut infeasibility certificates. This uses established optimization methods and requires no table enumeration.

All **78 Python tests pass**. An additional [independent implementation audit](independent-implementation-review.md) checks 160 constraint cases, 280 optimal endpoints and corresponding certificate mutations, 67 weighted kernels, all 512 binary 3×3 support catalogs, and the 204 simple cycles in complete 4×4 support. These finite checks use independent enumeration oracles and exact arithmetic. Floating-point spectral diagnostics are labeled separately.

The original audit also reproduces: 100 parameter cases, 896 path sequences, 2,968 integer leaf edges, and five spectral instances. All five archived bundle hashes and 38 pinned upstream Git blob hashes verify.

## CBEI and LEHD relevance

The [application note](cbei-use-cases.md) specifies the probability law, source universes, and current model boundaries before proposing a model change. In the public synthetic ten-worker example, the 42 feasible tables give annual commute-VMT means of 18,700 under uniform aggregate tables and about 16,158 under conditional individual-worker assignment. Both share the certified feasible range 9,460–25,080.

This is evidence that the choice of allocation law matters, not validation against observed commuting outcomes. Joint six-mode allocation would change the existing staged model. Source reconciliation, uncertain survey controls, missing routes, whole-table covariance, and commute-versus-total-VMT scope remain separate requirements. No private client data or production CBEI changes are included.

## Formal verification and next obligations

[Formal verification](formal-verification.md) is the authoritative ledger for exact compiled declarations, pinned dependencies, and compiler/axiom receipts. Supporting local statements are distinct from the complete exported sampling and counting theorems. The secure upstream Comparator requires Linux; the development host is macOS, and no full Comparator pass is claimed.

The focused Lean build passed on October 8, 2026: all 25 unchanged transport dependency modules compiled, followed by the new quarter-coefficient, retained leaf-energy, heterogeneous-width, and upstream ownership-bridge refinements. Six standalone declarations and nine new integrated declarations passed their standard-axiom checks; the integrated audit also checked two original transport declarations. This verifies local components of the argument, not the combined O(d²⁵) theorem.

Next work, in priority order:

1. Formalize the all-donor switching incidence count and completion-adjustment cases.
2. Carry localized leaf energy through the physical prefix embedding, hard-weight limit, global exposure decomposition, and repair comparison.
3. Carry the generic scales through every dependent interface and update the actual finite-bit sampler, law tabulation, and machine cost proof.
4. Complete the applicable Linux verification path for the changed exported theorem.
5. Extend practical benchmarks to larger public or synthetic commuting problems, with explicit target laws and comparison to established flow/IPF methods. Treat weighted and masked mixing guarantees as separate research problems.

Community corrections, counterexamples, independent replication, and formal contributions are welcome. A future change should update this ledger and its evidence together.
