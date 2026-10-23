# Contingency tables: proofs and reference algorithms

An open EcoDataLab project improving quantitative bounds and tools for [OpenAI result #115](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/115.md), which studies integer tables with fixed row and column totals. The same actual rational defect chain now has compiled inverse-gap bounds of [**d⁸ for general shapes**](docs/physical-defect-trace.md) and [**d^6.5 for bounded-aspect rectangles**](docs/aggregate-defect-trace.md), including nonsquare tables; the latter improves its previous shape-specific d⁷ bound. Our complete compiled sampler **re-proves the same existential bounded-sampling theorem as upstream** through a different machine and the earlier d¹⁷ route; it now has an [explicit but extremely loose runtime degree](research/runtime-degree/checkpoints/complete-explicit-degree-v1/), without establishing a smaller degree than upstream. A [checked finite-word construction](research/physical-trace-schedule/) now uses the stronger trace to sample defect and completion pairs to requested accuracy; converting those pairs to uniform original tables remains open.

<!-- BEGIN GENERATED CLAIMS -->

| Claim | Quantity and evidence | Assumptions and present limit |
|---|---|---|
| [Same-chain bounded-aspect refinement](docs/claims-and-evidence.md#aggregate-actual-gap) | Inverse gap ≤ 34848 A^(3/2)d^(13/2); exact shape bound 34848d⁵(m+n−2)³; lean theorem | Finite ordered dimensions m,n≥2; natural margins; p≥2 small cells; nonempty positive defect support; U=11d(m+n−2), L=7; exact completion counts. A≥0 and (m+n−2)²≤Ad; fixed A for the d^6.5 asymptotic reading. The Lean aspect statement is squared. Same canonical proposal Q=4p−3 in both completion branches. Take the minimum with the earlier shape bound; thin shapes retain d⁸. Complete sampler/runtime integration remains open. |
| [Actual rational defect trace](docs/claims-and-evidence.md#retained-defect-gap) | Inverse gap ≤ 431d⁸; shape bound 3872d⁶(m+n−2)²; lean theorem | Finite ordered dimensions m,n≥2; natural margins; at least two small cells and nonempty positive defect support. U=11d(m+n−2), L=7, d=10+(m+1)(n+1). Exact accepted completion counts. Rational changed chain: actual degree, conductances and normalization are compiled. Dyadic factor-two rounding remains reviewed mathematics. Complete sampler integration and runtime are open; baseline compiler/imports are trusted. |
| [Physical completion adapter at arbitrary scales](docs/claims-and-evidence.md#legacy-physical-completion) | Every-word feasibility; completion TV ≤ 2⁻ʰ; lean theorem | Natural margins and U,L,h; an actual positive physical state at the source capacity; both computed large-line lists nonempty. Accuracy uses a uniform word of the state-dependent computed length. Singleton blocks are included. Compiled semantic adapter to the old executable draw. No assumed accuracy or density condition. Fresh finite-word defect transitions and walks are now checked separately; empty completion blocks, revised output correction and encoded costs remain outside this adapter. No new complete sampler or exponent. |
| [Trace bound at the computed reference pair](docs/claims-and-evidence.md#computed-reference-trace) | Var ≤ 32p³ aggregateCT · energy; exact trace transition; lean theorem | Natural finite margins; both computed large-line lists nonempty; nonempty positive defect support; p≥2 small cells; U≥2 and L≥7 for the variance bound. The reference pair is fixed by margins and cutoff. Ordinary Lean compile and full headline closures; trusted reused imports. Same aggregate coefficient, with no equality assertion between different reference kernels. The bounded finite-word transition and walk are now checked separately. Complete sampler integration and encoded costs remain open. No new exponent or Comparator acceptance. |
| [Executable list acceptance correspondence](docs/claims-and-evidence.md#listed-acceptance) | Exact Boolean and accept/reject correspondence on every word; lean theorem | Natural finite margins and U,L,h; both computed large-line lists nonempty; actual physical source and candidate states at the source capacity; exact state-dependent completion word length. No-proposal hold and singleton selected blocks are included. Ordinary Lean compile and four complete headline closures with standard axioms and trusted reused imports. No adjacency, positive-original-margin, accuracy or padding-lower-bound premise. This closes acceptance; the finite-word trace composition and walk are checked separately. Revised outer realizer and cost composition remain open. No new exponent or Comparator acceptance. |
| [Weighted retry law (conditional)](docs/claims-and-evidence.md#weighted-exit-helper) | TV ≤ (1-a)^J + Jδ; a = ρΣS/w; lean theorem | Finite trial/output spaces; nonnegative rational S with positive total; w>0; supplied ideal successful-mass identity and trial accuracy; supplied fallback; J independent words of fixed width k. The flat bank has exactly J*k fair bits. Compiled conditional helper with complete headline closures and trusted reused imports. Its physical specialization, entering-edge success bound, zero-star handling and explicit local schedule are now compiled separately. This helper alone does not supply the incoming trace clock, adaptive outer schedule or encoded costs. No new gap or runtime exponent, default rebuild or Comparator acceptance. |
| [Bounded physical exits and explicit schedule](docs/claims-and-evidence.md#physical-star-trial) | Exit TV ≤ (1−ρ/2)^J+J·2⁻ʰ; explicit schedule ≤ 2⁻⁽ᵗ⁺¹⁾; lean theorem | Equal-total finite natural margins; both computed large-line lists nonempty; actual balanced source and supplied defect fallback. Entering-edge bounds require L≥7 and adjacency to that defect. Arbitrary natural U; original zero margins and singleton selected blocks allowed. Each local exit uses exactly J·[clog₂(32d²)+q_b(h)] uniform bits. Ordinary compilation and full headline-closure audits with trusted reused imports. Success mass, completion accuracy and entering-edge probability bound are derived. Zero-star TV does not imply deterministic holding. The finite-word trace composition and walk are checked separately. Complete outer sampler and encoded costs remain open. No new runtime exponent, default rebuild or Comparator acceptance. |
| [Rational clock and incoming acceptance](docs/claims-and-evidence.md#rational-clock-step) | Incoming TV ≤ 2⁻ᴺ+2⁻ʰ; exact ideal conductance/[2(4p−3)w(d)]; lean theorem | Actual source defect, p≥2 small cells and both computed large-line lists nonempty for completion. Equal original totals for conductance/neighbor identification. Arbitrary natural U,L,N,h; original zero margins and singleton selected blocks allowed. Exactly N·clog₂(2(4p−3))+q_d(h) uniform bits. Ordinary compilation and full headline-closure audits with trusted imports. The generally nondyadic clock is approximated by a fixed fair word. Incoming-plus-exit composition, a uniform finite-word reservation and the repeated walk are now checked separately. No complete sampler or runtime improvement follows from this local interface. |
| [Scheduled finite-word sampling of defect and completion pairs](docs/claims-and-evidence.md#physical-trace-walk) | TV to uniform defect and completion pairs ≤ 2⁻ʰ; explicit finite bit bank; lean theorem | Equal-total finite natural margins; both computed large-line lists nonempty; U≥2, L≥7, p≥2 small cells; supplied actual defect start fixed before the fresh word. Any natural h, including zero. Original zero margins and singleton selected completion blocks are allowed. All schedule parameters are explicit natural formulas; reserved width is T·B+F(h+2). Ordinary compilation and full headline-closure audits with trusted imports; separate AI source review. The output retains a defect label and is not an original table. Initialization and empty-support branches, the general repair/acceptance map, outer retries, other completion branches and encoded costs remain open. The compiled empty-support example makes a universal initialization shortcut impossible under the current hypotheses. No new complete sampler/runtime exponent, default-target Linux rebuild or Comparator acceptance. |
| [Sharper reviewed aspect coefficient](docs/claims-and-evidence.md#aggregate-incidence-gap) | Inverse gap ≤ 15488 A^(3/2)d^(13/2); reviewed mathematics | Ordinary equal-total margins; m,n≥2; nonempty positive defect branch; (m+n−2)²≤Ad; U=11d(m+n−2), L=7. Reference proposal 1/[2(4p−3)]; unit branch uses its smaller degree allowance 2(m+n)−3. Ideal completions. Reviewed AI mathematical derivation with exact finite checks. Its sharper orientation estimates and separate unit proposal remain outside the compiled 34848 theorem. This is not a complete sampler runtime bound. |
| [Restricted family with both dimensions growing](docs/claims-and-evidence.md#growing-family-gap) | Inverse gap O(d⁴) at fixed aspect; explicit 64856A d⁵ alternative; reviewed mathematics | Only the specified (R+1)-by-2b margins, R,b≥2; small-row total 1≤h≤U/[2(R−1)]; U=11ds, L=7, s=R+2b−1; s²≤Ad for fixed A; ordinary exact completion counts; unchanged rational proposal 1/[2(4p−3)]. Reviewed AI mathematics with separate one-token physical and higher-total slice/place fixtures. The d⁴ allowance uses Morris’s unextracted universal constant C_Z. No Lean verification, arbitrary-margin gap theorem, numerical d⁴ sampling schedule or runtime claim. General compiled exponent remains 8. |
| [Restricted rectangular family](docs/claims-and-evidence.md#thin-family-gap) | Inverse gap ≤ 2840d⁶; reviewed mathematics | Only the explicit 3-by-2b margins in the linked proof, b≥2; 1≤h≤floor(U/2); U=11d(2b+1), L=7; ordinary exact completion counts; rational proposal 1/[2(4p−3)]. Reviewed AI mathematics with one exact finite fixture. Not all thin tables; no Lean verification, complete sampler or runtime bound. The unrestricted compiled exponent remains 8. |
| [Original chain at smaller scales](docs/claims-and-evidence.md#physical-spectral-gap) | Inverse gap ≤ 3442d⁹; lean theorem | Finite ordered dimensions m,n≥2; equal natural-margin totals, including zeros; d=10+(m+1)(n+1). Ideal completion transitions. Ordinary additive compilation with full headline dependency closures; trusted pinned compiler and baseline imports. This existing chain construction at new scales is separate from the rational defect trace and the unchanged complete sampler; it is not a runtime bound. |
| [Ideal auxiliary chain](docs/claims-and-evidence.md#ideal-inverse-gap) | Inverse spectral gap ≤ 80,000d¹⁷; lean theorem | Equal-total natural margins; finite index sets; d=10+(m+1)(n+1). Ideal completion transitions; a step count does not give machine runtime. |
| [Bounded sampler: alternative proof](docs/claims-and-evidence.md#complete-bounded-sampler) | Every-tape time ≤ C Sᴰ; total variation ≤ 2⁻ʰ; lean theorem | Any finite dimensions m,n and natural margins r:Fin m→ℕ,c:Fin n→ℕ with equal ordinary totals; zero margins and empty dimensions are included. Numeric precision h≥1; M=∑ᵢrᵢ and S=m+n+clog₂(M+1)+h+1. One fixed machine and natural C>0,D apply uniformly to all inputs. Accuracy uses independent uniform fair bits; feasibility holds for every tape. Exactly the same existential theorem statement as upstream; a smaller complete machine-time exponent is not established. The separate explicit-runtime-degree claim now fixes D for the same local machine. This historical Linux receipt retains its original scope. The d¹⁷ inverse-gap power and S¹⁷⁰ reserved-bit/input allowance are different quantities. Practical sampler performance and strict Comparator acceptance remain unknown. This bounded near-uniform theorem supplies no exact-sampling or counting extension. |
| [Explicit complete runtime degree](docs/claims-and-evidence.md#explicit-runtime-degree) | Every-tape time ≤ C Sᴰ with explicit D; total variation ≤ 2⁻ʰ; lean theorem | Any finite dimensions m,n and natural margins r:Fin m→ℕ,c:Fin n→ℕ with equal ordinary totals; zero margins and empty dimensions are included. Numeric precision h≥1; M=∑ᵢrᵢ and S=m+n+clog₂(M+1)+h+1. One fixed machine and positive natural C apply uniformly; D is the fixed expression in CompleteDraw.FixedMachineTheorem. Accuracy uses independent uniform fair bits; feasibility holds for every tape. The existential sampling statement matches upstream. The additional explicit D has 4,137 decimal digits and is a conservative upper bound; no smaller machine-time degree than upstream has been established. The new degree packet has ordinary compilation and four complete headline-closure audits with trusted imports. It is separate from the historical default Linux receipt and strict Comparator acceptance. The numerical coefficient C remains existential. The d⁸/d^6.5 ideal-chain improvements are not integrated into this d¹⁷ machine. No practical runtime, exact-sampling or counting improvement follows. |
| [Finite-word probability law](docs/claims-and-evidence.md#finite-word-law) | Total variation ≤ 2⁻ʰ; lean theorem | Equal-total natural margins, including zero margins and empty dimensions; uniform reserved bits. This typed-law statement alone does not identify a literal encoded outer walker; the complete-machine claim has its own named and dependency-closure checks. |
| [Encoded completion and schedule](docs/claims-and-evidence.md#component-cost) | Polynomial charged component cost; lean component cost | Completion: d≥14, equal totals, dimension/free-coordinate bounds, dense margins; supplied finite word. Schedule: encoded margins and precision input. These component statements do not give the complete public machine's numerical runtime exponent. |
| [Executable references](docs/claims-and-evidence.md#executable-references) | Exact finite experiments; scope-specific measured timings; executable reference | Finite instances and each experiment’s stated target law and constraints. Enumeration grows rapidly; experiments do not prove general mixing or polynomial runtime. |

Saved receipt scopes (counts are distinct named audit requests, not exhaustive theorem totals):

- [Current integrated bounded-sampler Linux verification](formal/results/linux-focused-5b4af40/verification.json): **1511** named declarations; exact commit `5b4af40`. Exact-commit hosted Linux focused 1511 named replay and fresh compiled-environment audit. No separate standalone named audits, Comparator or new runtime result. Theorem sources and compilation inputs still match; checking-tool bytes changed: `scripts/prepare_environment_audit.py`. This historical receipt does not verify the changed tools or record a new run.

Historical component receipts are preserved in the [ledger](claims.json); their named declarations overlap the current integrated aggregate and are not added to it. The historical Linux focused run is a separate reproduction scope. Compiled-environment audit status is reported separately in [formal verification](docs/formal-verification.md); these counts describe saved named audits. Pinned upstream sources are checked when present; absent checkout files are explicitly reported as unchecked by the ledger JSON output.

<!-- END GENERATED CLAIMS -->

One concrete composed improvement is the complete reserved-bit allowance:
upstream `344^644 S^1288`, versus `12672000000·37^62·5^85 S^170` for our
compiled d¹⁷ route, in the same public size measure. The [comparison](docs/composed-complexity.md#comparable-result-in-the-same-public-size-measure)
includes every reserved completion retry. The local complete machine now has
a fixed explicit degree with 4,137 decimal digits; upstream's degree remains
symbolic, so no complete runtime advantage is established.

## Review and reproduction

Research, implementations, and the reviews labeled “independent” were produced by OpenAI Codex agents under EcoDataLab's direction. Those reviews use separate AI agents to examine AI-produced work. They provide another check, but no outside human MCMC or Lean review is claimed. We invite human reviewers to examine the Markov-chain arguments, formal theorem interfaces, executable semantics, and benchmark design; [contributing guidance](CONTRIBUTING.md) explains the evidence to include.

The native Windows checks were run on project-owned hardware by the same AI-assisted workflow. No outsider reproduction of those runs is recorded. Hosted Linux CI provides a fresh compilation environment, with the trust and scope limits described below. Compiler success establishes the checked Lean statements under their hypotheses and trusted dependencies; it does not establish scientific validity of a commuting model.

The [aggregate verification record](reports/aggregate-defect-trace-validation.json) binds the d^6.5 Lean build, printer-cost certificate and clean-checkout checks. The [versioned Comparator guard](research/strict-sampler-checkpoints/versioned-guard-v2/) reduced one measured complete metadata check from 26.92 to 1.13 seconds while retaining the stated checking boundaries. That startup receipt assumes a quiet cache under trusted supervision. A subsequent [cache-memo repair](research/strict-sampler-checkpoints/hash-memo-normalization-v1/) passed the previously failing dependency gate twice; full strict sampler acceptance remains open.

## What the research establishes

The compiled d¹⁷ ideal-chain bound covers all ordinary equal-total margins, including empty dimensions. The [completion-oracle proofs](docs/completion-oracle-formalization.md) establish equal accepted representation counts, acceptance at least one quarter at `L=3d`, and bounded-retry accuracy. The [dense completion proofs](docs/completion-dense-law.md) construct accurate completion laws at every physical state. The [finite-walk guide](docs/physical-finite-walk.md) connects those laws to restarted output-error bounds, and the [Boolean-law checkpoint](docs/completion-boolean-schedule.md) removes the supplied feasible fallback at the level of the typed finite-word law.

The historical default aggregate integrated the encoded-completion, physical-bridge, and both-branch Boolean-law/schedule proofs. Its [stage receipt](formal/results/completion-aggregate-1236/verification.json) binds the selected audits and authenticated object reuses. The [compiled-environment audit](formal/results/environment-aggregate-1236/README.md) enumerates the selected theorem environment and all six headline dependency closures; its totals include pinned upstream declarations. The [fresh Linux reproduction at `df469a5`](formal/results/linux-focused-df469a5/README.md) passed the complete focused workflow, with official dependency caches trusted. The [earlier runner failure](formal/results/linux-focused-cef573d-failure/README.md) remains preserved.

Subsequent repairs to the literal outer sampler are tracked in one [compiler checkpoint](docs/outer-sampler-compiler-checkpoint.md), with exact attempted sources, successful module checks, and retained failures. These results have a separate receipt scope from the earlier default aggregate and its Linux reproduction. The original [outer-sampler archive](research/outer-sampler/) remains unchanged. All thirteen research modules now pass ordinary Lean compilation, including the fixed public machine, final bounded-sampling theorem, and supplied-word cost bound. The audit records exact statement types, axioms and all 22 headline dependency closures. The [publication review](formal/results/native-sampler-checkpoint-publication-review.json) binds the released sources, audit report, and statement readback. The [separate quantitative packet](research/runtime-degree/checkpoints/complete-explicit-degree-v1/) now supplies an explicit numerical degree for that same machine. The expanded default target has now passed its fresh hosted Linux build and environment audit. Strict sampler replay remains pending. The [composed complexity review](docs/composed-complexity.md) separates the inverse-gap and reserved-bit powers from the explicit but very loose full machine-time exponent; no application-speed claim follows from these bounds.

Other results include sharp ordinary-table tail and mean bounds, a dense-compatible `128·47⁴d²⁵` inverse-gap bound, padding and rejection obstructions, exact small-fiber samplers, graph-block and cactus methods, certified cycle mixtures, and a classical worker-allocation baseline. [Practical uses](docs/practical-use.md) explains which probability law and tool fit a problem. The [status ledger](docs/status.md) records the detailed proof obligations.

## Starting points

- [Actual aggregate defect trace](docs/aggregate-defect-trace.md) and its [compiled packet](research/aggregate-defect-trace/): d^6.5 at bounded aspect for the same kernel, with exact comparison against the earlier d⁷ shape bound.
- [Actual rational defect trace](docs/physical-defect-trace.md) and its [compiled packet](research/physical-defect-trace/): general d⁸ bound, actual geometry and normalized kernel; the [original-chain d⁹ wrapper](docs/physical-spectral-chain.md) covers automatic branches.
- [Growing rectangular family](docs/growing-row-extension.md): reviewed `O(d⁴)` bound with a classical unextracted constant, and an explicit `64856A d⁵` alternative. Both dimensions and the small-row total may grow within the stated range. The specified margins remain essential; the [one-token family](docs/growing-row-comparison.md) keeps sharper constants. Neither family bound is a general-table or Lean result; the supporting [finite junction-energy helper](research/junction-star/) has compiled separately.
- [Parallel defect edges in thin tables](docs/thin-row-extension.md): reviewed d⁶ bound for an explicitly specified 3-by-2b margin family, allowing first-row mass up to half the cutoff. The [single-token proof](docs/thin-parallel-comparison.md) has a sharper constant; neither family theorem is Lean-formalized.
- [Aggregate incidence](docs/aggregate-incidence.md), [further shape bounds](docs/further-shape-bounds.md) and the [zero-range subclass](docs/zero-range-subclass.md): reviewed d^6.5 bounds beyond square tables, a restricted O(d⁴) comparison, and the [remaining general obstacle](docs/generic-repair-limit.md).
- [Quadratic-width transport](docs/retained-root-spectrum.md), [reciprocal padding growth](docs/reciprocal-padding-growth.md), and [constant padding](docs/constant-padding.md): the compiled transport and counting ingredients beneath the newer chain results.
- [Completion from the frozen sampler](docs/legacy-completion-backend.md): the arbitrary-scale physical adapter, computed-reference trace bound and executable list acceptance correspondence now compile. The stronger trace now has a checked finite-word schedule for uniform defect and completion pairs. Original-table correction, initialization/branches and full cost composition remain open.
- [Actual program costs](docs/composed-complexity.md#exact-draw-cost-certificates): compiled certificates now cover branch selection, printing, initialization, fallback construction, retry-word parsing and the exact unit packed trial. The [reference trial](research/runtime-degree/checkpoints/actual-reference-degree-v1/) and [complete numerical runtime degree](research/runtime-degree/checkpoints/complete-explicit-degree-v1/) are now closed, with separate ordinary compilation and full headline-closure evidence.

- [Repair-based output](docs/repair-output.md) and its [compiled research packet](research/repair-accept/): the actual repair fibers, bounded-bit terminal, retry error and executable reference.
- [Defect-only acceleration](docs/defect-trace.md), [arbitrary rectangular refinement](docs/rectangular-defect.md), and [weighted generalization](docs/general-defect-trace.md): geometry, inverse-gap derivations, exact trace checks and remaining physical proof obligations.
- [Direct defect sampler](docs/direct-defect-sampler.md), [composed schedule](docs/defect-sampler-composition.md), and [general joint output correction](docs/general-defect-output.md): finite-bit execution, actual output laws and honest cost accounting.
- [Shape-aware proposals and smaller completion scales](docs/shape-aware-defect.md), [resolvent spacing](docs/resolvent-rejection.md), and the [compiled finite hybrid lemma](research/spaced-attempts/): current follow-ups, bounded components, evidence and open integration work.
- [Further research directions](docs/research-directions.md): lessons from the complete integer-multiplication improvement sequence, and specific limits on transferring ideas from other fields.
- [Reference implementation improvements](docs/implementation-benchmarks.md): reproducible weighted-draw, graph-traversal and heat-bath preparation gains, with cold-start and memory costs.
- [Original research review](115/115-contingency-tables-review.md) and [source manifest](115/source-manifest.json): the preserved October 8, 2026 handoff, including hypotheses to test.
- [Contributor handoff](docs/handoff.md): checked results, reproduction commands, frozen research, and ordered next-round obligations.
- [Research status](docs/status.md): current results, limitations, and next proof obligations.
- [Ideal-only scales and dense-interface limit](docs/ideal-oracle-scales.md), [sharper physical repair](docs/physical-repair-refinement.md), and [automatic branches and feasibility](docs/reduced-all-small-chain.md).
- [Stationary success and uniform output](docs/physical-stationary-success.md): completion counts, the exact output bijection, and independent stationary retries.
- [Finite walks and output error](docs/physical-finite-walk.md): the actual selected transition law, independent restarts, and sufficient walk/retry schedules.
- [Completion by dilation and rounding](docs/completion-oracle-dilation.md), its [finite-table and geometry proofs](docs/completion-oracle-formalization.md), and [approximate-oracle error propagation](docs/physical-approximate-oracle.md): the completion route at the smaller outer scales and its remaining program obligations.
- [Canonical dense completion laws](docs/completion-dense-law.md): the pinned dense draw, analytic premise discharge, all-state residual inputs, and instantiated outer probability law.
- [Encoded completion program](docs/completion-sampler-program.md): computed dense inputs, exact whole-word and prefix semantics, computed fallback, and polynomial charged cost.
- [Computed physical bridges](docs/completion-physical-bridges.md): actual list ordering, proposal laws, physical completion accuracy, finite-law schedules, and empty-block reconstruction.
- [Both-branch Boolean law and computed schedule](docs/completion-boolean-schedule.md): automatic branches and greedy fallback, pointwise feasibility, full typed-word accuracy, and the computed numeric reservations.
- [Executable Boolean codec and retries](docs/completion-boolean-program.md): the additional signed decoder, independent word bank, frozen proof receipt, and native evaluations.
- [Binary-list completion decoder](docs/completion-list-decoder.md): exact encoded table semantics and a polynomial charged machine-cost proof for the decoder.
- [Explicit completion schedules](docs/completion-schedules.md): walk lengths, separate transition/terminal precisions, and a proved polynomial allowance for reserved random bits.
- [Completion input-size bounds](docs/completion-input-size.md): binary margin encodings, the public sampling-size measure, and generic deterministic cost composition.
- [Stationary-rejection obstruction](docs/stationary-success-obstruction.md): why the extra defect mass can force quadratic retries even when ordinary unpadding always succeeds.
- [Dense-compatible ideal chain](docs/reduced-small-chain.md), [original-chain comparison](docs/small-chain-gap.md), and [sequential padding](docs/sequential-padding.md).
- [Transport proof](docs/transport-localization.md), [switching and scale proof](docs/scale-audit.md), [error budgets](docs/error-budgets.md), and [AI-agent mathematical review](docs/independent-review.md).
- [Sharp tail formalization](docs/small-entry-formalization.md), [actual padding bridge](docs/scale-formalization.md), [padding obstruction](docs/padding-barrier.md), and [second AI-agent review](docs/second-checkpoint-review.md).
- [Formal verification](docs/formal-verification.md): compiler outcomes, exact pins, and remaining integration work.
- [Third AI-agent review](docs/third-checkpoint-review.md), [fourth review](docs/fourth-checkpoint-review.md), and [defect-transport research](docs/defect-transport-research.md): checked improvements and limits of the current repair method.
- [Reference sampler](docs/sampler.md), [linear bounds](docs/linear-bounds.md), and [AI-agent implementation audit](docs/independent-implementation-review.md).
- [Cactus sampler](docs/cactus-sampler.md), [graph-block sampler](docs/block-sampler.md), and [correlated-observation budgets](docs/block-budgets.md).
- [Certified cycle mixtures](docs/cycle-mixtures.md), [ordinary worker baseline](docs/worker-baseline.md), and [larger synthetic commuting benchmarks](docs/commute-scaling.md).
- [Commuting applications](docs/commuting-use-cases.md): target laws, source reconciliation, a synthetic example, and the [public LODES hold-out backtest](docs/commuting-backtest.md).
- [Mature worker-law libraries](docs/worker-library-benchmarks.md) and the [optional SciPy wrapper](docs/worker-baseline.md#optional-scipy-backend): matching-law benchmarks and practical batch sampling.
- [Composed complexity](docs/composed-complexity.md): source-level cost accounting, the explicit degree and remaining composed-cost obligations.
- [Executable ideal chain](docs/ideal-chain-experiment.md), [same-law sampling benchmarks](docs/sampler-benchmarks.md), [exact 2×2 analysis](docs/ideal-two-by-two.md), and [fifth AI-agent review](docs/fifth-checkpoint-review.md).
- [Contributing](CONTRIBUTING.md): welcome to mathematical corrections, counterexamples, formal proofs, implementations, and reproducible benchmarks.

## Reproduce the Python tools

Python 3.10 or newer is required. From the repository root, the core checks run directly from source without an installation:

```sh
make test
# Or, without Make:
PYTHONPATH=src python3 -m unittest discover -s tests -v
```

Both routes support a fresh source checkout without an editable install; tests requiring optional numerical libraries report explicit skips when those libraries are absent. For NumPy-dependent audits and research reports, install the research extra first:

```sh
python3 -m pip install -e '.[research]'
make verify
# Optional: download and verify the pinned upstream source files.
make sources
```

Saved mixture certificates replay using exact standard-library arithmetic. Replay reconstructs the current kernels and checks every rational witness, reporting any change from the historical producer's source bytes. Add `--require-producer-sources` to the replay script to require exact producer identity as well. Source verification downloads only files in the pinned manifest and checks their Git blob hashes; it does not execute upstream code. The [Python release receipt](reports/stage-close-verification.json) records the tested source hashes, optional dependencies, full verification command, and clean public-source archive run. It also preserves the hosted clean-checkout failure that led to the ledger fix. The [hosted Python receipt](reports/hosted-final-stage.json) records successful checks on Python 3.10, 3.12, and 3.13 at `df469a5`. The [environment-runner repair receipt](reports/environment-runner-fix/verification.json) records its local full-suite result and separate AI review. The [earlier stage receipt](reports/stage-verification.json) and [checkpoint receipt](reports/checkpoint-verification.json) retain their historical scopes.

For a first API example:

```python
from contingency115.tables import TableProblem, ExactTableSampler

problem = TableProblem([2, 2], [2, 2])
sampler = ExactTableSampler(problem)
assert sampler.count() == 3
table = sampler.sample()
assert sampler.unrank(sampler.rank(table)) == table
```

Generate the standard report bundle under the ignored local directory with `make reports-local` (also available as `make reports`). Set `REPORT_DIR` to choose another rerun destination. Additional reports can be run individually:

```sh
mkdir -p .local/reports
make reports-local
python3 experiments/padding_growth.py --output .local/reports/padding-growth.json
python3 experiments/block_budget_report.py --output .local/reports/block-budget-comparison.json
python3 examples/cactus_commute.py --output .local/reports/cactus-commute.json
python3 examples/block_factorization.py --output .local/reports/block-factorization.json
make replay-mixtures
python3 experiments/ideal_two_by_two.py --output .local/reports/ideal-two-by-two.json
python3 experiments/stationary_success.py --output .local/reports/stationary-success.json
python3 experiments/lattice_completion.py --output .local/reports/lattice-completion.json
python3 experiments/sampler_benchmarks.py --draws 500 --warmup 200 --repetitions 2 --output .local/reports/sampler-benchmarks.json
```

For deliberate publication work, `make reports-publish` regenerates the standard bundle in tracked `reports/`. Review those changes as new evidence; historical receipts retain their original source and result bindings.

## Reproduce the Lean checks

Lean setup is separate and downloads several GiB of pinned dependencies:

```sh
bash scripts/bootstrap_lean.sh
bash scripts/verify_lean.sh standalone
bash scripts/verify_lean.sh focused
```

The [claims and evidence ledger](docs/claims-and-evidence.md) and generated summary above bind each saved audit scope to its named declarations, source hashes, and receipt. The expanded default target includes the formerly separate component scopes and the proved sampler modules; its [current Linux receipt](formal/results/linux-focused-5b4af40/verification.json) binds the exact compiled target. Historical component receipts retain their original interfaces and must not be added again to the integrated audit count. Fresh compilation, dependency-cache reuse, and overlapping reproductions remain distinct. Saved historical receipts do not verify later source changes.

The [Linux](docs/linux-verification.md) and [native Windows](docs/windows-verification.md)
guides give the commands and exact verification scopes. Strict Comparator
verification remains open for the research sampler and original challenge;
only the separate [tiny fixture](formal/results/strict-comparator-smoke/README.md)
has passed the real sandbox, exporter, default kernel and comparison.

[Accelerated startup](research/strict-sampler-checkpoints/accelerated-plan-v1/)
now passes authentication and planning in an 8 GiB VM. A
[standalone metadata comparison](research/strict-sampler-checkpoints/snapshot-comparison-v1/)
measured 25.65 seconds for the original traversal and 0.198 seconds for a
candidate over all 131,021 admitted files; that candidate is not installed,
and the full proof run remains unexecuted. The [status](docs/status.md) and
[handoff](docs/handoff.md) retain prior failures, evidence boundaries and the
remaining runtime and checking obligations.

## A synthetic commuting example

Our entirely synthetic ten-worker commute example has 42 feasible tables. With exactly the same margins, bounds, and mileage assumptions, uniform aggregate tables give mean annual commute VMT of **18,700**, while conditional individual-worker assignments give about **16,158**. The feasible range, independent of either law, is **9,460–25,080**. These are model comparisons on invented data, not estimates for a real place.

Sparse support matters too: a six-cell cycle can connect a fiber that rectangle moves cannot. Equal weighting of all cycles slightly reduces the gap in the commuting fixture. Tuning the fixed probabilities reverses that result: rational certificates prove a gap improvement over 63% and beat every rectangle-only mixture on that fiber. Connectivity and proposal frequency both matter; this finite result does not establish a general mixing theorem.

For larger problems, the optimizer certifies both metric endpoints on a synthetic 300-destination case with more than 10²³⁶ feasible tables. A separate ordinary worker baseline samples a million-worker case and computes linear metric moments directly. These experiments have explicit work limits and specify different target laws where appropriate.

## Measured performance and public-data checks

On a 20×5 unrestricted table with one million workers, the simple Python urn sampler took **1.00353 seconds per table**, versus **26.40 microseconds** for SciPy Patefield in the retained [worker-library benchmark](docs/worker-library-benchmarks.md). These are median draw-phase times across three repetitions, with batches of two tables, for the same classical conditional-worker law. They measure those implementations on the recorded machine; they do not measure the uniform-table sampler or the `d¹⁷` inverse-gap result.

The [public LODES backtest](docs/commuting-backtest.md) scores 100 overlapping 2×2 cases from one released 2023 Rhode Island county origin–destination job table. Central 95% model intervals include the held-out published cell in **100/100** cases under uniform aggregate tables and **0/100** under the margin-only conditional-worker law. Mean widths are **7,912.36** and **124.64 jobs**, respectively. This descriptive comparison exposes the worker law's failure on that case frame and the uniform law's much wider intervals. The cases are dependent, the data count published jobs, and neither coverage figure establishes calibrated uncertainty or a validated commuting/VMT model.

## Scope

The source claim of exact expected-polynomial sampling concerns ordinary tables. Its companion FPRAS covers cell bounds and structural zeros. This project does not transfer one guarantee to the other. An exact dynamic program for a small bounded fiber does not supply a polynomial-time sampler for arbitrary binary-encoded inputs.

Uniform aggregate tables and conditional assignments of individual workers are different probability laws. Applications must specify their target law, reconcile input universes, and distinguish hard zeros from missing evidence. No private client data is included.

## Attribution

Original manuscripts and Lean library: OpenAI, pinned at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Initial review: GPT-6.1 Sol working with Ben Gould. Follow-up research, code, and review use OpenAI Codex agents under EcoDataLab's direction. AI-generated arguments are subject to the same reproducibility and review requirements as any contribution. See [NOTICE](NOTICE).

Apache-2.0. Community contributions are welcome through issues and pull requests.
