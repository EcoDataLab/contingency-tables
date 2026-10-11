# Contingency tables: proofs and reference algorithms

An open EcoDataLab research project building on [OpenAI result #115](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/115.md). A contingency table allocates integer counts while preserving row and column totals. This repository studies mathematical guarantees and supplies exact reference tools for small or structured problems.

The [complete bounded-sampler research checkpoint](docs/outer-sampler-compiler-checkpoint.md) now connects the smaller `80,000d¹⁷` ideal-chain schedule to a fixed public machine. For equal-total natural margins and precision `h≥1`, its theorem gives feasible output on every random tape and total variation error at most `2^-h` within uniformly polynomial time. The supporting Lean modules and complete compiled-environment audit passed. The numerical full runtime exponent and practical speed remain unknown.

The [default-target integration](docs/default-target-integration.md) imports those exact proved sources into the standard verification workflow. The expanded target passed [fresh hosted Linux verification](formal/results/linux-focused-5b4af40/README.md) at `5b4af40`: ordinary compilation, the focused named audit, and all 22 headline dependency closures. The cards below bind the current source to that receipt.

A separate [quantitative-helper checkpoint](research/runtime-degree/checkpoints/generic-helpers-v1/) supplies compiled compiler and arithmetic degree bounds. The newer [affine public-degree refinement](research/runtime-degree/checkpoints/affine-public-sampler-degree-v1/) sharpens the conditional runtime degree for the same fixed machine to `340·max(max(e,6),t)`, where `e` and `t` certify the complete reserved-bit-count and supplied-word draw realizers. Computing the bit count may be expensive, but the generated word remains affine in input size plus numeric bit count; its size does not inherit that computation's work degree. Ordinary native compilation, named axiom checks, and independent AI review of the saved artifacts passed. Numerical `e` and `t` remain unresolved, and no practical speedup follows. The [earlier multiplicative bound](research/runtime-degree/checkpoints/public-sampler-degree-v1/) and its evidence remain preserved. The [strict sampler challenge](research/strict-sampler-challenge/) exposes the exact machine statement and checking inputs; its native checks passed, while full Comparator acceptance remains pending.

<!-- BEGIN GENERATED CLAIMS -->

| Claim | Quantity and evidence | Assumptions and present limit |
|---|---|---|
| [Ideal auxiliary chain](docs/claims-and-evidence.md#ideal-inverse-gap) | Inverse spectral gap ≤ 80,000d¹⁷; lean theorem | Equal-total natural margins; finite index sets; d=10+(m+1)(n+1). Ideal completion transitions; a step count does not give machine runtime. |
| [Complete bounded sampler](docs/claims-and-evidence.md#complete-bounded-sampler) | Every-tape time ≤ C Sᴰ; total variation ≤ 2⁻ʰ; lean theorem | Any finite dimensions m,n and natural margins r:Fin m→ℕ,c:Fin n→ℕ with equal ordinary totals; zero margins and empty dimensions are included. Numeric precision h≥1; M=∑ᵢrᵢ and S=m+n+clog₂(M+1)+h+1. One fixed machine and natural C>0,D apply uniformly to all inputs. Accuracy uses independent uniform fair bits; feasibility holds for every tape. The numerical complete runtime degree D has not been extracted; d¹⁷ is an inverse-gap power and S¹⁷⁰ bounds reserved bits/input size, not complete machine time. Practical sampler performance and strict Comparator acceptance of this sampler remain unknown. This bounded near-uniform theorem supplies no exact-sampling or counting extension. |
| [Finite-word probability law](docs/claims-and-evidence.md#finite-word-law) | Total variation ≤ 2⁻ʰ; lean theorem | Equal-total natural margins, including zero margins and empty dimensions; uniform reserved bits. This typed-law statement alone does not identify a literal encoded outer walker; the complete-machine claim has its own named and dependency-closure checks. |
| [Encoded completion and schedule](docs/claims-and-evidence.md#component-cost) | Polynomial charged component cost; lean component cost | Completion: d≥14, equal totals, dimension/free-coordinate bounds, dense margins; supplied finite word. Schedule: encoded margins and precision input. These component statements do not give the complete public machine's numerical runtime exponent. |
| [Executable references](docs/claims-and-evidence.md#executable-references) | Exact finite experiments; scope-specific measured timings; executable reference | Finite instances and each experiment’s stated target law and constraints. Enumeration grows rapidly; experiments do not prove general mixing or polynomial runtime. |

Saved receipt scopes (counts are distinct named audit requests, not exhaustive theorem totals):

- [Current integrated bounded-sampler Linux verification](formal/results/linux-focused-5b4af40/verification.json): **1511** named declarations; exact commit `5b4af40`. Exact-commit hosted Linux focused 1511 named replay and fresh compiled-environment audit. No separate standalone named audits, Comparator or new runtime result.

Historical component receipts are preserved in the [ledger](claims.json); their named declarations overlap the current integrated aggregate and are not added to it. The historical Linux focused run is a separate reproduction scope. Compiled-environment audit status is reported separately in [formal verification](docs/formal-verification.md); these counts describe saved named audits. Pinned upstream sources are checked when present; absent checkout files are explicitly reported as unchecked by the ledger JSON output.

<!-- END GENERATED CLAIMS -->

## Review and reproduction

Research, implementations, and the reviews labeled “independent” were produced by OpenAI Codex agents under EcoDataLab's direction. Those reviews use separate AI agents to examine AI-produced work. They provide another check, but no outside human MCMC or Lean review is claimed. We invite human reviewers to examine the Markov-chain arguments, formal theorem interfaces, executable semantics, and benchmark design; [contributing guidance](CONTRIBUTING.md) explains the evidence to include.

The native Windows checks were run on project-owned hardware by the same AI-assisted workflow. No outsider reproduction of those runs is recorded. Hosted Linux CI provides a fresh compilation environment, with the trust and scope limits described below. Compiler success establishes the checked Lean statements under their hypotheses and trusted dependencies; it does not establish scientific validity of a commuting model.

## What the research establishes

The ideal-chain bound covers all ordinary equal-total margins, including empty dimensions. The [completion-oracle proofs](docs/completion-oracle-formalization.md) establish equal accepted representation counts, acceptance at least one quarter at `L=3d`, and bounded-retry accuracy. The [dense completion proofs](docs/completion-dense-law.md) construct accurate completion laws at every physical state. The [finite-walk guide](docs/physical-finite-walk.md) connects those laws to restarted output-error bounds, and the [Boolean-law checkpoint](docs/completion-boolean-schedule.md) removes the supplied feasible fallback at the level of the typed finite-word law.

The historical default aggregate integrated the encoded-completion, physical-bridge, and both-branch Boolean-law/schedule proofs. Its [stage receipt](formal/results/completion-aggregate-1236/verification.json) binds the selected audits and authenticated object reuses. The [compiled-environment audit](formal/results/environment-aggregate-1236/README.md) enumerates the selected theorem environment and all six headline dependency closures; its totals include pinned upstream declarations. The [fresh Linux reproduction at `df469a5`](formal/results/linux-focused-df469a5/README.md) passed the complete focused workflow, with official dependency caches trusted. The [earlier runner failure](formal/results/linux-focused-cef573d-failure/README.md) remains preserved.

Subsequent repairs to the literal outer sampler are tracked in one [compiler checkpoint](docs/outer-sampler-compiler-checkpoint.md), with exact attempted sources, successful module checks, and retained failures. These results have a separate receipt scope from the earlier default aggregate and its Linux reproduction. The original [outer-sampler archive](research/outer-sampler/) remains unchanged. All thirteen research modules now pass ordinary Lean compilation, including the fixed public machine, final bounded-sampling theorem, and supplied-word cost bound. The audit records exact statement types, axioms and all 22 headline dependency closures. The [publication review](formal/results/native-sampler-checkpoint-publication-review.json) binds the released sources, audit report, and statement readback. The numerical complete runtime degree remains unknown. The expanded default target has now passed its fresh hosted Linux build and environment audit. Strict sampler replay remains pending. The [composed complexity review](docs/composed-complexity.md) separates the inverse-gap and reserved-bit powers from the unknown numerical full machine-time exponent; no application-speed claim follows from these bounds.

Other results include sharp ordinary-table tail and mean bounds, a dense-compatible `128·47⁴d²⁵` inverse-gap bound, padding and rejection obstructions, exact small-fiber samplers, graph-block and cactus methods, certified cycle mixtures, and a classical worker-allocation baseline. [Practical uses](docs/practical-use.md) explains which probability law and tool fit a problem. The [status ledger](docs/status.md) records the detailed proof obligations.

## Starting points

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
- [Mature worker-law libraries](docs/worker-library-benchmarks.md): measured Python, SciPy, and R comparisons on the same classical law.
- [Composed complexity](docs/composed-complexity.md): source-level cost accounting and the remaining unknown full machine-time exponent.
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
python3 115/audit115.py --output /tmp/audit115-rerun.json
python3 experiments/independent_crosscheck.py --output /tmp/independent-crosscheck.json
python3 scripts/verify_sources.py
```

Saved mixture certificates replay using exact standard-library arithmetic. Source verification downloads only files in the pinned manifest and checks their Git blob hashes; it does not execute upstream code. The [Python release receipt](reports/stage-close-verification.json) records the tested source hashes, optional dependencies, full verification command, and clean public-source archive run. It also preserves the hosted clean-checkout failure that led to the ledger fix. The [hosted Python receipt](reports/hosted-final-stage.json) records successful checks on Python 3.10, 3.12, and 3.13 at `df469a5`. The [environment-runner repair receipt](reports/environment-runner-fix/verification.json) records its local full-suite result and separate AI review. The [earlier stage receipt](reports/stage-verification.json) and [checkpoint receipt](reports/checkpoint-verification.json) retain their historical scopes.

For a first API example:

```python
from contingency115.tables import TableProblem, ExactTableSampler

problem = TableProblem([2, 2], [2, 2])
sampler = ExactTableSampler(problem)
assert sampler.count() == 3
table = sampler.sample()
assert sampler.unrank(sampler.rank(table)) == table
```

Generate new report copies under the ignored local directory:

```sh
mkdir -p .local/reports
python3 experiments/scale_report.py --output .local/reports/scale-certificates.json
python3 experiments/budget_report.py --output .local/reports/budget-comparison.json
python3 examples/sparse_commute.py --spectral --output .local/reports/sparse-commute.json
python3 examples/linear_metric_bounds.py --output .local/reports/linear-bounds.json
python3 experiments/padding_barrier.py --output .local/reports/padding-barrier.json
python3 experiments/padding_growth.py --output .local/reports/padding-growth.json
python3 experiments/block_budget_report.py --output .local/reports/block-budget-comparison.json
python3 examples/cactus_commute.py --output .local/reports/cactus-commute.json
python3 examples/block_factorization.py --output .local/reports/block-factorization.json
python3 experiments/worker_baseline.py --output .local/reports/worker-baseline.json
python3 experiments/commute_scaling.py --output .local/reports/commute-scaling.json
python3 experiments/cycle_mixtures.py --replay reports/cycle-mixtures.json
python3 experiments/ideal_two_by_two.py --output .local/reports/ideal-two-by-two.json
python3 experiments/stationary_success.py --output .local/reports/stationary-success.json
python3 experiments/lattice_completion.py --output .local/reports/lattice-completion.json
python3 experiments/sampler_benchmarks.py --draws 500 --warmup 200 --repetitions 2
```

## Reproduce the Lean checks

Lean setup is separate and downloads several GiB of pinned dependencies:

```sh
bash scripts/bootstrap_lean.sh
bash scripts/verify_lean.sh standalone
bash scripts/verify_lean.sh focused
```

The [claims and evidence ledger](docs/claims-and-evidence.md) and generated summary above bind each saved audit scope to its named declarations, source hashes, and receipt. The expanded default target includes the formerly separate component scopes and the proved sampler modules; its [current Linux receipt](formal/results/linux-focused-5b4af40/verification.json) binds the exact compiled target. Historical component receipts retain their original interfaces and must not be added again to the integrated audit count. Fresh compilation, dependency-cache reuse, and overlapping reproductions remain distinct. Saved historical receipts do not verify later source changes.

The [Linux verification guide](docs/linux-verification.md) and [native Windows guide](docs/windows-verification.md) retain checkpoint scopes, exact commands, and receipts. Strict Comparator verification remains open for the research sampler and original three-theorem challenge. A separate [tiny `True` fixture](formal/results/strict-comparator-smoke/README.md) passed the actual sandbox, serial builds, exporter, default Lean kernel, and comparison; its tested Linux entrypoint and evidence are public. The [earlier full-challenge VM attempt](formal/results/strict-comparator-vm-895b45c/README.md) exhausted its 4 GiB memory allowance before export and remains recorded as failed. The [Comparator serial archive](research/comparator-serial/) retains its earlier offline scheduling tests, and the [runtime-degree archive](research/runtime-degree/) retains its historical diagnostic statuses. The later [seven-helper checkpoint](research/runtime-degree/checkpoints/generic-helpers-v1/) has separate successful compilation and audit evidence. The [strict sampler challenge](research/strict-sampler-challenge/) preserves its initial provisioning and configuration-authentication failures. A [tested configuration repair](research/strict-sampler-checkpoints/configuration-repair-v1/) passed that configuration check, then stopped at an unnamed import-cache directory before proof compilation. A [later partial cache observation](research/strict-sampler-checkpoints/cache-observation-v1/) identifies the missing `Cli/.lake` ancestor; its file-count limit prevented the remaining cache and required-object checks. Complete failure evidence and reproduction limits are retained. See the [current status](docs/status.md) and [handoff](docs/handoff.md) for the remaining obligations.

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
