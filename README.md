# Contingency tables: proofs and usable reference algorithms

An open EcoDataLab research project building on [OpenAI result #115](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/115.md): sampling and counting integer tables with fixed margins and cell bounds.

The research now includes a **Lean-verified `80,000d¹⁷` inverse-gap bound for an actual ideal auxiliary chain**, where `d=10+(m+1)(n+1)`. It covers all ordinary equal-total margins through automatic branch selection and a proved state-existence construction. The [completion-oracle formalization](docs/completion-oracle-formalization.md) proves equal accepted representation counts, acceptance at least one quarter at `L=3d`, and bounded-retry output accuracy. The [dense completion proofs](docs/completion-dense-law.md) supply the accurate fine-table law from the pinned canonical sampler and assemble accurate completions at every physical state. The [encoded completion program](docs/completion-sampler-program.md) now has exact output semantics and a polynomial charged-cost proof for supplied Boolean input. The concrete encoded outer program and its complete machine cost remain open.

The output proof extends to finite walks from a known feasible table and identifies the actual proposal/draw/test law. With independent restarted attempts, [approximate completions](docs/physical-approximate-oracle.md) add at most `R(Tγζstep+ζterminal)` to the ideal error `exp(−R/S)+RB exp(−T/K)`, with `γ≤1/2`. Here `K=80,000d¹⁷`, `S=2(1+p²)`, and the [finite-walk guide](docs/physical-finite-walk.md) defines `B` and sufficient walk/retry schedules. The new dense-law specialization proves the required all-state accuracy, including the exact empty-block branch, and gives this finite-law output bound with a supplied feasible outer fallback.

The repository also supplies sharp ordinary-table tail and mean bounds, exact samplers for small or structurally decomposable fibers, certified cycle-mixture comparisons, linear bounds, and a classical worker-allocation baseline with exact metric moments. [Practical uses](docs/practical-use.md) explains which probability law and tool fit each problem. Competitiveness of the complete #115 sampler against established application software has not been demonstrated.

## What improved

| Result | Evidence and scope |
| --- | --- |
| Sharp small-entry tail and mean bounds | Actual-table Lean proofs of the survival product, its linear bound, and the mean bound; attaining examples and exact finite checks |
| Original ideal chains: O(d⁸⁵) inverse gap | Compiled physical path, exposure, and full-variance proofs give `1024d⁸⁵` for the literal source completion chain and `512d⁸⁵` for its all-small unit chain |
| Ideal-only chain: O(d¹⁷) inverse gap | `80,000d¹⁷` at `U=5d³, L=3d`; equal ordinary totals suffice, including empty dimensions; exact completion is an oracle operation |
| Dense-compatible chain: O(d²⁵) inverse gap | `128·47⁴d²⁵` at `U=47d⁵, L=32d³`; same automatic branch and feasibility coverage |
| Sharper physical repair | Square-root cross-term bound plus tighter polynomial arithmetic reduce the previous conservative chain coefficient eightfold |
| Stationary success and uniform output | Lean proofs give exact table mass `1/Z`, success `N/Z`, and an independent-retry error bound; ideal-scale success is at least `1/[2(1+p²)]` |
| Finite-walk output guarantee | Actual rational transition law, positive starting state, terminal completion, bounded retries, and explicit sufficient schedules for any positive TV-error target |
| Approximate completion interface | Lean identifies the actual proposal/draw/test law and bounds transition, terminal, and restarted-output error; holding proposals incur no completion error |
| Completion oracle at `L=3d` | Lean proves the full accepted-preimage count, geometric count comparison, quarter acceptance, and bounded-retry accuracy at `k=d¹²` |
| Canonical dense completion at every state | 66 Lean audits included in the focused aggregate discharge the fine-law accuracy premise, assemble the actual physical completion family, and prove its normalized outer-law error; encoded outer-program and runtime integration remain open |
| Encoded completion program | 46 additional isolated Lean audits connect the computed dense draws, signed decoder, retries, and computed fallback to the analyzed output law, with polynomial charged cost in the full supplied input |
| Computed physical completion bridges | 193 additional isolated Lean audits connect actual large-index lists and completion outputs to each physical fiber, identify computed proposal laws, and specialize finite-law schedules and empty completions; the full Boolean walker remains separate |
| Executable Boolean codec and retries | 25 Lean audits included in the focused aggregate identify the signed decoder and consecutive independent word bank with the retry law for a supplied fine draw; six native evaluations passed |
| Binary-list completion decoder | 52 Lean audits included in the focused aggregate prove exact decoding and polynomial charged machine cost in the binary input size; nine native boundary checks passed |
| Explicit error and random-bit schedules | 56 Lean audits included in the focused aggregate bound all four scalar errors and the entire reserved bit bank; connecting these schedules to the complete physical program remains separate |
| Encoded input and public-size bounds | 32 Lean audits included in the focused aggregate bound the reserved bank in the original sampling-size measure and give cost composition for a supplied polynomial-time realizer; precision is measured by numeric `h` |
| Limit of stationary rejection | A reviewed ideal-scale family has `p²s→1`, so the unchanged rule's quadratic stationary-trial cost is unavoidable in worst-case order; eight exact finite checks |
| Smaller padding threshold | Actual ordinary-table counts prove half unpadding acceptance at `U=47d⁵`, with a smaller shape-aware alternative |
| Limit of this padding construction | A counting argument forces U=Ω(Ln²) in a 2×n family if acceptance stays bounded away from zero |
| Smaller accuracy and counting-estimator budgets | Exact rational allocations and independent-block median schedules; transition allowances and observable-evaluation costs are reported separately |
| Lean verification | 869 integrated declaration audits: 863 focused and six standalone; 46 encoded-program and 193 physical-bridge audits remain separate, all using standard foundational axioms |
| Exact reference algorithms | Uniform and weighted small-fiber DP, cactus cycle coordinates, and graph-block factorization, with explicit work limits |
| Exact feasible metric range | Rational min-cost flow with primal/dual and infeasibility-cut certificates; no table enumeration |
| Better fixed cycle mixtures | Exact certificates: over 63% larger gap on the 42-table fixture, beating every rectangle-only mixture; no general mixing or runtime claim |
| Ordinary worker baseline | Classical inverse-factorial law, exact integer draws, and full-covariance linear moments without sampling; excludes bounds and interaction weights |
| Exact ideal-chain diagnostics | Executable bounded oracle, 18-case same-law benchmark, and an exact 2×2 obstruction: inverse gap grows at least as U² in this free-cutoff family |

## Starting points

- [Original research review](115/115-contingency-tables-review.md) and [source manifest](115/source-manifest.json): the preserved October 8, 2026 handoff, including hypotheses to test.
- [Research status](docs/status.md): current results, limitations, and next proof obligations.
- [Ideal-only scales and dense-interface limit](docs/ideal-oracle-scales.md), [sharper physical repair](docs/physical-repair-refinement.md), and [automatic branches and feasibility](docs/reduced-all-small-chain.md).
- [Stationary success and uniform output](docs/physical-stationary-success.md): completion counts, the exact output bijection, and independent stationary retries.
- [Finite walks and output error](docs/physical-finite-walk.md): the actual selected transition law, independent restarts, and sufficient walk/retry schedules.
- [Completion by dilation and rounding](docs/completion-oracle-dilation.md), its [finite-table and geometry proofs](docs/completion-oracle-formalization.md), and [approximate-oracle error propagation](docs/physical-approximate-oracle.md): the completion route at the smaller outer scales and its remaining program obligations.
- [Canonical dense completion laws](docs/completion-dense-law.md): the pinned dense draw, analytic premise discharge, all-state residual inputs, and instantiated outer probability law.
- [Encoded completion program](docs/completion-sampler-program.md): computed dense inputs, exact whole-word and prefix semantics, computed fallback, and polynomial charged cost.
- [Computed physical bridges](docs/completion-physical-bridges.md): actual list ordering, proposal laws, physical completion accuracy, finite-law schedules, and empty-block reconstruction.
- [Executable Boolean codec and retries](docs/completion-boolean-program.md): the additional signed decoder, independent word bank, frozen proof receipt, and native evaluations.
- [Binary-list completion decoder](docs/completion-list-decoder.md): exact encoded table semantics and a polynomial charged machine-cost proof for the decoder.
- [Explicit completion schedules](docs/completion-schedules.md): walk lengths, separate transition/terminal precisions, and a proved polynomial allowance for reserved random bits.
- [Completion input-size bounds](docs/completion-input-size.md): binary margin encodings, the public sampling-size measure, and generic deterministic cost composition.
- [Stationary-rejection obstruction](docs/stationary-success-obstruction.md): why the extra defect mass can force quadratic retries even when ordinary unpadding always succeeds.
- [Dense-compatible ideal chain](docs/reduced-small-chain.md), [original-chain comparison](docs/small-chain-gap.md), and [sequential padding](docs/sequential-padding.md).
- [Transport proof](docs/transport-localization.md), [switching and scale proof](docs/scale-audit.md), [error budgets](docs/error-budgets.md), and [independent mathematical review](docs/independent-review.md).
- [Sharp tail formalization](docs/small-entry-formalization.md), [actual padding bridge](docs/scale-formalization.md), [padding obstruction](docs/padding-barrier.md), and [second independent review](docs/second-checkpoint-review.md).
- [Formal verification](docs/formal-verification.md): compiler outcomes, exact pins, and remaining integration work.
- [Third independent review](docs/third-checkpoint-review.md), [fourth review](docs/fourth-checkpoint-review.md), and [defect-transport research](docs/defect-transport-research.md): checked improvements and limits of the current repair method.
- [Reference sampler](docs/sampler.md), [linear bounds](docs/linear-bounds.md), and [independent implementation audit](docs/independent-implementation-review.md).
- [Cactus sampler](docs/cactus-sampler.md), [graph-block sampler](docs/block-sampler.md), and [correlated-observation budgets](docs/block-budgets.md).
- [Certified cycle mixtures](docs/cycle-mixtures.md), [ordinary worker baseline](docs/worker-baseline.md), and [larger synthetic commuting benchmarks](docs/commute-scaling.md).
- [CBEI and commuting applications](docs/cbei-use-cases.md): target laws, source reconciliation, and a public synthetic example.
- [Executable ideal chain](docs/ideal-chain-experiment.md), [same-law sampling benchmarks](docs/sampler-benchmarks.md), [exact 2×2 analysis](docs/ideal-two-by-two.md), and [fifth independent review](docs/fifth-checkpoint-review.md).
- [Contributing](CONTRIBUTING.md): welcome to mathematical corrections, counterexamples, formal proofs, implementations, and reproducible benchmarks.

## Reproduce

Python 3.10 or newer is required. The core reference implementation uses the standard library.

```sh
python3 -m pip install -e '.[research]'
python3 -m unittest discover -s tests -v
python3 115/audit115.py --output /tmp/audit115-rerun.json
python3 experiments/independent_crosscheck.py
python3 scripts/verify_sources.py
```

The archived audit and numerical mixture search need NumPy. Saved mixture certificates replay using only exact standard-library arithmetic. Source verification downloads only files in the pinned manifest and checks their Git blob hashes. It does not execute upstream code.

The current [completion aggregate](formal/results/completion-aggregate/verification.json) passed **869 Lean declaration audits: 863 focused plus six standalone**. It integrates 231 previously isolated declarations across nine modules into the default focused target. The encoded completion program's 46 audits and the [physical bridges' 193 audits](formal/results/completion-physical-bridges/verification.json) remain separate. These scopes contain disjoint named declarations. The aggregate reused validated dependency objects; fresh Linux verification of this expanded scope remains pending.

The historical eighth checkpoint passed **638 Lean declaration audits**, adding 212 declarations across nine modules. The unchanged Python sources retain the seventh checkpoint's **237 passing tests**; source-hash continuity was checked again. The [Python receipt](reports/checkpoint-verification.json) and [Lean receipts](formal/results/) record environments, source hashes, and exact scope.

Generate the research reports:

```sh
python3 experiments/scale_report.py --output reports/scale-certificates.json
python3 experiments/budget_report.py --output reports/budget-comparison.json
python3 examples/sparse_commute.py --spectral --output reports/sparse-commute.json
python3 examples/linear_metric_bounds.py --output reports/linear-bounds.json
python3 experiments/padding_barrier.py --output reports/padding-barrier.json
python3 experiments/padding_growth.py --output reports/padding-growth.json
python3 experiments/block_budget_report.py --output reports/block-budget-comparison.json
python3 examples/cactus_commute.py --output reports/cactus-commute.json
python3 examples/block_factorization.py --output reports/block-factorization.json
python3 experiments/worker_baseline.py --output reports/worker-baseline.json
python3 experiments/commute_scaling.py --output reports/commute-scaling.json
python3 experiments/cycle_mixtures.py --replay reports/cycle-mixtures.json
python3 experiments/ideal_two_by_two.py --output reports/ideal-two-by-two.json
python3 experiments/stationary_success.py --output reports/stationary-success.json
python3 experiments/lattice_completion.py --output reports/lattice-completion.json
python3 experiments/sampler_benchmarks.py --draws 500 --warmup 200 --repetitions 2
```

For a first API example:

```python
from contingency115.tables import TableProblem, ExactTableSampler

problem = TableProblem([2, 2], [2, 2])
sampler = ExactTableSampler(problem)
assert sampler.count() == 3
table = sampler.sample()
assert sampler.unrank(sampler.rank(table)) == table
```

Lean setup is separate and downloads several GiB of pinned dependencies:

```sh
bash scripts/bootstrap_lean.sh
bash scripts/verify_lean.sh standalone
bash scripts/verify_lean.sh focused
```

The [Linux verification record](docs/linux-verification.md) includes an independent focused build at `0aa5a61`, with all 632 checkpoint-8 focused audits passing and 73 recorded source hashes matched to that commit. It covers the finite-table geometry, quarter acceptance, and conditional completion accuracy. A separate full original-theorem build at `5e5d6ef` audited all three original exports. Thor also reproduced the earlier `b14082b` checkpoint: 128 tests, 100 focused modules, and 68 audits. Strict Comparator replay remains unavailable on the tested hosted runner because its sandbox ABI is too old; no Comparator pass is claimed.

## A concrete CBEI example

Our entirely synthetic ten-worker commute example has 42 feasible tables. With exactly the same margins, bounds, and mileage assumptions, uniform aggregate tables give mean annual commute VMT of **18,700**, while conditional individual-worker assignments give about **16,158**. The feasible range, independent of either law, is **9,460–25,080**. These are model comparisons on invented data, not estimates for a real place.

Sparse support matters too: a six-cell cycle can connect a fiber that rectangle moves cannot. Equal weighting of all cycles slightly reduces the gap in the commuting fixture. Tuning the fixed probabilities reverses that result: rational certificates prove a gap improvement over 63% and beat every rectangle-only mixture on that fiber. Connectivity and proposal frequency both matter; this finite result does not establish a general mixing theorem.

For larger problems, the optimizer certifies both metric endpoints on a synthetic 300-destination case with more than 10²³⁶ feasible tables. A separate ordinary worker baseline samples a million-worker case and computes linear metric moments directly. These experiments have explicit work limits and specify different target laws where appropriate.

## Scope

The source claim of exact expected-polynomial sampling concerns ordinary tables. Its companion FPRAS covers cell bounds and structural zeros. This project does not transfer one guarantee to the other. An exact dynamic program for a small bounded fiber does not supply a polynomial-time sampler for arbitrary binary-encoded inputs.

Uniform aggregate tables and conditional assignments of individual workers are different probability laws. Applications must specify their target law, reconcile input universes, and distinguish hard zeros from missing evidence. No private client data is included.

## Attribution

Original manuscripts and Lean library: OpenAI, pinned at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Initial review: GPT-6.1 Sol working with Ben Gould. Follow-up research, code, and review use OpenAI Codex agents under EcoDataLab's direction. AI-generated arguments are subject to the same reproducibility and review requirements as any contribution. See [NOTICE](NOTICE).

Apache-2.0. Community contributions are welcome through issues and pull requests.
