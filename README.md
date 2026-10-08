# Contingency tables: proofs and usable reference algorithms

An open EcoDataLab research project building on [OpenAI result #115](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/115.md): sampling and counting integer tables with fixed margins and cell bounds.

The research gives sharp ordinary-table tail and mean bounds, compiled Lean proofs of those bounds and their padding application, and a conditional **O(d²⁵) bound on the ideal small-chain inverse spectral gap**, compared with the source's explicit O(d¹²⁶). The full modified sampler and its bit complexity have not been formally verified.

The repository also supplies exact reference samplers, certified cycle-mixture comparisons, linear bounds with checkable certificates, and a classical worker-allocation baseline with exact metric means and variances. The optimization and ordinary worker tools handle much larger synthetic cases than exhaustive table enumeration.

## What improved

| Result | Evidence and scope |
| --- | --- |
| Sharp small-entry tail and mean bounds | Actual-table Lean proofs of the survival product, its linear bound, and the mean bound; attaining examples and exact finite checks |
| Localized transport: O(d⁸⁵) at original scales | Global edge-ownership argument and sharper path/root/repair constants, conditional on the source lemmas |
| Smaller scales: O(d²⁵) ideal inverse gap | Actual padding-count theorem for U=64d⁵ and a smaller shape-aware threshold; full transport and program integration remain open |
| Limit of this padding construction | A counting argument forces U=Ω(Ln²) in a 2×n family if acceptance stays bounded away from zero |
| Smaller accuracy and counting-estimator budgets | Exact integer/rational utilities, concentration and coupling derivations; changed-law tabulation and machine costs remain obligations |
| Lean refinements | Quarter transport coefficient, retained leaf energy, actual widths and ownership, ordinary-table switching and tails, scale interfaces and padding count; exact audit scope in the verification ledger |
| Exact reference algorithms | Uniform and weighted small-fiber laws, structural zeros and lower bounds, resource-limit failures, and independent enumeration oracles |
| Exact feasible metric range | Rational min-cost flow with primal/dual and infeasibility-cut certificates; no table enumeration |
| Better fixed cycle mixtures | Exact certificates: over 63% larger gap on the 42-table fixture, beating every rectangle-only mixture; no general mixing or runtime claim |
| Ordinary worker baseline | Classical inverse-factorial law, exact integer draws, and full-covariance linear moments without sampling; excludes bounds and interaction weights |

## Starting points

- [Original research review](115/115-contingency-tables-review.md) and [source manifest](115/source-manifest.json): the preserved October 8, 2026 handoff, including hypotheses to test.
- [Research status](docs/status.md): current results, limitations, and next proof obligations.
- [Transport proof](docs/transport-localization.md), [switching and scale proof](docs/scale-audit.md), [error budgets](docs/error-budgets.md), and [independent mathematical review](docs/independent-review.md).
- [Sharp tail formalization](docs/small-entry-formalization.md), [actual padding bridge](docs/scale-formalization.md), [padding obstruction](docs/padding-barrier.md), and [second independent review](docs/second-checkpoint-review.md).
- [Formal verification](docs/formal-verification.md): compiler outcomes, exact pins, and remaining integration work.
- [Reference sampler](docs/sampler.md), [linear bounds](docs/linear-bounds.md), and [independent implementation audit](docs/independent-implementation-review.md).
- [Certified cycle mixtures](docs/cycle-mixtures.md), [ordinary worker baseline](docs/worker-baseline.md), and [larger synthetic commuting benchmarks](docs/commute-scaling.md).
- [CBEI and commuting applications](docs/cbei-use-cases.md): target laws, source reconciliation, and a public synthetic example.
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

The [Python verification receipt](reports/checkpoint-verification.json) records 128 passing tests, independent audit results, the runtime environment, and SHA-256 hashes of the checked sources. [Lean receipts](formal/results/) record the separate formal checks.

Generate the research reports:

```sh
python3 experiments/scale_report.py --output reports/scale-certificates.json
python3 experiments/budget_report.py --output reports/budget-comparison.json
python3 examples/sparse_commute.py --spectral --output reports/sparse-commute.json
python3 examples/linear_metric_bounds.py --output reports/linear-bounds.json
python3 experiments/padding_barrier.py --output reports/padding-barrier.json
python3 experiments/worker_baseline.py --output reports/worker-baseline.json
python3 experiments/commute_scaling.py --output reports/commute-scaling.json
python3 experiments/cycle_mixtures.py --replay reports/cycle-mixtures.json
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

The [manual Linux workflow](docs/linux-verification.md) separates focused proofs, the original full theorem build, and strict Comparator replay. The tested hosted runner lacks the sandbox ABI required for Comparator; focused Lean compilation is a different verification level.

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
