# Contingency tables: proofs and usable reference algorithms

An open EcoDataLab research project building on [OpenAI result #115](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/115.md): sampling and counting integer tables with fixed margins and cell bounds.

The first research checkpoint gives a conditional **O(d²⁵) bound on the ideal small-chain inverse spectral gap**, compared with the source's explicit O(d¹²⁶). It combines a sharper switching argument, localized transport energy, and smaller compatible scales. This is a manuscript-level deduction from specified upstream lemmas; the full modified sampler and its bit complexity have not been formally verified.

The repository also supplies exact bounded-table and weighted reference samplers, sparse-cycle diagnostics, and exact linear bounds with independently checkable certificates. These tools can test small climate-accounting and commuting examples without implementing the source's enormous universal schedules.

## What improved

| Result | Evidence and scope |
| --- | --- |
| Stronger small-entry probability bound | Elementary switching proof, independent AI review, and exhaustive finite checks; ordinary uniform tables only |
| Localized transport: O(d⁸⁵) at original scales | Global edge-ownership argument and sharper path/root/repair constants, conditional on the source lemmas |
| Smaller scales: O(d²⁵) ideal inverse gap | Complete manuscript scale audit and nine polynomial certificates valid for every d ≥ 14; full program integration remains open |
| Smaller accuracy and counting-estimator budgets | Exact integer/rational utilities, concentration and coupling derivations; changed-law tabulation and machine costs remain obligations |
| Lean transport refinements | Six standalone declarations and nine new integrated declarations compiled; standard-axiom audits passed, with two original transport declarations audited alongside them |
| Exact reference algorithms | Uniform and weighted small-fiber laws, structural zeros and lower bounds, resource-limit failures, and independent enumeration oracles |
| Exact feasible metric range | Rational min-cost flow with primal/dual and infeasibility-cut certificates; no table enumeration |

## Starting points

- [Original research review](115/115-contingency-tables-review.md) and [source manifest](115/source-manifest.json): the preserved October 8, 2026 handoff, including hypotheses to test.
- [Research status](docs/status.md): current results, limitations, and next proof obligations.
- [Transport proof](docs/transport-localization.md), [switching and scale proof](docs/scale-audit.md), [error budgets](docs/error-budgets.md), and [independent mathematical review](docs/independent-review.md).
- [Formal verification](docs/formal-verification.md): compiler outcomes, exact pins, and remaining integration work.
- [Reference sampler](docs/sampler.md), [linear bounds](docs/linear-bounds.md), and [independent implementation audit](docs/independent-implementation-review.md).
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

The archived audit needs NumPy; exact integer and rational checks are distinguished from floating-point spectral diagnostics. Source verification downloads only files in the pinned manifest and checks their Git blob hashes. It does not execute upstream code.

The [Python verification receipt](reports/checkpoint-verification.json) records 78 passing tests, independent audit results, the runtime environment, and SHA-256 hashes of the checked sources. [Lean receipts](formal/results/) record the separate formal checks.

Generate the research reports:

```sh
python3 experiments/scale_report.py --output reports/scale-certificates.json
python3 experiments/budget_report.py --output reports/budget-comparison.json
python3 examples/sparse_commute.py --spectral --output reports/sparse-commute.json
python3 examples/linear_metric_bounds.py --output reports/linear-bounds.json
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

The secure upstream Comparator requires Linux and additional tools; focused Lean compilation is a different verification level.

## A concrete CBEI example

Our entirely synthetic ten-worker commute example has 42 feasible tables. With exactly the same margins, bounds, and mileage assumptions, uniform aggregate tables give mean annual commute VMT of **18,700**, while conditional individual-worker assignments give about **16,158**. The feasible range, independent of either law, is **9,460–25,080**. These are model comparisons on invented data, not estimates for a real place.

Sparse support matters too: a six-cell cycle can connect a fiber that rectangle moves cannot. Yet adding more cycles slightly reduces the spectral gap in the connected commuting fixture. The reports retain this negative result; connectivity alone does not establish a faster sampler.

## Scope

The source claim of exact expected-polynomial sampling concerns ordinary tables. Its companion FPRAS covers cell bounds and structural zeros. This project does not transfer one guarantee to the other. An exact dynamic program for a small bounded fiber does not supply a polynomial-time sampler for arbitrary binary-encoded inputs.

Uniform aggregate tables and conditional assignments of individual workers are different probability laws. Applications must specify their target law, reconcile input universes, and distinguish hard zeros from missing evidence. No private client data is included.

## Attribution

Original manuscripts and Lean library: OpenAI, pinned at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Initial review: GPT-6.1 Sol working with Ben Gould. Follow-up research, code, and review use OpenAI Codex agents under EcoDataLab's direction. AI-generated arguments are subject to the same reproducibility and review requirements as any contribution. See [NOTICE](NOTICE).

Apache-2.0. Community contributions are welcome through issues and pull requests.
