# Contributor handoff

This stage leaves a checked mathematical and reference-algorithm core, reviewed measurements, and frozen research drafts. Start with the [claim ledger](claims-and-evidence.md), [formal verification record](formal-verification.md), and [research status](status.md). Their source-bound receipts determine the checked scope; a file's presence in the repository does not establish that it compiled or that its English claim was reviewed.

The original OpenAI source remains pinned at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Preserve its attribution, dependency pins, and historical receipts. Current research and the reviews labeled “independent” use separate AI agents reviewing AI-produced work within this project. Outside human MCMC, Lean, implementation, and application review is welcome. Native Windows checks used project-owned hardware; no outsider reproduction of those runs is claimed.

## What contributors can build on

| Result or tool | Law or quantity | Evidence and boundary |
| --- | --- | --- |
| Ideal auxiliary-chain bound | Inverse spectral gap at most `80,000d¹⁷`, with `d=10+(m+1)(n+1)` | Checked Lean statements cover ordinary equal-total natural margins and automatic branches. Exact completion is an oracle operation. This bounds the ideal chain, not full machine runtime. |
| Finite-word output law | Pointwise feasible output and total variation at most `2^-h` under uniform reserved bits | Checked typed-law and schedule components include zero margins and empty dimensions. The typed law uses noncomputable constructions; it does not identify a complete literal encoded outer sampler. |
| Encoded completion and schedules | Output semantics and polynomial charged component costs | Checked components include dense draws, signed decoding, retries, physical-fiber interfaces, and numeric reservations under their stated hypotheses. Complete outer-program identification and full public-machine costs remain separate. |
| Python reference tools | Uniform aggregate tables; specified activity/factorial-weighted laws; law-independent metric extrema | Exact small-fiber DP, graph-block/cactus methods, certificate replay, and rational linear optimization have explicit work limits. They do not implement a universal polynomial-time uniform sampler. |
| Classical worker baseline | Unrestricted fixed-margin inverse-factorial law | Exact integer urn draws and full-covariance linear moments provide a reference conditional-independence model. This law differs from uniform aggregate tables and does not cover arbitrary caps, structural zeros, or interaction weights. |

The stage's ordinary aggregate audit passed with validated reused dependency objects and a freshly compiled aggregate root. The separate [compiled-environment audit](../formal/results/environment-aggregate-1236/README.md) passed and retains every selected theorem and all six headline dependency closures. Both checks trust their recorded compiler and dependency inputs; neither is strict kernel replay. Use the [ledger and receipt inventory](claims-and-evidence.md) for exact declaration counts, imported modules, hashes, axioms, and whether later source changes are covered. The [first fresh Linux attempt](../formal/results/linux-focused-cef573d-failure/README.md) passed the normal build and 1,236 named audits, then failed before the environment audit on an unused absent Lake library directory. Its failed outcome is preserved. A [fresh rerun at `df469a5`](https://github.com/EcoDataLab/contingency-tables/actions/runs/38030825047) checks the reviewed runner repair with unchanged proof sources; assess its final outcome and artifacts before claiming complete workflow success. Older Linux receipts retain their historical scope.

## What was measured

The [worker-library benchmark](worker-library-benchmarks.md) compares the same classical conditional-worker law in the Python urn, SciPy, and R. At 20×5 and one million workers, median draw-phase times were **1.00353 seconds per table** for the urn and **26.40 microseconds** for SciPy Patefield, across three repetitions with two-table batches. The report separates setup, warmup, validation, and process overhead and retains method crossovers and skipped cases. These timings do not measure the `d¹⁷` chain or a complete uniform-table sampler.

The [public LODES backtest](commuting-backtest.md) uses 100 predefined overlapping 2×2 cases from one released 2023 Rhode Island county origin–destination job table. Central 95% model intervals include the held-out published cell in **100/100** cases under uniform aggregate tables and **0/100** under the margin-only conditional-worker law. Mean widths are **7,912.36** and **124.64 jobs**. This is a descriptive failure of the worker law on that case frame, with much wider uniform intervals; the cases are dependent and the counts are processed public jobs. It supplies no calibration guarantee, mode-choice validation, or VMT/emissions estimate.

The [synthetic commuting example](commuting-use-cases.md) separately illustrates exact allocation laws and metric arithmetic on invented controls. The [same-law sampler benchmark](sampler-benchmarks.md) retains finite-chain correlation and budget failures. Keep these evidence classes separate when choosing a method.

## Reproduce from the public checkout

Use Python 3.10 or newer. From the repository root, the core suite runs without installing the package:

```sh
make test
# Equivalent source-only route without Make:
PYTHONPATH=src python3 -m unittest discover -s tests -v
```

Save rerun outputs separately from the published reports:

```sh
mkdir -p .local/reports
PYTHONPATH=src python3 -S experiments/cycle_mixtures.py --replay reports/cycle-mixtures.json
python3 experiments/commuting_backtest.py --output .local/reports/commuting-backtest.json
python3 scripts/claims_ledger.py --check-readme
python3 scripts/verify_sources.py --bundle-only
```

The default commuting replay is offline. Its additional `--verify-source` check downloads the fixed public sources and rejects changed bytes. The [backtest guide](commuting-backtest.md) explains the optional SciPy endpoint crosscheck. Follow the [library benchmark recipe](worker-library-benchmarks.md) for its pinned optional dependencies, timing phases, and bounded reruns. NumPy-dependent archived audits and other research reports require the `.[research]` extra described in the [README](../README.md).

For ordinary Lean verification, use the pinned repository workflow in an exclusive checkout:

```sh
bash scripts/bootstrap_lean.sh
bash scripts/verify_lean.sh standalone
bash scripts/verify_lean.sh focused --serial
```

Bootstrap downloads several GiB of dependencies. Serial mode controls concurrent project builds; it does not bound one compiler's memory. Preserve the complete logs, ordered axiom reports, source/object digests, dependency pins, and exact commit. The [Linux](linux-verification.md) and [Windows](windows-verification.md) guides describe platform-specific procedures and trust assumptions. Ordinary compilation is not strict Comparator replay.

## Frozen research, outside the checked core

- [Outer sampler](../research/outer-sampler/): the final attempted literal-program sources and errors are retained for resumption. Their output-law, executable realization, and complete cost claims require successful exact-source compilation and review before promotion. Read the archive's final attempt record before making another repair.
- [Runtime degree](../research/runtime-degree/): TreeDegree diagnostics passed; the PolynomialCompilerDegree diagnostic failed, and fresh-bit/finite-word work remains uncompiled. The [composed complexity note](composed-complexity.md) preserves the symbolic argument and its hypotheses. No numerical complete runtime exponent is known.
- [Comparator serial work](../research/comparator-serial/): 33 offline orchestration tests and 16 planner tests passed for the proposed scheduling route; no real Linux runtime result for that route is supplied. The [strict VM attempt](../formal/results/strict-comparator-vm-895b45c/README.md) passed actual ABI-11 sandbox preflight but exhausted memory before comparison. It produced no candidate export or kernel result.

The `d¹⁷` inverse-gap bound, the proposed `S¹⁷⁰` reserved-bit/input allowance, and the symbolic complete machine-time degree are different quantities. Here `S=m+n+clog₂(M+1)+h+1`, with numeric precision `h`. The reserved-bit envelope is not measured work or a known machine-runtime exponent.

## Next round: ordered obligations and promotion evidence

1. **Reproduce the verification baseline.** Start from the frozen release source and its checked root, standalone, and compiled-environment receipts. Inspect the fresh Linux result for its exact commit; reproduce any scope needed for a proposed change. Retain exact imports, filters, statement types, transitive axioms, and source/object hashes. Only a receipt for the selected compiled environment can support an exhaustive-inventory claim; named audit rosters and source scans cannot.
2. **Review the mathematics against the interfaces.** Start with the ledger's ideal-chain and finite-word headline statements. Trace ordinary-margin assumptions through branch selection, state existence, completion accuracy at every physical state, and restarted output error, including empty and zero-margin cases. Promotion requires a mathematical review of those exact hypotheses and laws, alongside successful compiler receipts; a smaller exponent alone is insufficient.
3. **Finish literal machine realization.** Reproduce the first unresolved error in the frozen outer-sampler archive, then resolve one interface at a time in an isolated candidate. Connect parsed margins, proposal choices, completion words, transitions, terminal trials, fallback, and encoded output to the checked law. Promotion requires exact-source compilation without admissions, axiom audits, output-law correspondence, and boundary checks for the literal public input/output program. Until then, the complete sampler remains research.
4. **Determine complete runtime accounting.** Start from the compiled realization's full work polynomial, retaining parsing, fresh random bits, all reserved trials, intermediate/output tree weights, and physical-machine conversion. Compile and review the frozen fresh-bit and compiler-degree proposals before using them. A numerical runtime exponent requires explicit polynomial degrees and constants for this same complete program in one public size measure. `d¹⁷`, `S¹⁷⁰`, and symbolic compiler degrees cannot substitute for that derivation.
5. **Complete strict checking.** First test the archived serial route on an adequately provisioned fresh Linux environment using the actual pinned tools. Preserve strict preflight and sandbox probes; start without submitted proof artifacts. A successful build must then reach export and built-in-kernel comparison of the exact intended claims. Promote strict verification only after the complete successful log and scope-bound receipt exist. Planner tests, ordinary Lean passes, and sandbox readiness are insufficient.
6. **Validate application models and performance.** Before acquiring new data, freeze a new public state/year selection and score protocol; test laws that represent spatial association against held-out released joints. Report interval widths with coverage, dependence, source processing, and failure cases. Separately benchmark a completed sampler against methods for identical laws and constraints, retaining setup, memory, effective-sample/accuracy costs, and work-budget failures. Broader model-validity and performance claims require these new observations; the current worker-library timing and single-state backtest do not establish them.

Contributions can tackle one obligation at a time. State the quantity, target law, assumptions, source revision, and evidence class in the result itself; preserve negative results and earlier receipts. See [CONTRIBUTING](../CONTRIBUTING.md) for review and reproduction expectations.
