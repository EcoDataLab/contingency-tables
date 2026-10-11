# Contributor handoff

This stage leaves a checked mathematical and reference-algorithm core, reviewed measurements, and a complete bounded sampler integrated into the default target with fresh hosted Linux evidence. Start with the [claim ledger](claims-and-evidence.md), [formal verification record](formal-verification.md), and [research status](status.md). Their source-bound receipts determine the checked scope; a file's presence in the repository does not establish that it compiled or that its English claim was reviewed.

The original OpenAI source remains pinned at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Preserve its attribution, dependency pins, and historical receipts. Current research and the reviews labeled “independent” use separate AI agents reviewing AI-produced work within this project. Outside human MCMC, Lean, implementation, and application review is welcome. Native Windows checks used project-owned hardware; no outsider reproduction of those runs is claimed.

## What contributors can build on

| Result or tool | Law or quantity | Evidence and boundary |
| --- | --- | --- |
| Ideal auxiliary-chain bound | Inverse spectral gap at most `80,000d¹⁷`, with `d=10+(m+1)(n+1)` | Checked Lean statements cover ordinary equal-total natural margins and automatic branches. Exact completion is an oracle operation. This bounds the ideal chain, not full machine runtime. |
| Finite-word output law | Pointwise feasible output and total variation at most `2^-h` under uniform reserved bits | Checked typed-law and schedule components include zero margins and empty dimensions. This component uses noncomputable constructions; literal program identification has its own later research-overlay evidence. |
| Encoded completion and schedules | Output semantics and polynomial charged component costs | Checked components include dense draws, signed decoding, retries, physical-fiber interfaces, and numeric reservations under their stated hypotheses. The complete public-machine result has separate research-overlay evidence; its numerical runtime degree remains unknown. |
| [Complete bounded machine](outer-sampler-compiler-checkpoint.md) | Every-tape feasible output and TV at most `2^-h` within uniform polynomial time | Equal-total natural margins, including empty dimensions and zeros; numeric `h≥1`. Ordinary compilation passed. The complete compiled-environment audit passed. Fresh hosted Linux verification of the integrated target passed. Numerical exponent and strict replay remain open. |
| Python reference tools | Uniform aggregate tables; specified activity/factorial-weighted laws; law-independent metric extrema | Exact small-fiber DP, graph-block/cactus methods, certificate replay, and rational linear optimization have explicit work limits. They do not implement a universal polynomial-time uniform sampler. |
| Classical worker baseline | Unrestricted fixed-margin inverse-factorial law | Exact integer urn draws and full-covariance linear moments provide a reference conditional-independence model. This law differs from uniform aggregate tables and does not cover arbitrary caps, structural zeros, or interaction weights. |

The historical stage's ordinary aggregate audit passed with validated reused dependency objects and a freshly compiled aggregate root. The separate [compiled-environment audit](../formal/results/environment-aggregate-1236/README.md) passed and retains every selected theorem and all six headline dependency closures. Both checks trust their recorded compiler and dependency inputs; neither is strict kernel replay. Use the [ledger and receipt inventory](claims-and-evidence.md) for exact declaration counts, imported modules, hashes, axioms, and whether later source changes are covered. The [fresh Linux reproduction](../formal/results/linux-focused-df469a5/README.md) passed normal compilation, all 1,236 named audits, and the full environment audit at `df469a50e32c652093bac17a031b5c2ae6bd8af7`, tagged `verify-stage-final-2026-10-10`. Its source checkpoint is the earlier reproduction baseline. The [default-target integration](default-target-integration.md) now promotes the proved sampler sources into the standard workflow; the [expanded target passed fresh hosted Linux verification](../formal/results/linux-focused-5b4af40/README.md), including all 22 headline closures. The [earlier inventory-runner failure](../formal/results/linux-focused-cef573d-failure/README.md) and older Linux receipts retain their exact original outcomes and scopes.

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

## Proved checkpoint and frozen research

- [Complete bounded sampler](outer-sampler-compiler-checkpoint.md): the exact thirteen-source overlay, successful normal compiler receipts, statement map, and current environment-audit evidence. The original [source archive](../research/outer-sampler/) and all failed attempts remain preserved. The promoted default target passed fresh hosted Linux verification; the earlier aggregate and Linux receipts retain their original scopes.
- [Runtime degree](../research/runtime-degree/checkpoints/generic-helpers-v1/): seven exact helpers passed ordinary native compilation, with separate 47-name generic and 21-name arithmetic/scalar/seed audits. The compiler lift controls degree from supplied certificates for the actual complete count and draw routines; those two numerical certificates remain missing. The [composed complexity note](composed-complexity.md) records the conditional formula, and the [earlier archive](../research/runtime-degree/) retains its failed and uncompiled versions. No numerical complete sampler exponent is known.
- [Comparator serial work](../research/comparator-serial/): the archived offline tests are now complemented by a separate [strict tiny-fixture pass](../formal/results/strict-comparator-smoke/README.md), including real exporter and default-kernel acceptance. The package supplies the exact tested Linux entrypoint and environment requirements. It verifies the `True` fixture only; the original challenge and research sampler need their own runs. The [earlier full-challenge VM attempt](../formal/results/strict-comparator-vm-895b45c/README.md) remains a recorded memory failure before export. The separate [revised sampler challenge](../research/strict-sampler-challenge/) now fixes the public machine in an exact standalone statement. Native entrypoints and their named audit passed; its latest attempt passed installation and real sandbox probes, then failed authentication of Lake’s generated configuration cache before proof compilation. All three startup outcomes are preserved. The next narrow repair must bind configuration objects to pinned package sources and toolchain traces; no successor code or VM retry is part of this checkpoint.

The `d¹⁷` inverse-gap bound, the proved `S¹⁷⁰` reserved-bit/input allowance, and the symbolic complete machine-time degree are different quantities. Here `S=m+n+clog₂(M+1)+h+1`, with numeric precision `h`. The reserved-bit envelope is not measured work or a known machine-runtime exponent.

## Next round: ordered obligations and promotion evidence

1. **Reproduce the reviewed baseline.** The fresh Linux build, full offline collector validation and independent AI saved-artifact readback passed. The [completed review](../formal/results/linux-focused-5b4af40/review.json) and [22-headline statement index](../formal/results/linux-focused-5b4af40/headline-index.json) close the previously interrupted source/report/closure checks; the earlier failed reader remains recorded. The integration PR is unmerged. Start any reproduction from the exact tagged source and preserve imports, filters, statement types, transitive axioms, and source/object hashes. Only a receipt for the selected compiled environment supports an exhaustive-inventory claim; named rosters and source scans cannot.
2. **Review the mathematics against the interfaces.** Start with the ledger's ideal-chain and finite-word headline statements. Trace ordinary-margin assumptions through branch selection, state existence, completion accuracy at every physical state, and restarted output error, including empty and zero-margin cases. Promotion requires a mathematical review of those exact hypotheses and laws, alongside successful compiler receipts; a smaller exponent alone is insufficient.
3. **Reproduce and review the integrated sampler.** The expanded target has passed a fresh hosted Linux build, 1,511 named audits and the complete selected environment audit. Use its exact receipt and all 22 headline closures to review the path from parsed margins through fresh bits, both branches, retries, fallback and printed output. Any proof/configuration change needs a new result for its own bytes; historical receipts retain their scopes.
4. **Extract the numerical complete runtime degree.** Polynomial-time existence is proved for the compiled realization. Obtain explicit degrees and constants for its full work polynomial, retaining parsing, fresh random bits, all reserved trials, intermediate/output tree weights and physical-machine conversion. Use the [checked generic degree certificates](../research/runtime-degree/checkpoints/generic-helpers-v1/) with their actual codec, realizer and numeric-bit measures; do not substitute the failed historical drafts. Use the same complete program and public size measure throughout. `d¹⁷`, `S¹⁷⁰`, and symbolic compiler degrees cannot substitute for that derivation.
5. **Complete strict checking.** Reproduce the tested tiny fixture on a compatible Linux environment, then run the intended challenge separately with sufficient resources. The [revised sampler packet](../research/strict-sampler-challenge/) provides exact statement/solution sources, descriptor, input freeze, runtime authenticator and checking runner; its documented durable-supervision and full-replay gaps remain open. Preserve strict preflight and sandbox probes; start without submitted proof artifacts. A successful build must reach export and built-in-kernel comparison of those exact claims. The tiny-fixture pass establishes the checking pipeline only. Claim strict sampler acceptance only after its own complete successful log and scope-bound receipt exist.
6. **Validate application models and performance.** Before acquiring new data, freeze a new public state/year selection and score protocol; test laws that represent spatial association against held-out released joints. Report interval widths with coverage, dependence, source processing, and failure cases. Separately benchmark a completed sampler against methods for identical laws and constraints, retaining setup, memory, effective-sample/accuracy costs, and work-budget failures. Broader model-validity and performance claims require these new observations; the current worker-library timing and single-state backtest do not establish them.

Contributions can tackle one obligation at a time. State the quantity, target law, assumptions, source revision, and evidence class in the result itself; preserve negative results and earlier receipts. See [CONTRIBUTING](../CONTRIBUTING.md) for review and reproduction expectations.
