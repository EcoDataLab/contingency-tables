# Replaying the public integration sources

The `integration-sampler` scope builds the public dependency closure for the
selected integration endpoints, including the complete reference experiment
and hybrid sampler. It reuses the existing verifier and public Lean sources.
Each attempt has a new output directory; earlier evidence is never replaced.

The default documented verification now runs both the preserved baseline and
this current research tree in one fresh attempt:

```sh
bash scripts/bootstrap_lean.sh
make lean
# Explicit fresh evidence location (must not already exist):
# bash scripts/verify_main.sh --serial .local/main-verification-example
```

Its `main-verification.json` records both stages. Success additionally requires
the d8, bounded-aspect squared and ordinary-program contract headlines in the
integration receipt. The historical baseline remains available as
`make lean-baseline`; bare `lake build Math115` remains that baseline library.
The main wrapper preserves existing source files and pins and uses the manifest
below rather than copying the research tree into another source directory.

To inspect or run the extension separately after the baseline is available:

Resolve the extension's source order without starting Lean, Lake or Git:

```sh
python3 research/repair-accept/verify.py --scope integration-sampler --plan
```

Then build the extension and audit the selected endpoint modules:

```sh
python3 research/repair-accept/verify.py --scope integration-sampler \
  --output .local/integration-sampler-fresh
```

Choose another output name for every subsequent run. `--lean PATH` overrides
the default pinned Lean binary. The source-only plan needs the bootstrapped
upstream/package sources and toolchain boundary, but does not require a
compiled baseline. The execution command requires the baseline build.

[The public manifest](integration-sampler.json) lists the additive module
sources, selected audit modules and headline names. The planner reads ordinary
Lean imports, separates the existing baseline closure, rejects missing or
unmapped research sources, and computes the extension's dependency order.
The execution compiles that order into one object tree seeded with baseline
links, so partial namespace roots do not hide one another. Dependencies are
built once; their individual packet audits are not rerun as bootstrap steps.
Additional checked endpoint sources can be added to the same manifest.
The current selection includes both general d8 and bounded-aspect squared
chain theorems, the complete ordinary-program contract and the separate checked
refinements. The manifest is authoritative for exact module and headline counts;
intermediate modules are compiled once and reached through endpoint closures.

The output retains `source-plan.json`, source/object compilation records,
diagnostics, the environment audit and imported-object inventory, and a new
`verification.json`. The audit selects the manifest's endpoint modules and
their complete headline dependency closures; it does not claim to enumerate
every declaration in every rebuilt research dependency. Pinned compiler,
bootstrap binaries and reused baseline/package imports remain trusted. This
is ordinary additive verification, separate from strict Comparator replay,
and establishes no new sampler runtime result.

Each module compilation has a 600-second allowance. The combined integration
audit has 1800 seconds; existing scopes retain their 600-second audit allowance.
On a stage timeout, partial stdout/stderr and a failed stage record are retained
without producing a passing verification receipt.

Implementation was checked with source planning and focused Python tests.
The expanded default entrypoint still requires its own fresh passing receipt;
individual packet audits and earlier narrower runs do not stand in for it.
