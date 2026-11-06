# Replaying the public integration sources

The `integration-sampler` scope builds the public dependency closure for the
selected integration endpoints, including the complete reference experiment
and hybrid sampler. It reuses the existing verifier and public Lean sources.
Each attempt has a new output directory; earlier evidence is never replaced.

From a fresh checkout, prepare the normal pinned toolchain, packages and
baseline first:

```sh
bash scripts/bootstrap_lean.sh
bash scripts/verify_lean.sh focused --serial
```

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
The current audit selections are `GeneralHybridSampler`,
`GeneralCorrectionCode`, `GeneralRawNeighbors`, `GeneralInitializationCode`,
and `GeneralJointCode`, with thirteen complete headline closures.

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
A complete fresh build through this new scope has not yet been run.
