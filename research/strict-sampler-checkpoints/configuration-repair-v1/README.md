# Strict sampler: indexed configuration repair and blocked authentication

The reviewed repair passed **74 offline tests in this projected layout**. In the actual retained Linux checking context, source installation and real strict preflight passed. The indexed Lake configuration provenance, sources, tools, traces and artifact identity checks completed; runtime authentication then failed at an **unnamed trusted import-cache root** whose directory check failed. It produced no runtime freeze. Planning, proof compilation, export, kernel comparison and full strict checking were not reached.

This successor preserves the [original strict sampler challenge](../../strict-sampler-challenge/README.md) and its native evidence. It changes runtime admission for indexed Lake configuration objects, not the theorem, fixed machine, Statement/Solution, descriptor, definition-hole policy, 679-source freeze or strict sandbox/default-kernel/axiom rules. The exact missing cache root remains **unknown**; the traceback does not distinguish absence from an ordinary nondirectory. A named read-only diagnostic is pending, not a result supplied here.

## Actual evidence by stage

| Stage | Captured result | Evidence |
| --- | --- | --- |
| Source installation | Exit 0, 9.65 s; zero submitted build files afterwards | [Log](evidence/startup/install.stdout.log), [outcome](evidence/startup/outcome.json) |
| Real strict preflight | Exit 0, 3.65 s; non-root systemd/Landrun sandbox probes passed | [Log](evidence/startup/preflight.stdout.log) |
| Configuration checks | Completed before the observed cache inventory exception, from exact frozen source ordering | [Provenance](provenance-bindings.json), [diagnosis](evidence/cache-diagnosis.json) |
| Runtime authentication | Exit 1, 200.83 s; unnamed trusted cache directory check failed | [Complete stderr](evidence/startup/authenticate.stderr.log) |
| Runtime freeze / plan / full strict | Not produced / not run / not run | [Outcome](evidence/startup/outcome.json) |
| Owned cleanup | Owner reported absent/reaped processes and unchanged retained pins | [Projected receipt](evidence/startup/cleanup.json) |

These times measure installation/preflight/authentication, not sampler runtime. [Verification](verification.json) keeps unperformed stages separate. The closed capture binds seven locally rehashed host downloads from an eight-member inventory, nine guest archive members, the original final outcome and cleanup digests. The remote-only checking disk is identified by owner metadata; it is neither included nor locally rehashed by this packet.

The earlier read-only **guest configuration capture passed**, but its **host terminal-status publication failed with WinError5**. Published status stayed `launching`; its temporary PASS was not promoted. Independent caller cleanup/post-pin observations supplied closure. The [split observation receipt](evidence/readonly-observation.json) retains both outcomes rather than normalizing them to overall success.

The [actual-byte conversion/inventory check](evidence/configuration-conversion.json) deterministically bound six captured configuration object/trace artifacts and rejected the two tested malformed variants. It only invoked the pure inventory validator on local read-only materialized data; it was not live runtime admission. Its `full_runtime_admission:false` remains historical and scoped. The [cache diagnosis](evidence/cache-diagnosis.json) was written while terminal collection was pending; that creation-time flag is preserved, while the newer outcome above records the closed authentication failure. No proof or mathematical rejection is inferred.

## Repair and trust boundary

[Runner](runner/strict_sampler.py) SHA `136f13a56001c6f4f31e73a7133193cc946be32de3cc4970edc9fc06c2a65d38` and [authenticator](runner/authenticate_runtime.py) SHA `4b9d22b3673dfc0820e2d4752c7deea9a3428add0e2ef97eb00383457c8b42ff` require a separately SHA-bound configuration-provenance file. They admit only the exact independently authenticated indexed configuration objects, not every `.lake/config` file or a basename exception. [Source derivation](source-derivation.json) explains the pinned package-index mapping.

The capture-specific [configuration provenance](configuration-provenance.json), SHA `645f1f13d16c12eb421d86c379ac2b18f7a40170226e07558445afb0336860a0`, binds slots `{0,1,5}`, six regular object/trace files, ten configuration sources, nine package revisions, actual Lean/LeanIR/Lake binary hashes and exact platform/commit/configHash/options. Locks must remain present or absent exactly as captured. The source/tool/artifact bytes, stat identities and keysets are rechecked; regeneration or drift fails closed. The [template](configuration-provenance-template.json) is explicitly ineligible. A trace or current object observed in a cache cannot authenticate itself.

Official pinned toolchain/package caches and the sealed retained context remain trusted inputs, not rebuilt Mathlib proofs. The read-only observer captured raw Git identity and exact sources but did not establish checkout cleanliness by running captured Git filters/hooks. The complete runtime source/Git/cache/native-audit admission was not reached in the failed startup. Native proof checks and separate default Linux receipts do not become strict exporter/kernel/Comparator evidence here. No numerical sampler degree is supplied.

The validator hard-pins retained bootstrap `da762be8cf147ef834961359511d3cf7cf5d47e04da2ed440f2c898befca9a91`, observed through stopped descendant `3ace7cad836f3a8cfa7ea8b38c98d4ec97da23e611da1cdac7bf1235d1e139a0`. The retained vendor image's dated public URL remains unresolved. Another compatible Linux environment is a new measured context requiring independently authenticated capture and a separately reviewed origin/runner freeze. A portable measured Linux outer supervisor for the full workload remains unpublished. This packet includes no VM images, host-specific wrappers, configuration binaries or transcripts.

[Original-to-public mappings](evidence/redaction-manifest.json) distinguish unchanged source/support bytes, the two test-fixture path substitutions, receipt omissions and guest path-prefix substitutions in logs. Full stage diagnostics and warnings remain; raw originals are preserved privately. Process identities/account paths are omitted from public projections. No original archive file was changed.

## Source and test reproduction

Location: `research/strict-sampler-checkpoints/configuration-repair-v1/`. The [patch](implementation.patch) records the two runtime body changes and the added test body against the frozen original corpus. The descriptor and three measured support libraries remain byte-identical. `source-plan.json` changes only two private Statement/Solution fixture references to the original public archive; every source digest and the trusted runner source-freeze are unchanged.

In a checkout containing this packet, bootstrap the pinned upstream/package sources before the offline tests:

```sh
bash scripts/bootstrap_lean.sh
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover \
  -s research/strict-sampler-checkpoints/configuration-repair-v1/runner \
  -p test_strict_sampler.py -v
```

Bootstrap is a contributor instruction, not a command run during packaging. The [projected test log](evidence/projected-offline-tests.log) and [receipt](evidence/projected-offline-tests.json) record the actual 74-test run. Tests use real source files, synthetic approved configuration/tool captures and mocked Git/system/dispatch; they run no Lean, service or VM. The selected directory depth preserves the test's repository-root lookup.

## Retained-context authentication replay

Follow the original corpus instructions for a separate checking checkout at `fe72b20170e7f85e399368e56baf65b8782b4b50`, exact 13 overlays and Statement/Solution. Install this repaired runner with its adjacent support libraries/source-freeze, preserving cold submitted proofs. Do not run `lake update`. These commands describe the retained-context sequence whose authentication failure is captured above; they are not a completed success recipe:

```sh
# CHECKOUT: dedicated actual non-root Linux checking checkout.
# RUNNER: installed repaired runner with original measured support assets.
# CONFIG_PROVENANCE: exact independently authenticated retained-context JSON.
# CONFIG_SHA: separately verified digest of that file.
# NATIVE_AUDIT: unchanged original corpus native-audit.json.
# RUNTIME: fresh output under CHECKOUT/.tools/linux-verification.
bash -c 'source "$1" preflight; configure_paths; strict_landrun_probe' \
  strict-sampler-probe "$CHECKOUT/scripts/bootstrap_comparator.sh"
python3 -I "$RUNNER/authenticate_runtime.py" --root "$CHECKOUT" \
  --runner "$RUNNER/strict_sampler.py" --output "$RUNTIME" \
  --native-audit "$NATIVE_AUDIT" \
  --lake-config-provenance "$CONFIG_PROVENANCE" \
  --lake-config-provenance-sha256 "$CONFIG_SHA"
# Run this next command only if authentication actually emits a runtime freeze.
# RUNTIME_SHA is its exact MATH115_C11_RUNTIME_FREEZE_SHA256 output.
python3 -I "$RUNNER/strict_sampler.py" --root "$CHECKOUT" \
  --runtime-freeze "$RUNTIME" --runtime-freeze-sha256 "$RUNTIME_SHA" \
  --plan --output "$CHECKOUT/.tools/linux-verification/configuration-repair-plan-01"
```

The current attempt never reached the final command. Comparator's existing Lean 4.34.0→4.34.1 build boundary, real non-root PAM/systemd user session and Landlock/seccomp probes remain required. Full strict execution requires separately reviewed durable outer ownership/deadline/capture/cleanup coverage; the inner cap alone is insufficient.

Next, obtain bounded read-only metadata identifying the rejected cache root and every selected external object. Do not create guessed empty directories, skip unnamed roots or infer this VM's root from a separate hosted Cli failure. Any later absent-unused-root policy needs explicit before/after absence binding, symlink/file/drift rejection and unchanged required-import/source-owner coverage. No such diagnosis or policy change is executed or claimed by this packet.
