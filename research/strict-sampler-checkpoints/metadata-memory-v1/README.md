# Metadata snapshot memory repair

The long historical sampler replay exhausted its guest RAM in the **Python verification helper**. The kernel killed that process at 9,751,912 kB anonymous RSS, after 20 completed modules and 42 passed command stages. The next module command has no recorded exit code. Export, default-kernel replay and Comparator were not reached. The [terminal summary](evidence/long04-terminal.json) preserves the result and provenance hashes; it is a sanitized account of privately retained receipts, not a replacement for their full bytes.

Both metadata helpers contain a recursive nested `walk` function. Its closure points back to itself and captures the dictionaries containing the snapshot results; the main guard also captures the expected metadata. Returning from the traversal closes descriptors but leaves this cycle for Python's cyclic garbage collector. Repeated snapshots can therefore retain large dictionaries even though callers have released them. The production guest used Python 3.14. The retained dictionaries are a demonstrated defect and a plausible contributor to the OOM; the evidence does not establish that they were its only cause.

The repair adds **`walk = None` in the existing outer `finally`, before the same descriptor-closing loop**, in [anchored_metadata.py](source/anchored_metadata.py) and [snapshots.py](source/snapshots.py). This breaks the closure's self-reference after recursion has returned or unwound. All filesystem observations, validation, return values, exception behavior and descriptor cleanup remain in the same order. Neither helper changes GC thresholds or calls `gc.collect()`. The preparation helper uses `ManifestTrie.snapshot`; this second fix matters even though its inherited header calls it a standalone prototype.

The changes are additive. The original helpers, failed attempts, observer repair, source freeze and original verifier remain unchanged. Exact original paths and SHA-256 hashes are in [reproduction-references.json](reproduction-references.json); four minimal diffs are under `source/`.

## Reproduce the small checks

From the repository root, with CPython 3.10 or newer on a POSIX system:

```bash
python3 -B -m unittest discover -s tests -p test_comparator_metadata_memory.py -v
python3 -B research/strict-sampler-checkpoints/metadata-memory-v1/tools/default_gc_diagnostic.py
```

The normal test bridge runs 15 checks: both lifetime regressions, equal successful outputs, symlink/missing-file/path and metadata rejection behavior, descriptor cleanup including an injected directory-open failure, exact AST deltas, candidate/preparation pin consistency, and fresh source assembly with tamper rejection. Lifetime fixtures temporarily disable GC to distinguish immediate release from later collection, then restore its prior state. This is diagnostic test behavior only.

The optional second command leaves default GC enabled and thresholds unchanged. A [saved local CPython 3.14 diagnostic](evidence/default-gc-result.json), with 100 files and 80 snapshots, retained 80 original expected dictionaries and about 8.47 MB of traced allocations, versus zero dictionaries and about 24.8 kB with the fix. These small measurements are not production RSS estimates or a guarantee of full-run memory use. Other Python versions may collect the old cycles sooner.

## Pinned next-run source preparation

The new [runner delta](source/versioned_runner.py.diff) changes only its metadata-helper pin, receipt version label and header. The new [memo preparation delta](source/prepare_memos.py.diff) changes only its candidate-runner and preparation-snapshot pins. The exact replacement recipes and expected result hashes are in [derived-sources.json](derived-sources.json), avoiding duplicated runner bodies. Their function/class bodies are identical to the preceding observer packet. The observer, sandbox, watchdog, inventories, admission checks, export, default-kernel replay and Comparator are unchanged. All exact candidate and reference hashes are checked by the offline assembly command:

```bash
python3 -B research/strict-sampler-checkpoints/metadata-memory-v1/tools/prepare_candidate.py \
  --destination /tmp/metadata-memory-next
```

The destination must not exist. The command copies only reviewed source/support files and writes `assembly.json`; it executes no preparation, Lean, checker or VM. It supplies separate `candidate/`, `preparation/` and unchanged `original/` directories, including each runner's correctly pinned runtime assets.

For a separately authorized future Linux run, assemble instead into a fresh directory **inside the fresh checking checkout**, for example `$CHECKING_ROOT/.tools/linux-verification/metadata-memory-next`. Set `STAGE` to that directory and `BASELINE_RUNTIME` to a freshly authenticated original runtime from that same checkout. The existing preparation invocation then uses:

```bash
python3 -I "$STAGE/preparation/prepare_memos.py" \
  --root "$CHECKING_ROOT" \
  --runner "$STAGE/original/strict_sampler.py" \
  --candidate "$STAGE/candidate/strict_sampler.py" \
  --authenticator "$STAGE/original/authenticate_runtime.py" \
  --baseline "$BASELINE_RUNTIME" \
  --output "$CHECKING_ROOT/.tools/linux-verification/metadata-memory-preparation" \
  --helper "$STAGE/preparation/NormalizeMemos.lean" \
  --snapshot "$STAGE/preparation/snapshots.py"
```

That preparation command performs real Linux work and **has not been run with this candidate**. It retains the original fresh-authentication and frozen-repeat gates. A future supervisor must bind the new source hashes and resulting fresh runtime hash before execution; old native/proof objects and old runtime receipts cannot establish a fresh pass. This packet supplies no new VM media, admitted lease or launch authorization.

The runner already supports `--wall-seconds 39600` (its default and maximum). The preceding observer packet's **VM invocation/profile** imposed a 7,200-second proof limit, whereas failed long04 used 39,600 seconds inside a 40,500-second proof phase and 55,800-second outer allowance. This source-only assembly includes no VM entry point, supervisor or media and does not encode that longer resource/lease profile. A future replay must explicitly bind the intended longer invocation and matching enclosing budgets; this repair is not a reason to restore the removed two-hour constraint.

The target remains only the historical **679-module** sampler, source freeze `2a15fa398282a2825cc773b5e5110f8bacc4fbc2af9f28afb88f1b326c1b93bd`, with 1,362 required command stages. It excludes newer executable-sampler research. Full strict acceptance remains open: neither this repaired preparation nor a repaired proof/export/kernel/Comparator replay has run. The retained vendor-image/source-archive availability gaps in the [VM notes](../../../docs/strict-comparator-vm.md) also remain. Lake's `--no-cache` is not a blanket artifact-cache read disable; this repair adds no new cache-provenance claim.

The [manifest](manifest.json) binds the packet, original references, normal test bridge and validation scope. Independent review is recorded separately from runtime verification.
