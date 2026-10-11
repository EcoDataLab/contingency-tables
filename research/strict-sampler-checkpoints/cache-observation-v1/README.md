# Later partial observation of the strict checking cache

A closed read-only observation of the stopped checking filesystem identifies **`formal/.lake/packages/Cli/.lake` as absent**. The requested cache root `formal/.lake/packages/Cli/.lake/build/lib/lean` is therefore `blocked_parent`. This is a later filesystem fact; the [earlier configuration-repair authentication failure](../configuration-repair-v1/README.md) and [original strict corpus](../../strict-sampler-challenge/README.md) remain unchanged.

The diagnostic **failed at the fixed 20,000-entry aggregate cache keyset cap**, after 96.75 seconds. Its top-level `complete` is false. It is not runtime authentication, a repaired startup, a completed cache inventory or strict acceptance.

| Retained root row | Appended metadata entries | Interpretation |
| --- | ---: | --- |
| Builtin Lean cache | 15,427 | Directory; completed metadata keyset |
| Cli requested cache | 0 | Blocked by absent `formal/.lake/packages/Cli/.lake` |
| LeanSearchClient | 53 | Completed metadata keyset |
| Qq | 184 | Completed metadata keyset |
| aesop | 1,740 | Completed metadata keyset |
| batteries | 2,538 | Completed metadata keyset |
| importGraph | 58 | **Partial tail** when the next entry exceeded the cap |

The raw producer initialized the last row's `keyset_complete=true` before traversal and emitted no keyset hash for that row. It must not be interpreted as complete. The [consumer outcome](evidence/outcome.json) records `last_root_consumer_keyset_complete:false` while the projected raw diagnostic preserves the original flag. Missing report fields are not empty inventories.

The mathlib, plausible and proofwidgets root observations, all **82 external candidate/object facts**, the cold-proof scan and **679 submitted-source hash checks** were not reached. Source-only expected owner analysis is not guest runtime coverage and is not promoted here. No absent-cache exception or startup fix is implemented by this addendum; root policy and a later measured run remain separate work.

## Exact evidence and limits

[Projected diagnostic JSON](evidence/cache-diagnostic.public.json.gz) retains every producer field with only guest/checking path-role substitutions, compressed with deterministic gzip. [Projection mappings](projection-map.json) bind the original raw SHA `990cf90ead4d9c73e054903af8c8aa6b44c27025a89e007bab9c5d0c24cb7fb9`, published gzip SHA and decompressed public SHA/size. Compression roundtrips exactly to the declared public projection, not to unredacted raw bytes.

The [exact captured guest error](logs/guest-reader-error.txt), [empty captured supervisor stderr](logs/supervisor.stderr.log), [empty emulator stderr](logs/qemu-stderr.log) and [allowlisted terminal stdout facts](logs/supervisor.stdout.public.json) preserve the relevant reporting outcome. No fuller guest traceback was captured beyond the error fields. Raw serial/QMP transcripts and raw host control details are kept privately and omitted, with their original inventory identities retained. The stdout file is explicitly a structured projection rather than a full transcript.

The [closed cleanup receipt](evidence/cleanup.json) records reaping, source/retained pin checks, process absence and removal/unmounting of the owned read-only mount. Source digest `8826d43c9416ff398da1e878380365eb638e3b7aa5c710374b53128c9b842fb6` and all five retained pins were unchanged. [Provenance](provenance-bindings.json) binds eight locally rehashed host downloads, a nine-member host inventory with one remote-only disk, all 39 regular guest archive members/local bytes, raw final/cleanup/capture identities and the [independent AI saved-artifact review](evidence/independent-fact-review.json). The remote disk itself is not supplied or locally rehashed.

Official cached tools/packages and the sealed retained filesystem remain explicit trust inputs. This is metadata observation, not a kernel, source-owner, imported-object, full-source or cache-admission guarantee. The retained image is not included and its exact external reproduction remains unresolved. No ordinary native/default Linux evidence is promoted to full strict success. This addendum performs no new live observation or wider-cap retry.

## Reproducing the filesystem diagnosis

Location: `research/strict-sampler-checkpoints/cache-observation-v1/`. The [collector](source/cache_diagnostic.py) preserves the observed collector body and all fixed caps, with only its checking-root default changed to the role path `/checking`. [Capture support](source/capture_support.py) extracts the original guest reader's data-copy/no-follow helpers, excluding boot, disk discovery, mounting and host supervision. [The small adapter](source/reproduce_diagnostic.py) supplies a checking-root parameter and a 300-second observational limit on an **already independently authenticated read-only Linux mount**.

These public source projections are not byte-identical copies of the original guest reader/module, and the adapter was not used for the recorded observation. Their exact source derivations and original hashes are in the projection map. They are syntax-checked, not live-replay evidence. They do not mount an image, execute captured files, run Git/Lean/configuration hooks, copy cache object bytes or provide a portable outer VM supervisor. A different filesystem is a new observation and requires its own source/context/ownership authentication.

```sh
# MOUNT: independently authenticated readonly source filesystem, mounted already.
# CHECKING_ROOT: absolute path of the checking tree within that filesystem.
# OUTPUT: new local output directory outside the readonly source mount.
PYTHONDONTWRITEBYTECODE=1 python3 -B \
  research/strict-sampler-checkpoints/cache-observation-v1/source/reproduce_diagnostic.py \
  --mount "$MOUNT" --checking-root "$CHECKING_ROOT" --output "$OUTPUT"
```

Do not widen the cap or treat a failed run as a complete inventory. Preserve output even on nonzero exit. The source-freeze and package set remain pinned, and current diagnostic completion/source/runtime admission must be stated independently. No missing directory should be created or silently skipped on the strength of this partial observation.
