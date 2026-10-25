# Complete metadata snapshot comparison

The completed 2026-10-11 startup06 experiment compared two standalone metadata walks over every one of the 131,021 authenticated cache entries. Both complete dictionaries matched each other and the admitted `(size, mtime_ns, ctime_ns, inode)` identities exactly. The candidate remains **uninstalled**. This is a stable Linux filesystem benchmark, not a claim of concurrent-race/error equivalence, a replacement checker or strict sampler acceptance.

| Measured operation | Seconds |
| --- | ---: |
| Original imported metadata sequence | 25.6491394 |
| Candidate directory-index preparation | 0.4151186 |
| Candidate metadata walk | 0.1979094 |
| Unchanged complete stat-only Guard | 27.0110501 |
| Original plan call | 83.5433168 |

The complete cache represents 9,261,675,188 logical bytes. The metadata reference calls the pinned original runner's actual `relative()` function and its `is_file()` then `stat()` observation sequence. The candidate uses the frozen-name directory index in [source/snapshots.py](source/snapshots.py). [source/guard_benchmark.py](source/guard_benchmark.py) performs exact dictionary comparisons against admission, retains the exclusive lock and original source/cold-tree checks, and calls the unchanged original stat-only guard once afterward. Metadata timings and whole-guard timing describe different operations; the former are not an installed whole-guard speedup.

The distinct guest used one vCPU, 8 GiB RAM, explicit `whpx,kernel-irqchip=off`, CPU `max`, no NIC, no swap and a fresh 80 GiB child. Installation, real sandbox preflight, original runtime authentication and planning/comparison all returned zero. Their stage times were 1.556, 0.480, 159.264 and 137.053 seconds; supervised lifetime through collection was 397.511 seconds. Each benchmark method had a 900-second ceiling and the aggregate benchmark a 1,800-second ceiling. [profile.json](profile.json) and [profile-delta.json](profile-delta.json) record the controls. Four-vCPU startup05 remains a separate historical context; this single experiment does not establish a causal CPU-count effect.

The raw serial stream decoded with strict Base64 validation without reconstruction. Its emitted archive SHA256 is `2b3d47f55eb583e87dd0d587f64b217b66ff1585334119456980fc79a5e6be73`. All 14 regular guest members were authenticated against the emitted manifest. [evidence/guest-evidence.tar.gz](evidence/guest-evidence.tar.gz) contains those exact guest bytes, including complete runtime inventory and logs, compressed to avoid duplicating large text. Paths inside are generic guest paths. Validate the complete member set without extraction or execution:

```sh
python3 source/validate_archive.py
```

The measured dictionary SHA256 is `17257fe85d74d659493751a463e4e646d2f5109df6e6d9ff8602cc70177d79c2`; exact dictionary equality, rather than digest equality alone, was required during the experiment. The emitted runtime hash is `e391c457d01020a0e384aa25af657417c127145be21695bd6d469bea418855d4`. Original source-freeze, checker, authenticator, archive, tools, seeds and plan bindings are in [provenance-bindings.json](provenance-bindings.json).

This attempt recorded zero soft-lockup warnings and empty QEMU stderr. That observation does not establish why startup05 warned or guarantee future warning-free operation. The supervisor terminated and reaped its owned VM after collection; QEMU returned 1. All five retained image/tool pins remained equal, and the process inventory was clear at collection. No proof compiler, exporter, default-kernel replay or Comparator step ran.

Separate read-only reviews approved the prototype and wrapper for this standalone comparison. They did not independently execute it. The candidate's stronger directory-drift checks, one leaf observation instead of the original multiple observations, and differing error paths remain limits on a replacement claim. No atomic namespace snapshot or general adversarial filesystem guarantee is established. [review-boundaries.json](review-boundaries.json) records the scope.

Exact portable source, guest entry, seed generator, ISO builder, installation/media helpers and resource delta are supplied. [reproduction-references.json](reproduction-references.json) gives commands, intended file layout and pinned prior packets. The host-specific VM wrapper, raw serial, seed ISO and retained images/bootstrap context are omitted and hash-bound; the exact source archive is also referenced by hash rather than duplicated. This is not a portable independently reproducible full VM package. Seven host records were downloaded and rehashed; the stopped child disk was deliberately retained remotely, 567,672,832 bytes, SHA256 `ff5ed23a4bce06757d7ffffb55ba1fe1e2ba170b059afa74581afde17d743c39`. Its omission limits image reproduction/forensics, not the authenticated 14-member guest receipt.

The earlier [accelerated planning receipt](../accelerated-plan-v1/), [authenticated TCG plan](../authenticated-plan-v1/) and [authentication diagnostics](../authentication-diagnostics-v1/) remain unchanged. This checkpoint used their retained challenge inputs; it is not a compilation of later research proof checkpoints.
