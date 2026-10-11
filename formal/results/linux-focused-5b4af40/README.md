# Integrated bounded sampler: fresh Linux verification passed

[GitHub Actions run 38101898049](https://github.com/EcoDataLab/contingency-tables/actions/runs/38101898049)
passed on 11 October 2026 UTC at
`5b4af402a281a9bc02a38adb168f7b0bfde5d3aa`, tagged
`verify-bounded-sampler-integration-2026-10-11`. The [receipt](verification.json)
binds the expanded default target, including the fixed public machine and its
complete bounded-sampling theorem. The job finished in 2 hours 50 minutes;
its selected verification step took 2 hours 47 minutes 47 seconds.

| Check | Result and scope |
| --- | --- |
| Ordinary compilation | The 685-module submitted source closure passed on a fresh hosted Linux job. Official dependency caches are trusted. |
| Named audit | All 1,511 focused declarations passed the exact ordered roster, using only `propext`, `Classical.choice`, and `Quot.sound`, or subsets. |
| Compiled environment | 25,448 selected declarations, including 18,054 theorem constants; 11,951 imported modules; all 22 headline dependency closures. These include pinned upstream and generated/private declarations, not just new results. |
| Additional obligations | Three source-private helpers were resolved to actual compiled declarations; two program-identity closure checks passed. |
| Standalone declarations | Six names were checked for inclusion in the environment. No separate standalone named replay ran, so they are not added to 1,511. |
| Strict Comparator | Not run. The full numerical machine-time exponent and practical speed remain unknown. |

The full report retains statement types, defining modules, axioms and closure
bindings. The [claim guide](../../../docs/claims-and-evidence.md) and earlier
[complete-checkpoint statement map](../../../docs/outer-sampler-compiler-checkpoint.md)
supply English interpretations, which remain subject to mathematical review.
The [environment report](environment-audit/environment-audit.stdout.gz)
decompresses to 459,840,089 bytes with SHA-256
`e99076aab0a36c2f21623bf16fb882d07b264497e7dc5ac2f163386a44ff9e94`.
Its exact selection and driver are retained in
[frozen-config.json](environment-audit/frozen-config.json) and
[Audit.lean](environment-audit/Audit.lean). Headline closures overlap; their
sizes must not be added.

## Evidence provenance

Artifact `11691583222`, named `math115-linux-focused-38101898049-1`, was
downloaded in full. Its 59,553,741 bytes match GitHub's SHA-256
`a4b058840dc81f6371478fbbc4c3135b0f6453bf1cb4c05417aa99d2f7ef2b5a`.
The provider [run](provider-run.json), [job](provider-job.json), and
[artifact](provider-artifact.json) files are allowlisted metadata projections;
original response-byte digests remain in the receipt. Actors and signed
download URLs are excluded.

The [member map](archive-member-map.json) accounts for all 23 archive members.
Original text bytes are preserved, with deterministic lossless gzip for large
files. Byte-identical before/after inventories and empty streams share files.
Excluded binary helper objects were verified against their recorded identities;
their hashes and sizes remain in the map. The original ZIP and compiled
dependencies are not committed to this source repository.

The exact [packager](packager.py) authenticated provider associations, source
hashes against the immutable Git commit, the complete source graph, ordered
named audits, report structure, all headline closures, private-helper and
program-identity obligations, inventories and imported-object bindings.
The [publication review](review.json) records the root's completed collector
validation and a separate AI agent's **partial** readback. That second reader
confirmed provider/archive associations, all package file hashes, metadata
projections and outcome fields, then blocked on a local Git subprocess pipe.
It was stopped before completing the independent immutable-source and full
report/closure checks; those checks remain open. No second parse or retry was
started. The frozen receipt retains its creation-time pending-review annotation;
that historical field is not rewritten. No outside human review or independent
execution by those reviewers is claimed.

The receipt stores the observed run-time claims-ledger hash separately from
proof/configuration inputs. This permits later evidence annotations without
a circular requirement that the ledger contain its own future receipt hash.
The checked headline union and proof inputs remain fixed.

Official dependency caches, compiler binaries, the operating system,
loader/libraries and Python are trusted. The imported-object inventory binds
the hosted runner's recorded resolution and hashes; offline readback does
not reconstruct its filesystem. This is ordinary compilation and environment
inspection, not strict kernel replay.

## Reproduction

Check out the exact tag above, follow the pinned [Linux setup](../../../docs/linux-verification.md),
and run `bash scripts/verify_lean.sh focused --serial`. Preserve the logs,
ordered axiom reports, compiled environment and source/object inventories.
The [bootstrap log](bootstrap-lean.log), [verification log](verification.log),
[environment](environment.json) and [outcome](outcome.json) retain the actual
commands and outcomes. Serial mode limits concurrent compilers, not one
compiler's memory use.

The [contributor handoff](../../../docs/handoff.md) separates this completed
integration from the remaining numerical-degree, strict-verification,
performance and application-validation work. Later source/configuration
changes require evidence for their own exact bytes.
