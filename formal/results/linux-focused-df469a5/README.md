# Completed stage: fresh Linux focused verification

[GitHub Actions run 38030825047](https://github.com/EcoDataLab/contingency-tables/actions/runs/38030825047)
passed on 10 October 2026 UTC at
`df469a50e32c652093bac17a031b5c2ae6bd8af7`, tagged
`verify-stage-final-2026-10-10`. The [receipt](verification.json) binds that
source checkpoint, its ordinary Lean build, all **1,236 focused named axiom
audits**, and the complete compiled-environment audit. The [earlier failed
attempt](../linux-focused-cef573d-failure/README.md) remains separately preserved.

| Check | Result and scope |
| --- | --- |
| Ordinary compilation | Focused upstream transport and integrated `Math115` closure passed on a fresh hosted Linux job; official dependency caches are trusted. |
| Named audit | All 1,236 declarations passed the exact ordered allowlist, using only `propext`, `Classical.choice`, and `Quot.sound`, or subsets. |
| Compiled environment | **22,710 selected declarations**, including **16,549 theorem constants**, with **11,849 imported modules** and all **six headline dependency closures**. These include pinned upstream and generated/private declarations, not just new theorems. |
| Input integrity | Helper compilation and audit each preserved their recorded input inventories. The audit receipt records 1,181 input files and 69,797 artifact files, including explicit absent inventory roots. |
| Separate standalone named audit | Not run in this job. Its six declarations are inclusion checks in the full environment report; the earlier standalone receipt retains its own scope. |
| Strict Comparator | Not run. No complete encoded outer sampler, numerical full runtime exponent, or new performance result is established here. |

The audit retains the exact namespace/defining-module selection in
[frozen-config.json](environment-audit/frozen-config.json), the generated
[driver](environment-audit/Audit.lean), and the complete report in
[environment-audit.stdout.gz](environment-audit/environment-audit.stdout.gz).
The report decompresses to 149,192,527 bytes with SHA-256
`bf0fa0e2dc770358b783ff5526e35f0c14da2adb866677bab25d57f62f5a62b6`.
Its deterministic content matches the earlier native report byte for byte;
the Linux compiler/object inventories and process receipt are distinct.
Every selected theorem type and axiom list, and every headline's complete
proof/type dependency closure, is retained. The [English-to-Lean headline
index](../environment-aggregate-1236/headlines.json) explains those statements.
Dependency closures overlap and their sizes must not be added.

## Evidence provenance

The authenticated GitHub run, job, and artifact REST objects are retained as
[provider-run.json](provider-run.json), [provider-job.json](provider-job.json),
and [provider-artifact.json](provider-artifact.json). They are the saved JSON
representations without content projection; their original saved-byte hashes
match `source_metadata_sha256` in the receipt. Signed download credentials
are excluded. Artifact `11662172536`, named
`math115-linux-focused-38030825047-1`, was downloaded in full: its **27,968,975
bytes** match the provider's SHA-256
`093069d997afd8355fd35dd0130f56ff000ab61ec931e89593ce3737f8dee4d5`.

The [archive member map](archive-member-map.json) accounts for all 23 original
members. Original text bytes are preserved, with deterministic lossless gzip
for large reports. Byte-identical before/after inventories and empty streams
share a single published file. The only excluded binary is the audit helper's
`.olean`; its actual bytes were checked against the recorded object digest
and its original length and hash remain in the map. The ZIP and imported
binary dependencies are not included in this source repository.

The exact [offline packager](package.py) checked provider associations, outcome,
source hashes against the immutable Git commit, ordered named audits, complete
environment report, snapshot equality, and all recorded imported-object bindings.
It has a separate [source review](packager-review.json). The frozen receipt's
`independent_review` field records the packaging-time pending state; the later
[actual-artifact review](review.json) records post-packaging readback without
rewriting that receipt. The [publication manifest](manifest.json) binds the
published files other than itself. These reviews were performed by separate
AI agents within this project; no outside human review is claimed.

Compiler binaries, official dependency caches, the operating system, system
loader/libraries, and Python remain trusted. The imported-object map binds the
hosted runner's recorded resolution and hashes; offline packaging does not
recreate its unavailable filesystem. This is ordinary compilation plus a
compiled-environment audit, not strict kernel replay.

## Reproduction and handoff

Use the exact tagged source and the pinned instructions in the
[Linux guide](../../../docs/linux-verification.md). The successful job's
[bootstrap log](bootstrap-lean.log), [verification log](verification.log),
[environment](environment.json), and [outcome](outcome.json) preserve its
commands and results. Later publication commits add evidence and documentation
while preserving this checkpoint's active proof and verification inputs.

The [contributor handoff](../../../docs/handoff.md) lists the completed stage
and the remaining encoded-program, runtime-accounting, and strict-verification
obligations. A new source change requires verification of its own exact bytes.
