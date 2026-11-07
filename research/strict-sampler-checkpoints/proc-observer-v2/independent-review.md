# Independent AI review of replay controls

This is a separate AI-agent source/evidence review.

6 November 2026. Read-only source and evidence review completed before remote
staging/launch; no active script, configuration, media, or remote job was changed
by this reviewer. Verdict: pass; no blocking defect found in the reviewed controls.

Exact reviewed supervisor SHA-256:
`b645e89fe2ddd3effcb3d39d3a31b7297eddee53c3ba1266270eb4907157321e`.
Exact reviewed ISO SHA-256:
`cd2c4b7145a3f7cbce2cdf4b197f97e91394a6bdb664d85e930dc76c8d7cbebd`
(82,968,576 bytes).

I independently reran 19 supervisor, 3 progress, and 14 observer fixtures; all
passed. I recomputed every source-review receipt and staging-manifest member
hash. Using the existing local pycdlib environment, I read all three ISO members
and checked exact byte equality with the generated sources, then decoded and
checked all 12 embedded payload hashes. All bindings matched.

The resource patch retains the pinned QEMU/backing chain, fresh 80 GiB virtual
disk, 10 GiB guest RAM, one CPU, no NIC, no swap admission, original checker and
sandbox, 7,200-second inner proof deadline, and 12,600-second outer deadline.
The separately versioned host profile requires 40 GiB free at admission, stops
only the held owned VM below 20 GiB host free or above 16 GiB child-file length,
and samples every second. These are sampled stop guards, not a hard OS quota.
The previous 874,774,528-byte child reached only nine modules and gives no
complete-build growth guarantee. Fresh resource admission remains required at
launch; the reviewed prestaging snapshot alone does not reserve resources.

The observer candidate is exactly
`b5e8c0f95fdd5f6b9193c2b0537782b242d0fe0c269dae7b5a7a4c73a32cb1f0`.
Independent AST comparison found changes only to `compiler_pids` and
`MeasuredRunner`. Denied/vanished executable reads invalidate the entire sample;
unknown observations do not become zero, update the measured peak, or reset the
five-second watchdog. Positive overlap remains an immediate failure, including
when another PID is unreadable. The old real Linux toy recovery, persistent
denial/watchdog, and overlap receipts and their exact hashes were reviewed.
Those diagnostics used Python toy processes and establish no Lean acceptance.

Shell calls use argument vectors or fixed reviewed, quoted paths. Resource,
telemetry, timeout, and cleanup failures remain failures; progress is telemetry,
not acceptance. Acceptance still requires all 1,362 command stages, actual
exporter/default-kernel/Comparator results, final inventories and rehashes, and
authenticated evidence readback. The target is only historical source freeze
`2a15fa398282a2825cc773b5e5110f8bacc4fbc2af9f28afb88f1b326c1b93bd`
(679 modules), excluding newer research modules. This note does not certify the
subsequently launched attempt or a final acceptance outcome.

## Public packet readback

The public `research/strict-sampler-checkpoints/proc-observer-v2` packet was
subsequently reviewed independently. Normal unittest discovery ran all 36
observer/supervisor/progress tests successfully. Every declared manifest member,
the normal-suite bridge, all reproduction-reference targets, and all 19 regular
toy archive members were hashed independently and matched their declarations.
The archive contained no extra members or unsafe paths. Declared packet files
and archive contents contain no private host/account paths; local Python cache
files are gitignored and are outside the packet manifest.

Review found and the author repaired two documentation/provenance issues:
the challenge's old provisioning narrative now has an explicit historical
11 October heading and current-status link, and `original_runner` now names
the diagnostic baseline actually required by preparation (`4ba0a3...`), rather
than its `acebbe...` predecessor. The corrected public file SHA-256 and updated
packet manifest were read back and match. Active controls/archive/media were
unaffected. The packet honestly records a dated pending historical-only attempt,
retains failed/toy evidence, states sampled-resource limitations, and does not
claim complete VM reproducibility or strict acceptance. Public packet verdict:
pass after those two corrections. This is source/evidence review, not a later
run-outcome certification.
