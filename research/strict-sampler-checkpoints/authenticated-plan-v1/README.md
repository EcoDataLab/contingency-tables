# Strict sampler startup admission passed

11 October 2026. A bounded Linux guest attempt passed source installation,
real non-root sandbox preflight, complete runtime authentication and plan
admission for the frozen 679-module revised-sampler challenge. All four stages
returned zero. Full submitted proof compilation, export, default-kernel replay
and Comparator comparison remain unexecuted.

| Stage | Measured duration | Ceiling |
| --- | ---: | ---: |
| Install | 9.823 s | 600 s |
| Strict preflight | 3.607 s | 300 s |
| Authenticate | 2,583.607 s | 5,400 s |
| Plan | 2,142.388 s | 3,600 s |

The complete owned VM interval was 4,825.217 seconds. These measure startup and
admission work, not sampler runtime. The guest used four vCPUs, nominal 8 GiB
RAM, QEMU TCG, no NIC, no swap and a fresh 80 GiB sparse child. Its outer ceiling
was 12,600 seconds. Linux 7.3.0-8-generic reported Landlock ABI 11, non-root UID
1000 and zero effective capabilities; actual systemd and Landrun denial probes
passed. Owned processes closed and the five retained image/tool pins matched.

The only source changes from startup03 were the bounded phase ceilings, the
plan wall allowance and the unique provisioning instance identifier. The
checker runner, authenticator, submitted proof sources, indexed configuration
provenance, unused-cache policy, cache inventories and guard predicates stayed
unchanged. The earlier memory failure and 600/1,800-second failure packets are
preserved. This passage adds a later outcome without replacing them.

## Exact bindings and scope

| Binding | SHA256 |
| --- | --- |
| Runtime freeze | `e391c457d01020a0e384aa25af657417c127145be21695bd6d469bea418855d4` |
| Admitted plan | `6f95a195f568b3ab53493b4e2d534f69d0fa2cf7b6054f2b8d1a94c3f04f5d0c` |
| Submitted source freeze | `2a15fa398282a2825cc773b5e5110f8bacc4fbc2af9f28afb88f1b326c1b93bd` |
| Raw supervisor configuration | `5673a2ade0f21fda364f4084c89ace15b2581ca679f2ef7594f7abfec574a602` |
| Unchanged runner | `4ba0a3c42bee4f511909fc50ad33b00be2a5cc3cabecdd2b54ac08ec7970d1a6` |
| Unchanged authenticator | `742ec1105d5bb44a392046ec06ca5944a20989bc0cb5a037d2997b37def2b943` |

The admitted roots are `Math115.StrictSamplerStatement` and
`Math115.StrictSamplerSolution`, using installation commit
`fe72b20170e7f85e399368e56baf65b8782b4b50` and its exact frozen overlays.
Installation recorded zero submitted build files. The plan's runtime/source
hashes match their actual collected bytes. This is the existing fixed-machine
challenge; admission does not add the later gap refinements to its proof scope.

[Outcome](outcome.json), [verification](verification.json) and
[provenance bindings](provenance-bindings.json) identify the preserved private
capture and this allowlisted projection. Eleven guest files are included
byte-for-byte; the phase table omits only argv and process identities, with its
original digest retained. Complete authentication and plan stderr contain
1,284 and 831 diagnostic JSON records respectively, with no other lines
omitted. Official toolchain/package caches remain explicit trusted inputs;
this is not a from-source rebuild or independent certification of Mathlib.

Seven of eight host capture files were downloaded and locally rehashed. The
eighth is the stopped `sampler-overlay.qcow2`: 576,913,408 bytes, remote SHA256
`d213b6e9ee94fde56c8b300c5c70226f0caaff29492ba3a96a68ccf4e1e8df16`.
It was deliberately retained remotely, not lost. All thirteen regular guest
archive members, including runtime freeze and admitted plan, were independently
byte/hash authenticated after extracting the complete collection stream.
The disk omission limits full-image reproduction and offline disk forensics;
it does not leave a missing stage log or an incomplete scoped startup receipt.
The raw disk, host controls and runtime inventory are not supplied by this
public projection. The exact dated vendor-image URL and portable outer
supervisor remain unresolved, so no independent public reproduction is claimed.

[Reproduction references](reproduction-references.json) pin the existing public
runner/authenticator bodies and their base inputs. [Cap delta](cap-controls.diff)
records every semantic control change without distributing private host
wrappers. Templates retain all provenance/policy/diagnostic flags and require
actual emitted hashes, fresh outputs and bounded owned supervision. They do
not assert that the public projection alone can recreate the retained VM.

## Full-run budget still needs work

The [guard assessment](guard-cost-assessment.json) derives closed intervals
from the included full progress streams. Inventory-end to guard-begin took
595.283 seconds in authentication and 739.029 seconds in plan; the source maps
those intervals to cache metadata snapshotting and guard construction.
Individual call costs were not separately measured. The complete
`Guard.check(rehash=True)` wrapper took 972.242 and 1,024.789 seconds. Each
completed full inventory/guard covered 131,021 files and 9,261,675,188 logical
bytes. These are logical work counters, not physical disk throughput.

The unchanged full execution performs 2,724 stat-only guard calls around its
679-module build and final stages, plus additional full rechecks. A
39,600-second inner allowance would require less than 14.54 seconds per
stat-only guard even before compiler, exporter, kernel and other work.
The stat-only call has not been timed in isolation, so multiplying the observed
full-hash durations into a projected runtime would be unjustified. The measured
metadata spans nevertheless make the current TCG full-run budget doubtful.
The next bounded diagnostic should time an exact `Guard.check(rehash=False)`
with every validation retained, then assess the execution environment or a
reviewed implementation improvement. No full proof was dispatched after this
startup passage, and this packet contains no full-proof execution result.

A standalone replay still needs the retained-context provenance and the same
cold-proof, source-owner, indexed configuration, cache-state, sandbox and
kernel conditions described in the
[diagnostic source packet](../authentication-diagnostics-v1/). This outcome
projection is not a replacement setup corpus or an acceptance of the sampler.

The separate [publication review](publication-review.json) checks the projected
files and phase bindings against the sealed local capture. It is AI review of
saved evidence, with no additional VM or Comparator execution.
