# Accelerated startup, planning and guard timing

The retained 2026-10-11 startup05 completed source installation, real sandbox preflight, runtime authentication, original strict plan admission and one exact `Guard.check(rehash=False)` call. It used an 8 GiB, four-vCPU QEMU guest with explicit `whpx,kernel-irqchip=off`, no guest NIC and no swap. Every guest stage returned zero. This receipt contains no proof compilation, export, default-kernel replay or Comparator result; it does not establish strict sampler acceptance.

| Measured stage | Seconds |
| --- | ---: |
| Installation | 1.649 |
| Sandbox preflight | 0.535 |
| Authentication | 157.789 |
| Plan plus timing wrapper | 108.342 |
| Original plan call within wrapper | 81.639 |
| Exact stat-only guard within wrapper | 26.625 |
| Supervised VM lifetime through collection | 357.629 |

The admitted plan has 679 modules and source-freeze SHA256 `2a15fa398282a2825cc773b5e5110f8bacc4fbc2af9f28afb88f1b326c1b93bd`. Its actual emitted runtime-freeze SHA256 is `e391c457d01020a0e384aa25af657417c127145be21695bd6d469bea418855d4`; the plan and timing metrics bind that same runtime. The unchanged checker and authenticator bodies are referenced in [reproduction-references.json](reproduction-references.json). [control/guard_benchmark.py](control/guard_benchmark.py) is the exact measured wrapper: it preserves the original admission and plan call, then times the original guard under the same exclusive lock. It executes no proof step. The wrapper received a separate source review; that review is not independent execution of this packet.

The guard inspected the complete frozen 131,021-file cache, representing 9,261,675,188 logical bytes. The unchanged full execution schedules 2,724 stat-only guard calls. Multiplying one measured call by that count gives 72,526 seconds, or 20.15 hours, before compiler, exporter and kernel work. This is an empirical guard-cost projection from one call, not a measured full run or mathematical runtime floor. It exceeds the supported 39,600-second inner deadline. No full proof was dispatched. A proposed metadata traversal optimization remains private pending separate review and complete-cache equivalence and timing checks; this receipt changes no checker predicates.

The raw collection stream contained exactly these two kernel warnings:

```text
[  308.647758] watchdog: BUG: soft lockup - CPU#2 stuck for 22s! [swapper/2:0]
[  336.658516] watchdog: BUG: soft lockup - CPU#2 stuck for 48s! [swapper/2:0]
```

They appeared inside the Base64 evidence payload after planning and guard timing. Their cause is unestablished. Reconstruction removes only those two exact inserted strings, then validates the decoded archive against the guest-emitted SHA256 `b61fd3888f777d36cec6a30315b7253abb1326a0ffbf8211efa6d876103de7c0`. All 14 regular guest members match the emitted member manifest. Raw serial is retained unchanged and digest-bound in [serial-interleaving.json](serial-interleaving.json). [control/reconstruct_archive.py](control/reconstruct_archive.py) implements this narrow reconstruction and member validation for a separately supplied raw stream; the raw stream itself is omitted here. The recorded offsets refer to the normalized encoded payload, not file byte offsets.

The host also emitted six `failed to get xsave state: No error` QEMU diagnostics. [warnings.json](warnings.json) preserves their exact diagnostic tail and multiplicity while replacing the private executable path. The supervisor terminated and reaped its owned VM after collection; QEMU returned 1. Guest stage success is therefore accompanied by an explicit host termination receipt, rather than a clean guest shutdown claim. All five retained image/tool pins remained equal.

This packet copies 12 guest files byte-for-byte and projects the phase report to durations, caps, return codes and stream hashes. The 23 MB runtime inventory, host controls, raw serial, VM wrappers, seed and images remain private and digest-bound. Seven of eight host inventory records were downloaded and rehashed. The eighth is the deliberately remote-only stopped child disk, 568,262,656 bytes, SHA256 `15babc4ad6032795e34590dfbb46b339b3acf30f7203c330de85d49fa9ad2dd7`; it is not a missing stage log. These omissions limit complete image reproduction and forensics, and this is not an independently reproducible public VM package. [provenance-bindings.json](provenance-bindings.json) records exact bindings and projections; [manifest.json](manifest.json) binds the public file bytes.

The earlier [authentication diagnostics](../authentication-diagnostics-v1/) and [TCG authenticated plan](../authenticated-plan-v1/) remain separate evidence contexts. An identical serialized runtime hash does not equate their accelerator environments. The source archive and plan used here are the retained authenticated challenge inputs, not a compilation of later research checkpoints.
