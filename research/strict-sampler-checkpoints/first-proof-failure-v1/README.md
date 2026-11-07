# First bounded cold proof attempt: hash-sidecar drift

The first actual cold serial proof attempt stopped at its first dependency gate. Lake returned zero after 3.022 seconds and reported that all 3,101 dependency jobs were current. The after-stage cache guard then rejected metadata drift at:

```text
formal/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/Field/Defs.olean.server.hash
```

No module build completed. The original real sandbox preflight passed; the dependency service supplied eight valid compiler observations, with sampled peak zero. No exporter, default-kernel replay or Comparator stage ran. This is a preserved failure, not strict sampler acceptance, an OOM finding or a two-hour timeout. The logs establish changed sidecar metadata; they do **not** establish unchanged sidecar content.

[evidence/proof-output/receipt.json](evidence/proof-output/receipt.json) retains both attempted stage records and exact commands. The dependency [stdout](evidence/proof-output/0000_dependencies_current.stdout.log), [stderr](evidence/proof-output/0000_dependencies_current.stderr.log) and enclosing [proof error](evidence/proof.stderr.log) are byte-identical authenticated guest members. The command was `lake --no-cache --no-build build +Math115.LatticeCompletion:deps`, under the original sandbox and owned service. The unchanged stat identity policy caught the write; no cache exemption or skipped gate was introduced.

The attempt used a fresh cold source/output context, 10 GiB RAM, one vCPU, explicit WHPX, no NIC or swap, and a 7,200-second serial dispatch deadline. Installation, original sandbox preflight and original authentication passed. The enclosing proof phase failed after 110.258 seconds; VM lifetime was 374.832 seconds. All owned processes closed, all five retained image/tool pins remained equal, and the process inventory was clear at terminal collection. QEMU was terminated by its owned supervisor after collection; its exit code is preserved in [outcome.json](outcome.json).

All 21 regular raw guest members were strict-decoded and authenticated against the emitted archive SHA256. This minimal packet copies only failure/phase/resources/progress and exact proof-stage logs/receipt. The complete private archive, raw serial, controls and stopped child disk are hash-bound in [provenance-bindings.json](provenance-bindings.json). The unchanged runtime inventory remains SHA256 `e391c457d01020a0e384aa25af657417c127145be21695bd6d469bea418855d4` and is already supplied in the prior [versioned guard packet](../versioned-guard-v2/). It is not duplicated here.

Changed guest/seed/ISO controls are supplied under `source/`; original v2/authenticator/installer/media inputs and commands are referenced in [reproduction-references.json](reproduction-references.json). Private host VM wrappers/images remain omitted, so this is not an independently reproducible whole VM. Every completed stage remains in the receipt; no automatic duplicate attempt followed the failure.

This attempt checked the historical retained 679-module sampler closure, source archive `47e864e49025da1e505c32ae1c5f23428ed900b1ecc64468cb72478095824a84` and source-freeze `2a15fa398282a2825cc773b5e5110f8bacc4fbc2af9f28afb88f1b326c1b93bd`. It did not check the new research modules in `e40c471`. Pre-admission hash-memo preparation is being investigated separately; this failure packet claims no repair or subsequent success.
