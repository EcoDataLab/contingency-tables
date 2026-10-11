# Default-target integration

The complete bounded-sampler theorem remains proved at the published `fe72b20` checkpoint: one fixed machine gives feasible output on every random tape and total variation error at most `2^-h` within uniformly polynomial time, for equal-total natural margins and numeric `h≥1`. Its [exact statement map and evidence](outer-sampler-compiler-checkpoint.md) include empty dimensions and zero margins.

This integration promotes the checkpoint's thirteen source files into `formal/Math115/` and imports them through the default root. Each file's SHA-256 must match its entry in the preserved [checkpoint ledger](../formal/results/native-sampler-checkpoint/checkpoint.json) and [source bundle](../formal/results/native-sampler-checkpoint/sources/Math115/). The proof bytes are unchanged; the default import graph and audit configuration are expanded. Creation-time source headers remain unchanged; current exact-hash receipts determine verification status.

Fresh aggregate and Linux verification of the expanded target are **pending**. The planned roster contains 1,511 focused inclusion requests plus six standalone requests. The [default audit contract](../formal/default-audit-contract.json) requires 22 headline closures and the three private-helper obligations already checked in the complete checkpoint. These are verification requirements, not new passing counts. The claims ledger has no current aggregate receipt for the changed target until a new source-bound result is reviewed.

The earlier [aggregate](../formal/results/completion-aggregate-1236/verification.json), [compiled-environment audit](../formal/results/environment-aggregate-1236/README.md), and [Linux reproduction](../formal/results/linux-focused-df469a5/README.md) remain valid historical receipts for their exact configurations. The separate complete-checkpoint audit remains evidence for the identical sampler sources; it does not certify this new default root.

To verify the promoted target, run the repository workflow from its root in an exclusive checkout:

```sh
bash scripts/bootstrap_lean.sh
bash scripts/verify_lean.sh standalone
bash scripts/verify_lean.sh focused --serial
```

The focused workflow includes the compiled-environment audit. Preserve the complete logs, source/object hashes, import closure, statement types, axiom reports, and before/after inventories. Linux reproduction uses the same serial workflow and existing resource caps; serial execution limits concurrent compilers, not the memory used by one compiler. Official dependency caches and ordinary Lean/compiler inputs remain trusted. Passing Python checks does not verify these Lean targets.

The numerical complete runtime degree and practical sampler performance remain unknown. Strict Comparator acceptance of this sampler still needs its own complete run; the [tested tiny fixture](../formal/results/strict-comparator-smoke/README.md) verifies only that fixture. Human mathematical review, benchmarks against matching target laws, and held-out application validation remain separate obligations in the [contributor handoff](handoff.md).
