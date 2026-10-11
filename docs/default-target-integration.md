# Default-target integration

The complete bounded-sampler theorem remains proved at the published `fe72b20` checkpoint: one fixed machine gives feasible output on every random tape and total variation error at most `2^-h` within uniformly polynomial time, for equal-total natural margins and numeric `h≥1`. Its [exact statement map and evidence](outer-sampler-compiler-checkpoint.md) include empty dimensions and zero margins.

This integration promotes the checkpoint's thirteen source files into `formal/Math115/` and imports them through the default root. Each file's SHA-256 must match its entry in the preserved [checkpoint ledger](../formal/results/native-sampler-checkpoint/checkpoint.json) and [source bundle](../formal/results/native-sampler-checkpoint/sources/Math115/). The proof bytes are unchanged; the default import graph and audit configuration are expanded. Creation-time source headers remain unchanged; current exact-hash receipts determine verification status.

The expanded target **passed fresh hosted Linux verification** at `5b4af402a281a9bc02a38adb168f7b0bfde5d3aa`. The [receipt](../formal/results/linux-focused-5b4af40/README.md) binds ordinary compilation of the 685-module submitted closure, all 1,511 focused named audits, and the complete selected environment: 25,448 declarations, including 18,054 theorem constants, 11,951 imported modules and 22 headline dependency closures. The [default audit contract](../formal/default-audit-contract.json) also checks three private helpers and two program-identity closures. Six standalone names were checked for inclusion in the environment; no separate standalone named replay ran in this job, so the named count is 1,511. The claims ledger now binds this exact passing receipt. Official dependency caches, compiler and platform inputs remain trusted; strict Comparator was not run.

The earlier [aggregate](../formal/results/completion-aggregate-1236/verification.json), [compiled-environment audit](../formal/results/environment-aggregate-1236/README.md), and [Linux reproduction](../formal/results/linux-focused-df469a5/README.md) remain valid historical receipts for their exact configurations. The separate complete-checkpoint audit remains evidence for the identical sampler sources; it does not certify this new default root.

The full offline collector validated the new artifact against its immutable run
commit. A separate AI reader has now completed the independent saved-artifact
readback, including source bindings, ordered named records, the full selected
environment and all 22 headline closures. The
[publication record](../formal/results/linux-focused-5b4af40/review.json) and
[compact statement index](../formal/results/linux-focused-5b4af40/headline-index.json)
record that result. The
[earlier interrupted review](../formal/results/linux-focused-5b4af40/review-partial.json)
is preserved, and the original evidence bytes are unchanged. This is additional
artifact inspection, not an independent compiler run or human mathematical
review. The integration PR remains unmerged at this checkpoint.

To verify the promoted target, run the repository workflow from its root in an exclusive checkout:

```sh
bash scripts/bootstrap_lean.sh
bash scripts/verify_lean.sh standalone
bash scripts/verify_lean.sh focused --serial
```

The focused workflow includes the compiled-environment audit. Preserve the complete logs, source/object hashes, import closure, statement types, axiom reports, and before/after inventories. Linux reproduction uses the same serial workflow and existing resource caps; serial execution limits concurrent compilers, not the memory used by one compiler. Official dependency caches and ordinary Lean/compiler inputs remain trusted. Passing Python checks does not verify these Lean targets.

The numerical complete runtime degree and practical sampler performance remain unknown. Strict Comparator acceptance of this sampler still needs its own complete run; the [tested tiny fixture](../formal/results/strict-comparator-smoke/README.md) verifies only that fixture. Human mathematical review, benchmarks against matching target laws, and held-out application validation remain separate obligations in the [contributor handoff](handoff.md).
