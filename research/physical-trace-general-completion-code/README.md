# Computed completion requests

Computes the frozen completion sampler's coarse margins, exact requested bit count, residual draw and retained source matrix from raw margin/profile/word data.

Correspondence assumes actual profile encodings and the stated nonempty large-line lists. It does not change the frozen sampler or its costs.

The checked [source](formal/ResearchPhysicalTraceJoin/GeneralCompletionCode.lean) compiled with pinned Lean 4.34.1. The [receipt](attempt-03/verification.json) binds that source, the compressed compiled-environment audit and imported-object hashes. Full module declarations and the selected headline dependency closures were audited; only the standard Lean axioms occur. The compiler and reused imports remain trusted. Separate AI source/evidence review is recorded with this stage; this is not outside human review or strict Comparator acceptance.

Headline statements:

- `Math115.PhysicalTraceJoin.rawCoarseMargins_eq`
- `Math115.PhysicalTraceJoin.rawCompletionBits_eq`
- `Math115.PhysicalTraceJoin.rawCompletionResidual_eq`
- `Math115.PhysicalTraceJoin.rawCompletionResidual_terminal`
- `Math115.PhysicalTraceJoin.rawCompletionSource_terminal`

[Attempt history](attempts.json) preserves failed candidates and diagnostics. [Public replay instructions](../repair-accept/INTEGRATION-REPLAY.md) describe building the source closure. `REPRODUCE.sh` replays this module when its documented pinned dependencies are already available.
