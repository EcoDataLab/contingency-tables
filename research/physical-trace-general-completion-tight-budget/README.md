# A tighter uniform completion-bit bound

Bounds the same frozen completion program using its actual fixed residual dimension, a count bound and a mass bound. The minimum with the previous allowance is proved to bound every actual source request and never exceed that allowance.

The scalar bound is checked. Existing full sampler reservations are unchanged; a shorter-word adapter and whole-program composition are separate obligations.

The checked [source](formal/ResearchPhysicalTraceJoin/GeneralCompletionTightBudget.lean) compiled with pinned Lean 4.34.1. The [receipt](attempt-02/verification.json) binds that source, the compressed compiled-environment audit and imported-object hashes. Full module declarations and the selected headline dependency closures were audited; only the standard Lean axioms occur. The compiler and reused imports remain trusted. Separate AI source/evidence review is recorded with this stage; this is not outside human review or strict Comparator acceptance.

Headline statements:

- `Math115.PhysicalTraceJoin.completionBudget_totalReservedBits_mono`
- `Math115.PhysicalTraceJoin.completionBits_le_rawTight`
- `Math115.PhysicalTraceJoin.rawTightCompletionBits_le_old`

[Attempt history](attempts.json) preserves failed candidates and diagnostics. [Public replay instructions](../repair-accept/INTEGRATION-REPLAY.md) describe building the source closure. `REPRODUCE.sh` replays this module when its documented pinned dependencies are already available.
