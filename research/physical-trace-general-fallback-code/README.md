# Legacy and deterministic branch code

Thin ordinary wrappers reuse the frozen sampler, its exact word width, the greedy fallback and ordered zero restoration. Every reserved word agrees with the typed fallback branch, including precision zero.

These wrappers preserve the existing backend at its own scales. They add no new sampler law, numerical runtime bound or branch-preservation assumption.

The checked [source](formal/ResearchPhysicalTraceJoin/GeneralFallbackCode.lean) compiled with pinned Lean 4.34.1. The [receipt](attempt-02/verification.json) binds that source, the compressed compiled-environment audit and imported-object hashes. Full module declarations and the selected headline dependency closures were audited; only the standard Lean axioms occur. The compiler and reused imports remain trusted. Separate AI source/evidence review is recorded with this stage; this is not outside human review or strict Comparator acceptance.

Headline statements:

- `Math115.PhysicalTraceJoin.rawPositiveLegacyWordWidth_eq`
- `Math115.PhysicalTraceJoin.rawPositiveLegacyReducedWordCode_eq`
- `Math115.PhysicalTraceJoin.rawPositiveLegacyWordCode_eq`
- `Math115.PhysicalTraceJoin.rawPositiveDeterministicWordCode_eq`

[Attempt history](attempts.json) preserves failed candidates and diagnostics. [Public replay instructions](../repair-accept/INTEGRATION-REPLAY.md) describe building the source closure. `REPRODUCE.sh` replays this module when its documented pinned dependencies are already available.
