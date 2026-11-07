# A spanning lower bound for inverse repair labels

Every ordinary table with positive row and column margins has at least p-1 valid ordered inverse labels, where p counts the union of small rows and small columns. Consequently max(c0,p-1) is a valid allowance.

Natural subtraction covers empty and degenerate cases. No large-line or residual-slack assumption is needed for this count theorem. The current sampler still uses c0; the stronger numerator has not been installed.

The checked [source](formal/ResearchPhysicalTraceJoin/GeneralAugmentedLower.lean) compiled with pinned Lean 4.34.1. The [receipt](attempt-03/verification.json) binds that source, the compressed compiled-environment audit and imported-object hashes. Full module declarations and the selected headline dependency closures were audited; only the standard Lean axioms occur. The compiler and reused imports remain trusted. Separate AI source/evidence review is recorded with this stage; this is not outside human review or strict Comparator acceptance.

Headline statements:

- `Math115.PhysicalTraceJoin.inverseSupportCount_spanning_lower`
- `Math115.PhysicalTraceJoin.augmentedInverseSupportAllowance_le_count`

[Attempt history](attempts.json) preserves failed candidates and diagnostics. [Public replay instructions](../repair-accept/INTEGRATION-REPLAY.md) describe building the source closure. `REPRODUCE.sh` replays this module when its documented pinned dependencies are already available.
