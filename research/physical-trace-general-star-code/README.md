# Raw balanced-state exit

Uses the existing dyadic proposal, frozen balanced-source completion, defect projection and ordered fixed-block first success with the original entering defect as fallback.

This is the balanced-state exit used by the joined trace. Its exact and longer-reserved-word equations preserve source width and fallback-valued successes; no cost bound is claimed.

The checked [source](formal/ResearchPhysicalTraceJoin/GeneralStarCode.lean) compiled with pinned Lean 4.34.1. The [receipt](attempt-03/verification.json) binds that source, the compressed compiled-environment audit and imported-object hashes. Full module declarations and the selected headline dependency closures were audited; only the standard Lean axioms occur. The compiler and reused imports remain trusted. Separate AI source/evidence review is recorded with this stage; this is not outside human review or strict Comparator acceptance.

Headline statements:

- `Math115.PhysicalTraceJoin.rawBalancedTest_eq`
- `Math115.PhysicalTraceJoin.rawDyadicNeighborDraw_eq`
- `Math115.PhysicalTraceJoin.rawStarStep_eq`
- `Math115.PhysicalTraceJoin.rawStarTrial_eq`
- `Math115.PhysicalTraceJoin.rawStarExit_eq`
- `Math115.PhysicalTraceJoin.rawStarExit_eq_reserved`

[Attempt history](attempts.json) preserves failed candidates and diagnostics. [Public replay instructions](../repair-accept/INTEGRATION-REPLAY.md) describe building the source closure. `REPRODUCE.sh` replays this module when its documented pinned dependencies are already available.
