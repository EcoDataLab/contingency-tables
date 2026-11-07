# Concrete joined step and walk

Combines the incoming transition and balanced-state exit into the actual stronger joined trace and its whole fixed-width walk.

The exit starts after the actual source completion block; uniform reservation slack remains at the end. The pointwise walk theorem supplies the real step correspondence, with no assumed desired law or abstract step contract.

The checked [source](formal/ResearchPhysicalTraceJoin/GeneralJoinedCode.lean) compiled with pinned Lean 4.34.1. The [receipt](attempt-03/verification.json) binds that source, the compressed compiled-environment audit and imported-object hashes. Full module declarations and the selected headline dependency closures were audited; only the standard Lean axioms occur. The compiler and reused imports remain trusted. Separate AI source/evidence review is recorded with this stage; this is not outside human review or strict Comparator acceptance.

Headline statements:

- `Math115.PhysicalTraceJoin.rawJoinedStep_eq`
- `Math115.PhysicalTraceJoin.rawJoinedWalk_eq`

[Attempt history](attempts.json) preserves failed candidates and diagnostics. [Public replay instructions](../repair-accept/INTEGRATION-REPLAY.md) describe building the source closure. `REPRODUCE.sh` replays this module when its documented pinned dependencies are already available.

Attempt 02 passed compilation and the Lean environment audit, then failed imported-object authentication because a transitive receipt was missing. Attempt 03 supplied the complete accepted dependency inventory and passed all stages. The earlier attempt is retained as a postcheck failure.
