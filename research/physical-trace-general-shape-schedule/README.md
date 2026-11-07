# Shape-aware retry schedule

Keeps the existing correction numerator c0 and chooses the exact reciprocal block ceil(2p(p-1)/c0). The checked budget gives the target dyadic accuracy with no more retries or precision than the current linear schedule.

This is an alternative typed retry law with supplied actual start/fallback, plus exact computational parameter correspondence. It does not alter the current whole program. Minimality concerns the integer product-cover block, not optimal runtime.

The checked [source](formal/ResearchPhysicalTraceJoin/GeneralShapeSchedule.lean) compiled with pinned Lean 4.34.1. The [receipt](attempt-04/verification.json) binds that source, the compressed compiled-environment audit and imported-object hashes. Full module declarations and the selected headline dependency closures were audited; only the standard Lean axioms occur. The compiler and reused imports remain trusted. Separate AI source/evidence review is recorded with this stage; this is not outside human review or strict Comparator acceptance.

Headline statements:

- `Math115.PhysicalTraceJoin.shapeCeiling_le_iff`
- `Math115.PhysicalTraceJoin.positiveTraceShapeBlock_eq_ceiling`
- `Math115.PhysicalTraceJoin.positiveTraceShapeBlock_le_iff`
- `Math115.PhysicalTraceJoin.positiveTraceShapeBlock_success`
- `Math115.PhysicalTraceJoin.positiveTraceShapeAttempts_le_linear`
- `Math115.PhysicalTraceJoin.positiveTraceShape_budget`
- `Math115.PhysicalTraceJoin.positiveTraceShapeScheduled_accuracy`
- `Math115.PhysicalTraceJoin.positiveTraceShapeBlock_code`
- `Math115.PhysicalTraceJoin.positiveTraceShapeScheduleData_code`
- `Math115.PhysicalTraceJoin.shapeSchedule_fixture10`
- `Math115.PhysicalTraceJoin.shapeSchedule_fixture20`

[Attempt history](attempts.json) preserves failed candidates and diagnostics. [Public replay instructions](../repair-accept/INTEGRATION-REPLAY.md) describe building the source closure. `REPRODUCE.sh` replays this module when its documented pinned dependencies are already available.
