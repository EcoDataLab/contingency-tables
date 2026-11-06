# Computable stronger-chain schedules

List catalogs, indicator sums and natural arithmetic compute all walk counts, precisions, completion/step/trial widths and outer retry reservations used by the checked typed reference sampler.

These are exact formula correspondences, including positive retry-chunk width. They do not establish a smaller full runtime or change the schedule.

The checked [source](formal/ResearchPhysicalTraceJoin/GeneralScheduleCode.lean) compiled with pinned Lean 4.34.1. The [receipt](attempt-02/verification.json) binds that source, the compressed compiled-environment audit and imported-object hashes. Full module declarations and the selected headline dependency closures were audited; only the standard Lean axioms occur. The compiler and reused imports remain trusted. Separate AI source/evidence review is recorded with this stage; this is not outside human review or strict Comparator acceptance.

Headline statements:

- `Math115.PhysicalTraceJoin.rawUniformCompletionBits_eq`
- `Math115.PhysicalTraceJoin.rawScheduleSteps_eq`
- `Math115.PhysicalTraceJoin.rawTerminalScheduleWordWidth_eq`
- `Math115.PhysicalTraceJoin.rawPositiveWordWidth_eq`
- `Math115.PhysicalTraceJoin.rawPositiveTrialWordWidth_positive`

[Attempt history](attempts.json) preserves failed candidates and diagnostics. [Public replay instructions](../repair-accept/INTEGRATION-REPLAY.md) describe building the source closure. `REPRODUCE.sh` replays this module when its documented pinned dependencies are already available.
