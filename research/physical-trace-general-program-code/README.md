# Complete ordinary list sampler

Computes branch dispatch, the searched initializer, trial blocks, fallback and zero restoration from ordinary lists, naturals and Booleans. The width and every-word output agree with the all-input typed sampler.

The public entry point checks equal totals internally. Correctness covers all complete reserved words on equal-total inputs, including zeros, empty lists and t=0. The reused retry maps all blocks before selecting the first success: no early-return or charged-time saving is established.

The checked [source](formal/ResearchPhysicalTraceJoin/GeneralProgramCode.lean) compiled with pinned Lean 4.34.1. Its [receipt](attempt-03/verification.json) binds the source, compiled object, full module audit and selected headline dependency closures. Only standard Lean axioms occur; the compiler and reused imports remain trusted. Separate AI source and evidence review is recorded for this stage. No revised encoded realizer, charged runtime theorem or strict Comparator acceptance is claimed.

Headline statements:

- `Math115.PhysicalTraceJoin.rawCorrectedRetryCode_eq`
- `Math115.PhysicalTraceJoin.rawPositiveReferenceWordCode_eq`
- `Math115.PhysicalTraceJoin.rawHybridWordWidth_eq`
- `Math115.PhysicalTraceJoin.rawHybridSamplerCode_eq`

[Attempt history](attempts.json) retains failed candidates and diagnostics. [Public replay instructions](../repair-accept/INTEGRATION-REPLAY.md) describe the shared source build. `REPRODUCE.sh` checks this module when its documented dependencies are already available.
