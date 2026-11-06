# A shorter complete typed sampler with the same law

The alternative `tightHybridSampler` retains the current classifier, deterministic and legacy branches, initialization, correction numerator, outer retries and precisions. Its reference branch uses the tighter completion reservations throughout the joined walk, fresh terminal completion, correction and complete retries. The total width is no larger, and its output law is exactly the existing hybrid law for every equal-total input and natural t.

This is a complete **typed** alternative over a different finite-word domain. The current ordinary `rawHybridSamplerCode` still uses the old widths; no raw shorter-word output adapter or revised encoded realizer is claimed. Exact equality of output distributions supplies the same feasibility/accuracy guarantee, without asserting equality on the same input word or measured running time.

The [source](formal/ResearchPhysicalTraceJoin/GeneralTightSampler.lean) passed ordinary Lean compilation and the [full assumption audit](attempt-03/verification.json). Only standard axioms occur; the compiler and reused imports remain trusted. Separate AI source and receipt review checks the full composition. [Attempt history](attempts.json) preserves the initial dispatcher elaboration failure. No strict Comparator acceptance is claimed.

Top-level statements are `tightHybridSampler_width_le_old`, `tightHybridWordLaw_eq` and `tightHybridWord_accuracy`. The receipt lists their complete dependency closures and the intermediate trial/retry/reference statements.

See the [refinement guide](../../docs/sampler-refinements.md), [reserved-word comparison](../../docs/reservation-comparison.md) and [shared source replay](../repair-accept/INTEGRATION-REPLAY.md).
