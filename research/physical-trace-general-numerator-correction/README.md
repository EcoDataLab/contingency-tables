# Stronger inverse-fibre correction allowance

A generic common valid correction numerator gives exact successful point mass, bounded-coin error and fresh-retry accuracy. The checked choice C=max(c0,p-1) supplies ideal success at least 1/(2p) and error at most (1-1/(2p))^R+R*(2^-h+2^-k).

This additive law uses actual positive reduced margins, an actual start/fallback and supplied h,k,R. It does not change the current raw coin c0, install a new schedule or claim a new gap/runtime exponent.

The [source](formal/ResearchPhysicalTraceJoin/GeneralNumeratorCorrection.lean) passed ordinary pinned Lean compilation and its [full assumption audit](attempt-01/verification.json). The receipt binds source, object, compiled audit and imported-object inventory. Only standard axioms occur; the compiler and reused imports remain trusted. Separate AI source/receipt review passed. No strict Comparator or independent kernel acceptance is claimed.

Headline statements:

- `Math115.PhysicalTraceJoin.terminalNumeratorIdeal_success`
- `Math115.PhysicalTraceJoin.terminalNumeratorTrial_accuracy`
- `Math115.PhysicalTraceJoin.terminalNumeratorRetry_accuracy`
- `Math115.PhysicalTraceJoin.terminalAugmentedNumerator_le_count`
- `Math115.PhysicalTraceJoin.augmentedInverseSupportAllowance_ratio_lower`
- `Math115.PhysicalTraceJoin.actualShape_terminalAugmented_success_lower`
- `Math115.PhysicalTraceJoin.actualShape_terminalAugmentedRetry_accuracy`

[Attempt history](attempts.json) retains failed candidates and diagnostics. See the [refinement guide](../../docs/sampler-refinements.md) and [shared public replay](../repair-accept/INTEGRATION-REPLAY.md).
