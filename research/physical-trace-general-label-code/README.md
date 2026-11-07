# Ordered defect labels from both stored views

The literal catalog search derives the unique ordered defect labels from both profile views. The resulting correction takes only the raw state, retained residual matrix and correction bits.

The theorem identifies actual state/residual encodings. It preserves padding failure, coin failure and the exact word; arbitrary malformed encodings are outside that contract.

The checked [source](formal/ResearchPhysicalTraceJoin/GeneralLabelCode.lean) compiled with pinned Lean 4.34.1. The [receipt](attempt-03/verification.json) binds that source, the compressed compiled-environment audit and imported-object hashes. Full module declarations and the selected headline dependency closures were audited; only the standard Lean axioms occur. The compiler and reused imports remain trusted. Separate AI source/evidence review is recorded with this stage; this is not outside human review or strict Comparator acceptance.

Headline statements:

- `Math115.PhysicalTraceJoin.orderedDefectLabelIndices_eq`
- `Math115.PhysicalTraceJoin.orderedDefectLabelCode_eq`
- `Math115.PhysicalTraceJoin.jointAutoCorrectionCode_eq`

[Attempt history](attempts.json) preserves failed candidates and diagnostics. [Public replay instructions](../repair-accept/INTEGRATION-REPLAY.md) describe building the source closure. `REPRODUCE.sh` replays this module when its documented pinned dependencies are already available.
