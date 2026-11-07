# Separate AI source review

Final checked source SHA-256: `c59da9d490d2a8ff204a6d82da7cffe921132698e615805b07656738fe5b928b`.

Reviewed frozen source: `formal/ResearchPhysicalTraceJoin/TracePreparation.lean`.

Source SHA-256: `c59da9d490d2a8ff204a6d82da7cffe921132698e615805b07656738fe5b928b`.

The packet's README and claim/hypothesis table were also checked against this source and preserve the distinction between preparation tags and implemented sampling branches.

Final-source reconciliation against attempt 02 found the explicit `LargeMarginSemantics` import for the computed index equivalence and case-split/simplification repairs in branch-specification proofs. Definitions, theorem statements, hypotheses, and mathematical scope are unchanged.

A separate AI reviewer checked the scale formula, actual list guards, semantic branch specifications, deterministic law statement, and retuning fixture. No mathematical or hypothesis mismatch was found. `traceCutoff` uses the dimensions of the supplied lists and agrees exactly with the existing `squareCutoff` on `List.ofFn` margins. The large-line and small-cell guards reuse the actual `largeIndices` and `smallCellCatalog`, and the catalog-length theorem connects them to the actual first-paper small-cell type.

The classifier tests dimensions at most one first. Its later reference tag requires both dimensions at least two, at least two actual small cells, and nonempty computed large lists. It asserts no defect nonemptiness or supplied start. Since the first-paper mask is a union of full rows and columns, any nonempty mask in dimensions at least two contains at least two cells; thus the residual no-small tag corresponds exactly to zero actual small cells. The unit tag is preparation terminology, not identification of a new finite-word unit sampler.

The deterministic theorem proves that all ordinary tables in its dimension branch coincide, using the opposite margin equation for any existing cell. Empty index types are covered because there is then no cell to consider. It compares the point law of a supplied feasible table with the correct uniform table law; it neither selects that table nor implements the deterministic branch. Equal totals derive the nonempty uniform target. No accuracy premise is introduced.

The concrete retuning theorem checks cutoffs 726 and 418 and tags unit and no-small for the displayed original and reduced margin lists. The lists have the same ordinary total, but changing dimensions changes the prescribed cutoff and mask. This correctly demonstrates that branch decisions must be recomputed when the dimension-based scale is retuned. It does not identify physical states, completion fibres, proposal clocks, or trace kernels across those scales. A fixed externally chosen cutoff remains a different interface whose premises must be checked separately.

The module classifies supplied lists. It does not filter zero margins, connect a filter implementation, initialize defects, assert a universal defect start after preprocessing, construct a new outer table draw, prove physical-state transport, complete a sampler, or establish implementation costs or runtime bounds. The earlier checked zero-margin table equivalence alone supplies none of those physical or algorithmic statements.

The saved attempt-03 receipt reports successful full compilation and assumption audit of 61 declarations, 31 theorems, and five complete headline dependency closures, using only standard axioms. Its source hash matches this reviewed source. These are separate evidence from source review. The earlier preflight import failure is not a compiler result for this source. This is AI source review, not human expert review or an independent kernel check.

The final ordinary compilation and full assumption audit are recorded separately in this packet.
