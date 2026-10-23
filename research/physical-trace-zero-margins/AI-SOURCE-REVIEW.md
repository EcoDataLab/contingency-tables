# Separate AI source review

Reviewed frozen source: `formal/ResearchPhysicalTraceJoin/ZeroMargins.lean`.

Source SHA-256: `0437fa3a69f9b4cd779369ea62ee820084f5ffd68288b4a60ef7a5763340edeb`.

Final-source reconciliation: attempt 04 added `Equiv.symm` to the extension-entry proof's existing simplification list, exposing the inverse function of the explicit equivalence record. Attempt 05 only excludes `Equiv.invFun_as_coe` from that list to avoid reversing this unfolding in a simplifier loop. No definition, theorem statement, hypothesis, or mathematical scope changes from attempt 03.

A separate AI reviewer checked the ordinary-table equivalence, literal entry formulas, probability-law transport, and README scope. No mathematical or hypothesis mismatch was found. A feasible nonnegative table has zero entries in every zero-margin row or column, by its actual margin equalities and nonnegative summands. `zeroMarginSupportedEquiv` merely attaches this support proof and forgets it in the inverse direction. Composing it with the existing `rectangleCompletionEquiv` restricts exactly to positive-margin row and column subtypes and restores removed entries by literal nested-if zero insertion. No arbitrary feasible table is selected.

The generic `RestrictedTable` alias elaborates the subtype finite instances with opaque predicates, matching the pinned rectangle equivalence before specializing to positive margins. This changes the elaboration route, not the mathematical restricted table space. The retained restriction-entry theorem and explicit four-case extension-entry proof expose the same literal maps. The inverse identities are inherited from the equivalence, including empty positive-index types and zero total margins. The equivalence itself has no equal-total, nonempty-support, ordering, cutoff, or positive-original-margin hypothesis.

Restoration of laws is transport through the inverse bijection. The existing `variation_equiv` identity preserves TV exactly between any two reduced-table laws, and `uniform_equiv` restores the uniform reduced-table law to the uniform original-table law. Equal original totals derive both required nonempty table spaces using the existing table existence theorem and the explicit equivalence. The TV-to-uniform corollary therefore compares the correct two uniform targets, without conditioning, error amplification, or an assumed approximation bound.

Reconciliation against attempt 01 found the generic alias repair, an explicit summand argument for `Finset.single_le_sum`, and replacement of the extension-entry `rfl` by case analysis through the named equivalence definitions. Apart from the new auxiliary generic alias and the corresponding specialization, the mathematical definitions, theorem interfaces, hypotheses, and scope are unchanged. The README accurately keeps verification pending and distinguishes this ordinary-table law interface from the physical defect construction.

This module does not implement list preprocessing or choose a retained-index order, transport physical cutoffs or masks, establish nonempty defect support, initialize a defect walk, repair a physical completion joint, supply finite-word code, complete a sampler, or prove runtime bounds.

Full compilation and assumption auditing were pending for this frozen candidate when this note was written. The separately reported minimal generic-alias probe does not verify the full module. This is AI source review, not human expert review or an independent kernel check.

Final result: attempt05 failed compilation in the extension-entry proof. No assumption audit ran. The semantic review does not establish a checked module.
