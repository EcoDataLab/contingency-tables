# Exact completion adjustments against the source definitions

`formal/Math115/CompletionAdjustment.lean` connects the elementary completion
calculations in `docs/scale-audit.md` to the pinned OpenAI Lean source. The
complete module has compiled with Lean 4.34.1 and `autoImplicit=false` against
OpenAI commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. A private audit of
15 public declarations found only `propext`, `Classical.choice`, and
`Quot.sound`; the scalar row-major conditional statement needs only the
first and third. There are no admissions or new axioms. Compilation emitted
two style-only tactic-sequencing warnings and no errors.

The source represents the fixed reference row and column by `none`, with
other lines represented by `some`. The new exact identities use its actual
`CompletionTranslation.star`, rather than defining a different translation:

- a row transfer is the difference of two matrix units on the reference
  column;
- a column transfer is the difference of two matrix units on the reference
  row;
- simultaneous unit increases are the two reference-arm units minus the
  reference-center unit;
- simultaneous decreases negate that last matrix.

Coincident matrix positions combine algebraically. Every elementary family
therefore has entry magnitude at most one, support at most three, at most
two negative cells in either orientation, and an orientation with at most
one negative cell. Singleton rectangles are included by allowing an empty
nonreference index type. Empty rectangles have no reference cell and are
outside the `star` theorem's type; their deterministic-completion branch
is proved separately: `empty_rectangle_card_one` gives cardinality one for
any nonempty ordinary fiber with no rows or no columns, and
`physical_empty_completion_weight` obtains that nonemptiness from an actual
physical state's positive weight.

The physical bridge retains the source feasibility assumptions: both
endpoints are `PhysicalStates`, and their residual completion total fits
the formal large-cell capacity. Here `B` is the source's array of cell
capacities, not the scalar dense cutoff also called `B` in the manuscript.
It extracts one shared coordinate pair
from `IntegerExchangeAdjacent`. The signed row and column margin changes
then expose all four doubled-coordinate view combinations. This also
strengthens the source's pointwise residual-change bound from two to one.

A restriction lemma prevents the invalid shortcut of dropping one endpoint
of a transfer that lies outside the large rectangle. It requires the
margin change to vanish off the included rows or columns. The actual
physical bridge proves that condition using the source's zero-residual
lemmas, then applies its fixed `Equiv.optionSubtypeNe` reference indexing.
No edge-family classification is assumed in the final physical exchange
statement.

The main exchange export is `exchange_reference_adjustment_bounds`.
`repair_reference_adjustment_bounds` and
`repair_reverse_reference_adjustment_bounds` give the corresponding bounds
for both repair directions. Reversing a move uses its proved
`ElementaryMargins` classification; the numeric fields of `Bounds` alone
would not imply the negative-support bound for the reverse matrix.

For an actual repair, the proof uses the source `repairMatrix` and
`repairedProfile`. The contribution outside retained cells is exactly the
indicator of the receiving cell `(t.row,s.column)`. A small receiver gives
zero completion-margin changes; a large receiver adds one to exactly its
row and column. The source defect, repaired-capacity, endpoint-feasibility,
and profile-equality hypotheses are retained explicitly.

The row-major conditional statement uses the source's existing prefix and
special-entry lemmas. Given `q(s)=ell`, the repaired special entry equals
`ell` for a receiver in the same row and `ell-1` otherwise. Every position
strictly before `s` is unchanged. This is an exact conditional-level and
prefix statement; it does not assert arbitrary prefix feasibility without
the source defect and endpoint hypotheses. `repaired_profile_prefix` also
proves the equality for both doubled-coordinate views, using the source
profile's capacity bound to recover the complemented coordinate.

`translation_rejection_iff` formalizes the exact zero-entry criterion for
rejection. `singleton_translation_nonnegative` handles a single completion
row or column: the reference adjustment is the literal difference between
the target and source tables. A target-table witness is explicit, so the
result does not assume the target fiber is nonempty without evidence.

The source interfaces used here are `SignedMarginTranslation` and
`ReferenceCompletionBlock` for the fixed reference translation;
`SmallCoordinateSums`, `PhysicalOriginalResiduals`, and
`PhysicalResidualMargins` for actual endpoint margins; and
`PhysicalRepairMargins` and `RepairPrefixes` for the source repair. The
bridge strengthens these interfaces without modifying their definitions.

These bounds support the manuscript acceptance calculation: a negative
unit adjustment rejects precisely when its source completion entry is
zero, and at most two cells need this check. The finite proposal acceptance
count is handled in the separate acceptance module. Dense-bin geometry,
the full reduced-scale ideal chain, and its bounded-machine implementation
remain separate integration obligations. This module does not by itself
certify the reduced dense `A,B` scales or an end-to-end sampler.
