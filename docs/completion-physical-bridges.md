# Completion in physical coordinates

Seven additional bridge modules now have authenticated native Lean evidence for
**193 named declarations**. They connect computed profile proposals, the actual
completion program's list order, empty completion fibres, reference-coordinate
laws, and the physical schedule and bit allowance. The
[verification record](../formal/results/completion-physical-bridges/verification.json)
contains the exact source snapshots, executed audit drivers, logs, and dependency
provenance. This is a component checkpoint; the aggregate count and Linux
integration are unchanged.

| Module | Audited declarations | Result |
|---|---:|---|
| [AdaptiveDenseCompletion](../formal/Math115/AdaptiveDenseCompletion.lean) | 24 | Separates dense dimension, geometric dimension, and dilation in a finite Boolean completion experiment. |
| [CompletionOuterSchedule](../formal/Math115/CompletionOuterSchedule.lean) | 2 | Instantiates the physical dense-law error bound with explicit walk, restart, and precision schedules. |
| [CompletionRandomBudget](../formal/Math115/CompletionRandomBudget.lean) | 6 | Identifies the physical reservation and proves its bit-count bounds. |
| [PhysicalComputedProposal](../formal/Math115/PhysicalComputedProposal.lean) | 69 | Computes the catalogue and proposal code, with exact decoded proposal law. |
| [PhysicalReferenceWalk](../formal/Math115/PhysicalReferenceWalk.lean) | 21 | Proves finite-law mixing and completion bounds for supplied reference coordinates. |
| [ListedLatticeCompletion](../formal/Math115/ListedLatticeCompletion.lean) | 32 | Identifies the actual completion program with a physical completion in computed list order. |
| [PhysicalEmptyCompletion](../formal/Math115/PhysicalEmptyCompletion.lean) | 39 | Reconstructs the unique completion fibre when either large-index set is empty. |

## Computed proposals and list order

`PhysicalComputedProposal` builds the small-cell catalogue from the encoded
margin lists. Its state decoder identifies valid profile codes. For equal-total
margins, its neighbor proofs show that codes emitted from a valid state decode
to physical neighbors.
The catalogue order supplies the cell equivalence used throughout the proposal.
The typed catalogue and fibre equivalences are noncomputable semantic proof
wrappers; the
pointwise code identities identify the executable list programs.

At the ideal scales `U = 5d³` and `L = 3d`, the program computes the cutoff and
prepares its own profile-check input. `idealPreparedProposal_eq` identifies each
returned code after decoding. With equal row and column totals,
`idealPreparedProposal_law` proves the whole normalized physical proposal law,
including the unused-word mass. The preparation and proposal have polynomial bounds on charged execution cost
plus encoded output weight, in their complete encoded inputs.

`ListedLatticeCompletion` handles physical states with at least one large row
and one large column. It uses the computed large-index lists and their reference
positions, preserves their entry order, and proves the residual dimensions,
equal totals, strong margin bounds, and common Boolean-word allowance needed by
the [encoded completion program](completion-sampler-program.md).

`programTable_code` proves a pointwise identity between the actual list program
and the finite table returned on each reserved word. The state-dependent required
prefix fits the common reservation. Transport through `finiteFibreEquiv` gives
`completionDraw`; its uniform-word law is within `2⁻ʰ` of the uniform physical
completion fibre. This includes the dense and bounded-retry fallbacks already
analyzed by the completion program.

The oracle family transports that same chosen completion into any supplied
reference coordinates. `referenceDraw_law` and `outerLaw_variation` identify its
reference law and bound the resulting abstract outer law. These arguments do
not assume that different orderings produce identical approximate dense laws.

## Empty completion and reference laws

When either large-index set is empty, every cell is retained by the profile.
`PhysicalEmptyCompletion` reconstructs the row and column views from the
computed catalogue and profile code. The completion fibre is then a singleton,
so the returned point law equals its uniform law exactly. The reconstruction
program has a polynomial realizer bounding charged execution cost plus encoded
output weight.

This output is a completion fibre containing a **pair of row and column views**.
It becomes an ordinary table only when the separate balance test succeeds.
This component does not identify the unit-branch walk or an entire outer program.

`PhysicalReferenceWalk` proves mixing and approximate-completion bounds for the
chain belonging to a supplied reference pair. Its ideal specialization uses
`U = 5d³`, `L = 3d`, equal totals, and a supplied feasible fallback. These are
finite-law statements; they do not identify a Boolean implementation of the
whole walk.

## Schedules and bit allowances

`CompletionOuterSchedule.denseOuterLaw_explicit_accuracy_half` instantiates the
previous physical dense outer law with the computed walk count, restart count,
and separate step and terminal precisions. For equal-total margins and a feasible
fallback, its total-variation bound is `2⁻⁽ʰ⁺¹⁾`, hence at most `2⁻ʰ`. The listed
completion bridge has its own reference-law bound; no equality with a different
approximate outer law is asserted.

`CompletionRandomBudget` identifies a state-independent reservation of

\[
 R\bigl[T(s+F_{\rm step})+F_{\rm terminal}\bigr]
\]

bits: proposal and completion words at each transition, plus a separate terminal
completion word in each attempt. With `M` the row total and
`N = d + clog₂(M+2) + h + 3`, it proves both a separated bound proportional to
`d²⁰(h+3)N⁶⁴` and a combined bound proportional to `N⁸⁵`, using the explicit
constant `budgetCoefficient`. These count reserved random bits. They do not
measure runtime, construct the entire word bank, or bound a final public machine.

## Independent dilation parameters

`AdaptiveDenseCompletion` leaves the dense dimension `D`, geometric allowance
`g`, and positive dilation `k` independent. Its accuracy theorem requires
`D ≥ 14`, full row and column dimensions at most `D`, free dimension at most
`D` and `g−1`, `g ≥ 1`, and `k ≥ 2g`. Coarse row and column margins must satisfy
the respective `3g` strong-margin bounds, and each enlarged fine margin must be
at least `D¹²`. Equal totals, a feasible fallback, and the stated finite-box
Prékopa–Leindler and finite-grid Cheeger inputs remain explicit.

Under those hypotheses, the actual canonical Boolean fine draw and bounded
completion retry attain the dyadic error bound. No comparison between `D` and
`g`, automatic parameter selection, or performance improvement is proved.
A separate zero-bit singleton draw covers one-row or one-column tables when a
feasible fallback is supplied; it is not installed as an automatic branch of
the completion draw.

The seven modules passed fresh named audits against their exact compiled
objects. Six objects were reused; `ListedLatticeCompletion` compiled freshly in
batch6 with one style warning preserved in its log. The record distinguishes
reuse markers, inherited historical metadata, and available predecessor compile
receipts. `PhysicalReferenceBoolean`, the complete Boolean outer walker, and
the public sampling machine remain outside this verified checkpoint.
