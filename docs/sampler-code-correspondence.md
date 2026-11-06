# Executable components of the stronger sampler

The [complete ordinary list-and-bit program](executable-sampler.md) now composes
these components. This page records the initial component interfaces; later
wrappers compute the labels and coarse margins internally and supply the
accepted walk, corrected trial, retry and zero-restoration correspondence.

Four checked pointwise correspondences connect ordinary computational
list/natural/Boolean definitions to parts of the typed finite-word sampler.
They preserve the existing mathematical operations for every valid encoded
input and every supplied word. No new approximation error is introduced.

| Component | Computational operation | Pointwise correspondence | Input boundary |
|---|---|---|---|
| Initialization | Greedy fallback, first passing ordered label pair, two inverse profile views | `positiveTraceInitializationCode_initialStart` | Original lists, erased equal-total proof; computed reference tag in the theorem. No supplied table, start or labels. |
| Rational-clock proposal | Capped interval draws followed by raw ordered neighbor lookup | `rawClockNeighborDraw_eq` | Actual encoded physical state, actual denominator and finite Boolean word. No runtime semantic decoder. |
| Terminal correction | Matrix repair, full padding test, unpadding, literal inverse count and bounded coin | `terminalCorrectionCode_eq` | Actual full retained source matrix and ordered repair labels, with a supplied bit suffix. |
| Retained completion reconstruction | Combine reached-state small entries with the actual residual block before correction | `jointSourceMatrixCode_draw`, `jointTerminalCorrectionCode_eq` | Encoded actual reached state and residual draw; ordered repair labels remain explicit. The frozen-draw theorem uses existing typed coarse-margin parameters. |

All names are in `Math115.PhysicalTraceJoin`. These data-producing functions
are ordinary Lean definitions outside the noncomputable proof sections.
The specifications and correspondence proofs can use standard classical
axioms. This distinguishes executable component code from the partly
noncomputable semantic representation used by the
[all-input finite-word theorem](hybrid-finite-word-sampler.md).

The raw neighbor list keeps its exact order and multiplicity. An accepted
interval index pointing to an unused proposal slot produces `none`; it does
not incorrectly retry that slot. Matrix reconstruction deliberately uses
output padding zero so it retains entries below L before repair and the
padding test. The correction program preserves both padding failures and
coin failures. Initialization uses the exact catalog order, including the
complement convention for its second view.

The later [complete program](executable-sampler.md) computes the ordered defect
labels and coarse margins from raw state codes, composes the accepted trace
and exact word slices, and identifies its output with the typed map. A
machine-language realizer and charged-cost composition remain to be supplied.

| Packet | Successful receipt |
|---|---|
| [Initializer code](../research/physical-trace-general-initialization-code/) | [attempt-04](../research/physical-trace-general-initialization-code/attempt-04/verification.json) |
| [Raw neighbors](../research/physical-trace-general-raw-neighbors/) | [attempt-04](../research/physical-trace-general-raw-neighbors/attempt-04/verification.json) |
| [Terminal correction](../research/physical-trace-general-correction-code/) | [attempt-04](../research/physical-trace-general-correction-code/attempt-04/verification.json) |
| [Retained reconstruction](../research/physical-trace-general-joint-code/) | [attempt-03](../research/physical-trace-general-joint-code/attempt-03/verification.json) |

All four passed ordinary compilation and full module/headline-closure
audits; only `propext`, `Classical.choice`, and `Quot.sound` occur. The
[separate AI source and receipt review](../research/physical-trace-general-joint-code/AI-SOURCE-REVIEW.md)
records exact sources, input boundaries and checks. The compiler and reused
imports remain trusted. Failed candidates are retained. These checks are
separate from fresh unified Linux replay and strict Comparator acceptance.
