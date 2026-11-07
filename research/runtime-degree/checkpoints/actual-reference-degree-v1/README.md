# Exact reference packed-trial degree certificate

The original `Math115.LatticeOuterProgram.packedTrialRealizer` now has an
unconditional numerical `Typed` certificate. `Typed` bounds charged tree-machine
work plus the original encoded output uniformly in the original input weight.
It covers every raw parameter tuple, including invalid dimensions/catalogues,
ragged or invalid rows/views, arbitrary precision/schedule values, zero-width,
short and extra words, and rejection/fallback outcomes.

Import `ReferenceRuntime.PackedTrialDegree` and use
`Math115.ReferenceRuntimeNext.typed_actual_packedTrial`. Its conservative bound
K is the exact 591-digit natural in `reference-degree.json`; no desired work
inequality, successful-output witness or valid-input assumption is supplied.
The main original programs and codecs are unchanged.

The actual parser, cap-guarded profile walk, neighbor/repair/filter/dedup proposal,
step and terminal completion samplers, full dense transitions, all eager retries,
binary greedy fallbacks, decoder, normalization/permutation and outer checks
remain charged. The terminal cost uses the independently proved cubic output
bound from the original profile fold; the walk's work bound is not reused as
its encoded state size.

18 defining reference modules compiled with pinned Lean4.34.1, j2/M8192.
34 saved focused type/axiom checks report only `propext`, `Classical.choice`,
and `Quot.sound`. `SOURCE_REVIEW.md` records independent source/binding review.
`final-verification.json` binds all successful source/object/receipt bytes,
ordinary reused prerequisites, selected checks and the exact literal degree.
The two failed attempts are retained and explicitly classified as failures;
neither failed attempt supplies an accepted object or theorem.

This packet includes exact source bytes for those 18 modules and 12 previously
private frozen normalization/completion/metadata/map prerequisites. Existing
unit/repair/retry, generic-degree and pinned upstream OAI/Math115 sources remain
ordinary prerequisites from their reviewed packets/repository. This is a source
and evidence packet: object caches, compiler runtimes and new audit frameworks
are not duplicated. `source-projection.json` maps the accepted defining bytes
to the intended published source paths.

For a focused reproduction, compile these module roots in a fresh output prefix
using the existing pinned Lean4.34.1 and reviewed prerequisite object prefixes:

1. `AffineMapWith.Degree`, `AffineMapWith.ChunkExample`.
2. The five `InputNormalization` sources in dependency order.
3. `ReferenceRuntime.DecoderDegree`, `CompletionPrepareDegree`,
   `DenseLayoutDegree`, `DenseWidthCoreDegree`, `DenseTrialWidthDegree`,
   `CanonicalBitCountDegree`, `DenseAcceptanceDegree`, `DenseExponentDegree`,
   `DenseTransitionDegree`, `DependentChunksDegree`, `DenseOffsetDegree`,
   `DenseTrialConstructionDegree`, `CompletionReservationDegree`.
4. `CompletionRuntime.EntryOutput`, `ValidDegree`, `MatrixDegree` and
   `ReferenceMetadata.TranslationDegree`, `ResidualDegree`.
5. `ReferenceRuntime.DenseDrawDegree`, `CompletionDrawDegree`,
   `OuterWordParsingDegree`, `ProfileStepDegree`, `PackedTrialDegree`.

Use `lean -j2 -M8192 -DautoImplicit=false --root=<packet> -o <fresh-object>
<source>` with `LEAN_PATH` beginning with the fresh object prefix, followed
by the existing reviewed prerequisite prefixes. The receipt's import path
records identify the originally selected prerequisites. Do not invoke a default
sampler build or rebuild all upstream dependencies. Inline final endpoint and
axiom readbacks reproduce with the defining modules.

This certificate closes the reference-trial field. Complete publicDraw/public
machine-time composition is a separate packet. No sampler speed measurement,
minimal exponent, fresh standalone environment rebuild or strict challenge
acceptance is claimed here.

Published with the [complete explicit-degree theorem](../complete-explicit-degree-v1/). The sources and successful evidence are exact copies of the reviewed stage. Earlier prerequisite receipts keep their recorded scopes.
