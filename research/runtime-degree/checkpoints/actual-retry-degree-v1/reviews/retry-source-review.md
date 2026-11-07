**Independent retryWords source and evidence review — 11 October 2026.**

**PASS for the requested parser certificate.** No semantic, degree-arithmetic,
literal-DAG, all-input, or hidden-premise gap was found in the reviewed source
and saved focused audit. This is a source/evidence review; no compiler or
dependency rebuild was run.

`Math115.RetryRuntimeNext.typed_actual_retryWords` certifies the literal
`Math115.LatticeOuterProgram.retryWordsRealizer` at degree **42914304**.
`Typed` expands to one polynomial over natural coefficients, of degree at most
that allowance, uniformly bounding charged realizer cost plus encoded output
by evaluation at encoded input weight. The audit prints the expanded
`actual_retryWords_polynomial` with the exact original realizer cost, actual
`retryWords z` output, and `∀ z : RetryData`, with no input premise. RetryData
is the unrestricted product of trial parameters, fallback MatrixCode,
attempt count, and supplied Boolean list. No feasibility, well-formedness,
positive width, bounded precision, or exact word-length condition appears.

The complete original `Math115.LatticeOuterProgram` is imported by the final
module. I independently compared the thin helper program bodies against the
pinned original BooleanChunkProgram: chunk and complete-row bodies match
after whitespace removal; chunks match after the two declared helper aliases.
The compiled actual bindings then name the original realizers directly. This
preserves multiplication, actual quotient, bounded drop/take, range, eager
mapWith, and the original retry prefix preparation. No alternate parser or
early-success loop replaces the charged DAG.

The degree arithmetic checks are: listLength 2; dropFast 2; takeFast 8; chunk
`6*2*8 = 96`; actual quotient 4; length/quotient preparation `2*4 = 8`; bounded
range retains 8 because its numeric count is at most supplied list length;
eager mapWith `2*(1+96*(96+1)) = 18626`; chunks `8*18626 = 149008`;
profile/attempt widths 1/6/6; retry bank `6*6 = 36`; prefix preparation
`36*8 = 288`; final parser `288*149008 = 42914304`. Generic composition
charges both repeated width calculations and every eagerly constructed chunk.

The numeric iteration gates are proved from the existing data: dropFast uses
the minimum of requested drop and stored list length with a sublist invariant;
range uses `length / width ≤ length`; mapWith derives its accumulator envelope
from the pointwise cost-plus-output certificate and prefix length. No desired
runtime bound is supplied as a premise. The shared quotient degree-4 helper
is unconditional on both natural operands, including divisor zero. Thus zero
width yields no row indices; short words yield only complete chunks; surplus
words are truncated at the original bank width. These cases still retain all
prefix/quotient/range work in the charged expression. Arbitrary fallback and
configuration data contribute encoded input weight without adding a validity
condition.

Evidence readbacks passed for 39 selected source/object/frozen/compiler/driver
and successful compilation-to-audit digest comparisons. The current original
LatticeOuterProgram source matches its preserved source snapshot, and the
BooleanChunkProgram digest matches both its source binding and preserved input
snapshot. The two original import objects match the owner reuse-map digests;
the original LatticeOuterProgram object also matches its locally preserved
provenance object. All 25 requested axiom reports occur exactly once, in driver
order, and agree with verification.json; each uses only `propext`,
`Classical.choice`, and `Quot.sound`. The saved audit exits zero with empty
stderr and prints the unconditional actual endpoint. Final source SHA256:
`f99a096ec1364fb8cdef055c6b7209e9464321febe4baa44a4d27822e23a97df`;
final object SHA256:
`04c3fd597d90c1949d7a89f43cf67c2be763c44b9f46eeb8c3604b5cf1fe8a3d`.

The audit is focused and transitive for its named declarations, not an
exhaustive compiled-environment inventory or fresh dependency replay. Imported
compiler/cache objects remain a trust boundary; the remote BooleanChunkProgram
provenance path is represented by the owner's authenticated export/reuse
receipt rather than directly reopened here. The dormant ActualChunkBridge
source is outside the compiled final import chain and supplies no endpoint
evidence. The degree is a conservative upper certificate in the fixed charged
tree model, not an optimal exponent, lower bound, or measured runtime.
Packed trials, complete draw/sampler runtime, output recovery, and physical
machine runtime remain outside this certificate and unknown.
