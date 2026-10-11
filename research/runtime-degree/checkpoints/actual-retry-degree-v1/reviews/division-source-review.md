**Independent division/quotient source and evidence review — 11 October 2026.**

**Pass; ready to bundle as a shared helper for the actual retry-cost
certificate.** `typed_division` and `typed_quotient` name the pinned literal
`TreeTyped.division` and `TreeTyped.quotient` realizers. Their existing `Typed`
contract supplies one polynomial of natural degree at most 4, uniformly over
every natural operand pair, bounding the actual charged work plus encoded
output. The successfully compiled audit source also unwraps this contract
into the unconditional inequalities for `(a/b,a%b)` and `a/b`.

Divisor zero is covered explicitly. The original division program tests
`0<divisor`; its other branch returns `(0,dividend)`, matching the literal
natural-number division and remainder semantics. The quotient realizer is
the existing composition of this full division with the first projection,
so its certificate retains the work of producing the remainder and the
projection charge. No nonzero-divisor or normalized-remainder premise is
added to either cost endpoint.

The one-bit division step is certified at degree 1 using the actual
comparison, addition, doubling and subtraction programs. Its fold envelope
`40X+10` is derived from the pinned bit-size growth lemma and unchanged
divisor field for arbitrary initial divisor, quotient and remainder.
Every processed-prefix state is charged. The degree-1 step with a linear
state envelope gives fold degree 2; the actual bits/reversal preparation has
degree 2; their composition gives core degree 4. The original conditional
division and final quotient projection retain degree 4. This is an upper
certificate in the fixed charged tree model, not a tightness or measured
execution-time claim.

Read-only checks passed for both successful defining source/object receipts,
the five selected imported-helper source/object bindings, the exact copied
comparison/subtraction seed bodies and their provenance digest, the literal
division/quotient degree-4 type readbacks, and six ordered transitive axiom
reports. All reported axioms are within `propext`, `Classical.choice`, and
`Quot.sound`. Defining source SHA256:
`5e03bc8b825b6d0cbfecf77b6454db781ec2fe40c7ca55d644b94e3d9b4dff3c`;
defining object SHA256:
`a84f0a08cdf0d87dde72b119d873baa7f7652118400388a23559c3c587b1aa03`.

No compiler, test suite or dependency/cache inventory was run for this
review. The upcoming retry certificate still needs its own completed
composition and saved evidence; this helper does not supply that endpoint.
