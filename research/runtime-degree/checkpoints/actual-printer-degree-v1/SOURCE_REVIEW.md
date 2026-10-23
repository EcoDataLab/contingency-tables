**Independent source and evidence review — 11 October 2026.**

**Pass: no source, statement, or saved-evidence blocker found for the printer
certificate.** The compiled endpoint identifies the exact pinned
`OAI.ContingencyTables.GreedyFeasibleTable.printMatrixRealizer` and supplies one
natural-coefficient polynomial, chosen before the input, with degree at most
4 bounding its charged work plus the encoded output weight for every
`List (List Nat)` input. The input measure is the fixed codec's encoded tree
weight. This is an upper degree certificate, not a tightness or measured-time
claim.

The defining pinned program is
`flatMapPoly (flatMapPoly LiteralCodec.natWordRealizer)`. The new proof uses
that program's actual cost field; `natWord_eq` identifies its natural-word
output with `encodeNat`, and the final readback explicitly charges
`weight (GreedyFeasibleTable.printMatrix rows)`. Neither the headline nor its
pointwise endpoint requires rectangularity, feasibility, matching totals,
successful parsing, an input-size promise, or a desired printer-cost bound.
Consequently empty outer lists, empty rows, ragged row lengths, zero entries,
and arbitrary natural values are within the quantified domain.

The affine transformations preserve the fixed realizers and charged outputs.
Affine composition substitutes a proved linear semantic output-weight bound
into the second cost polynomial; it retains the first and second work charges
and the final output. Append retains its reversal and list-cons fold. Flatten
retains its reversal and append fold. Their intermediate-prefix bounds use
the encoded append, reverse, flatten, and prefix weight identities. Eager map
retains every mapped construction, bounds the accumulated mapped prefix, and
charges the final reversal. The generic affine-output premises are then
proved for the actual bit conversion, natural-word encoder, and row printer.
This yields natural-word degree 2, row degree 3, and outer printer degree 4;
the literal Symbol output uses `weight_word = 18*length+1`.

Read-only verification passed for all 26 files in the prepared manifest, both
new source/object bindings and successful defining compilation receipts,
the compiler and driver hashes, raw audit streams, and the 16 explicit
prerequisite source/object bindings. The two public proof sources match the
frozen defining inputs byte for byte:

- `LinearCollections.lean`: `7839ffe7bb9c651e1497ff09f244b19455bc5c2cc1c095264e60c1a34c695eb0`.
- `PrinterDegree.lean`: `cfdb1af28a5df1d7f8b0bb93d6bd7077dd0d18d865346f15b1a5b432ed861bfb`.

The saved stream passed the ordered 25-name checker and exact actual-printer
type readback. Every named transitive axiom report is within `propext`,
`Classical.choice`, and `Quot.sound`. This review inspected the sources and
replayed the saved evidence checks; it launched no compiler, cache scan,
default build, or prepared public-path reproduction.

The remaining-five interpretation is consistent with the actual
`ActualDrawSeams` record and the passed earlier branch packet. Printer degree
4 and branch degree 1008 can be weakened to a common sufficiently large
certificate degree, but the five other exact realizer fields still need
their own numerical charged-work-plus-output certificates: `initial`,
`fallback`, `referenceTrial`, `unitTrial`, and `retryWords`. Closing the printer
therefore does not determine the complete draw degree `t`. The historical
draw expression `8*(1+k*(k+1))*k^5` and public runtime expression
`340*max(1008,t)` retain their conditional status.
