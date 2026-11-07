# Independent AI source and receipt review

22 October 2026. Result: **pass for the stated semantic completion adapter**.
This is a separate AI review of the frozen source and saved compilation/audit
readbacks. The reviewer did not run a compiler replay, a default-target build,
or Comparator. No outside human review is claimed.

Reviewed source: `formal/ResearchComparison/LegacyPhysicalCompletion.lean`,
195 lines, SHA-256
`6a05f58ea287a1e62a28eb6b5b61ad690c4e04735525223610be04cb4defa704`.
Evidence: `attempt-02/verification.json`, compile output and result, and
`attempt-02/audit.stdout.json.gz`. The source hash and compressed audit/object
inventory hashes agree with the receipt.

## Exact statement closed

For natural margins `r : Fin m → ℕ`, `c : Fin n → ℕ`, arbitrary natural `U,L`,
a positive physical state `z : ReducedSmallChain.States r c U L` at the actual
`ReducedSmallChain.capacity`, and precision `h`, assume both computed
large-line lists are nonempty. The adapter constructs the ordinary residual
table margins in computed list order, proves their totals equal, and gives an
entry-preserving equivalence between that table type and the physical
completion fibre above `z`.

On **every** Boolean word of the old draw's exact computed length for those
residual margins, `completionDraw_code` identifies the literal
`LatticeSampler.draw` output with the matrix code of the reindexed physical
completion. Thus every word has a feasible typed fibre interpretation.
For a uniform word of that length, `completionLaw_accuracy` proves total
variation from uniform on the fibre at most `dyadic h = 2^(-h)`.
`oracleFamily_accuracy` transports this bound to every supplied large reference
row and column. Singleton selected blocks are included. Empty selected blocks
are excluded by the two explicit nonemptiness hypotheses.

The row and column code lemmas preserve the actual `largePaddedMargins`
inputs, including the column complement-view rule. Capacity nonrestriction
comes from `physical_paper_capacity`, not a supplied cap premise. Feasibility,
equal residual totals, backend code correspondence and accuracy are proved
inside the closure. No desired sampling law, accuracy bound, density condition,
or program correspondence is assumed. `Classical.choose` selects the typed
witness from the existing `LatticeSampler.draw_spec`; the pointwise code
theorem fixes which executable output it represents. This is a semantic
adapter, not a new executable physical decoder or outer machine.

## Compiled readback checked

The saved successful compilation returned zero in 39.900 seconds, with one
`letI` style warning. The compiled-environment audit returned zero in
156.777 seconds and enumerates 36 module declarations, including 18 theorems.
Every selected declaration and every declaration in all four complete
headline closures has no nonstandard axioms. Their axiom union is exactly
`Classical.choice`, `Quot.sound`, and `propext`.

| Headline in `Math115.LegacyPhysicalCompletion` | Closure size | Contains `Math115.LatticeSampler.draw_spec` |
|---|---:|---|
| `coarseRows_code` | 9,027 | No; it is a residual-input identity |
| `completionDraw_code` | 43,783 | Yes |
| `completionLaw_accuracy` | 43,785 | Yes |
| `oracleFamily_accuracy` | 43,787 | Yes |

These counts overlap. Compiler and reused baseline imports remain trusted;
this is ordinary additive Lean evidence, not strict Comparator acceptance.

## Remaining bridge to the canonical defect trace

The new trace shares the physical residual margins, source capacities,
reference translations and `acceptedCount` algebra used here. The adapter
therefore supplies the approximate uniform source completion required for a
directed acceptance test. It does not identify a trace transition.

The canonical `actualRationalTrace` is on positive **defects**, with clock
`1/[2(4p−3)]` and weighted balanced-star exits
`S(b,e)/Σ_f S(b,f)`. The old `selectedTransitionLaw` is a full-state chain
with a different dyadic clock. The canonical accepted conductance also chooses
reference lines with `Classical.choice`; executable lists choose their first
large lines. A future implementation needs a theorem parameterized by the
computed reference pair, or a proved kernel equality. Uniform completion
under reindexing alone does not prove reference-kernel invariance.

Still required are the finite transition/weighted-exit law, rational or
certified dyadic proposal, capped exit and geometry errors, and a call cap
covering failures. Word lengths here depend on the requested state; common
reservations, fresh conditional blocks and adaptive composition remain open.
The defect stationary law must then be joined to the completion-retaining
repair, padding test and inverse-fibre correction, with initialization,
mixing, retry and precision schedules. Existing general terminal mathematics
and Python code assume positive original margins; the trace theorem permits
zero margins. Zero-margin and other degenerate branches, including empty
defect support and empty completion blocks, need a total wrapper.
Encoded assembly and all added charged costs remain separate obligations.
No new complete sampler, end-to-end runtime exponent, or measured speedup is
established by this adapter.
