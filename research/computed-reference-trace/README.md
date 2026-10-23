# Aggregate trace at the computed reference pair

23 October 2026. The aggregate physical defect-trace bound now applies to the
first large row and column selected by the program. The proof constructs the
trace for every fixed reference pair, then specializes to those computed
lines. It retains the existing coefficient and exact rational clock; it does
not assert that different reference pairs produce identical kernels.

The [compiled source](formal/ResearchComputedReference/Trace.lean) uses
`Math115.ComputedReferenceTrace`. Write `p` for the number of small cells,
`w` for physical completion weights, `W` for accepted defect-to-defect
conductance and `S` for accepted balanced-to-defect conductance. The selected
pair is fixed by the margins and cutoff, independently of the current state.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| The actual aggregate variance bound holds at every fixed reference pair. | `referenceTrace_poincare_aggregate` | Finite ordered dimensions, natural margins, a large reference row and column, nonempty positive defect support, `p≥2`, `U≥2`, `L≥7`. Actual capacity, degree, acceptance and full-state variance are derived. |
| The same bound holds at the first computed large row and column. | `computedReferenceTrace_poincare_aggregate` | Finite natural dimensions and margins, both computed large-line lists nonempty, and the preceding support/scale hypotheses. The bound is `Var≤32p³ aggregateCT(r,c,U)·energy`. |
| The off-diagonal transition is `[W(d,e)+Σ_b S(b,d)S(b,e)/Σ_f S(b,f)]/[2(4p−3)w(d)]`. | `computedReferenceTrace_transition` | Both lists nonempty, positive defect support nonempty, `p≥2`, distinct defects. Zero-star terms contribute zero. No padding lower bound is needed for this identity. |
| Stationary mass is `w(d)/Σ_e w(e)`. | `computedReferenceTrace_pi` | The same construction hypotheses, without the distinct-defect condition. |
| The previous canonical transition is recovered at its own abstractly chosen pair. | `referenceTrace_canonical_P` | Nonempty large-row and large-column types, nonempty positive defects and `p≥2`. This is not equality between different reference kernels. |

Singleton selected blocks are included. Zero original margins are permitted
when the stated support and large-line hypotheses hold. Missing reference
lines and empty defect support are outside this packet. The actual bounded
trace transition still requires list-acceptance correspondence, correctly
weighted exits and error accounting. Adaptive fresh words, output correction,
degenerate branches and encoded cost composition also remain open. See the
[completion bridge](../../docs/legacy-completion-backend.md#remaining-interface-to-the-canonical-defect-trace).

## Verification and replay

The [receipt](attempt-03/verification.json) binds the exact published source
to an ordinary Lean 4.34.1 compilation and environment audit. Compilation
took 52.32 seconds and the audit 89.13 seconds. All 34 module declarations,
including 29 theorems, were enumerated. Four complete headline closures have
30,456, 11,668, 11,659 and 11,543 declarations respectively. Only `propext`,
`Classical.choice` and `Quot.sound` occur. The gap closure contains the actual
aggregate variance, padding-seven acceptance, physical degree and harmonic
trace transfer theorems. Reused object hashes match the accepted aggregate
or physical-completion receipts.

This is an additive ordinary compilation with trusted compiler and imported
objects. It is not a fresh default-target or Linux rebuild, strict Comparator
acceptance, independent review, or evidence of a new complete sampler.

The first two failed proofs are preserved with source and diagnostics in
`attempt-01/` and `attempt-02/`. The successful repair changes only the proof
of the canonical-pair identity: it proves the two conductance equalities
before rewriting the chain. No statement or resource limit changed. The
[proof diff](attempt-03/proof-only.diff) and source comparison are retained.
Source and compressed audit bytes are unchanged on publication. The public
receipt projects the local record into the repository receipt schema;
diagnostic paths are replaced by `<repo>` and `<packet>`, with trailing
whitespace removed. Objects and caches are not distributed.

Prepare the pinned compiler and matching imports for
`Research.AggregateDefectTrace`, upstream `Rooted.LargeMarginReference` and
`ResearchAudit.EnvironmentAudit`, together with their package roots. Then:

```sh
LEAN_PATH=<prepared-object-roots> bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

`LEAN_BIN` can override the compiler path. The script compiles this module,
runs the existing environment auditor and checks standard axioms throughout
the headline closures. It does not download or rebuild dependencies. The
script was syntax-checked; the saved compile used these options and identical
source. `python3 scripts/claims_ledger.py --check-readme` replays the saved
receipt checks, including exact types and full dependency closures.
