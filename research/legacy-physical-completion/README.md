# Completion adapter at arbitrary outer scales

22 October 2026. The frozen complete sampler now has a compiled semantic
adapter to the newer chain's physical completion fibers. It applies at
arbitrary natural cutoff `U` and padding `L`, including `L=7`, when both
computed large-line lists are nonempty. This closes the residual-input and
completion-law interface; it does not implement the new outer sampler.

For an actual positive physical state `z`, the adapter constructs residual
margins in computed list order and proves their totals equal. For every word
of the old program's exact requested length, `LatticeSampler.draw` produces
the matrix code of a feasible residual table corresponding to a physical
completion of `z`. Uniform words give total variation at most `2^(-h)` from
uniform on that fiber. The guarantee transports to every reference-line pair.

All statements below are in `Math115.LegacyPhysicalCompletion` in the
[compiled source](formal/ResearchComparison/LegacyPhysicalCompletion.lean).

| English claim | Lean statement | Hypotheses |
|---|---|---|
| The residual inputs are the actual physical program's row and column lists. | `coarseRows_code`, `coarseColumns_code` | Natural `U,L`, actual physical state, the corresponding nonempty large-line list, and a cell enumeration. The column complement view is preserved. |
| The ordinary residual table is equivalent to the physical completion fiber, preserving entry order. | `finiteFibreEquiv`, `finiteFibreEquiv_entry` | Both large-line lists nonempty; actual physical capacity. Cap redundancy and equal residual totals are proved. |
| Every exact-length word has the stated feasible physical interpretation of the actual old executable output. | `completionDraw_code` | Same state and list hypotheses; any natural precision `h`; exact computed word length. |
| The physical completion law is within `2^(-h)` of uniform. | `completionLaw_accuracy` | Same hypotheses; uniform word at the computed length. No accuracy premise. |
| The same bound holds in every reference coordinate system. | `oracleFamily_accuracy` | Same hypotheses and any selected large reference row/column. |

The typed witness uses `Classical.choose` on the existing executable
`LatticeSampler.draw_spec`. Its pointwise code identity identifies the
program output; the witness is not a new executable decoder. Singleton
selected blocks are included; empty selected blocks are outside this adapter.
Word width is state-dependent. Shared word reservations, fresh conditional
bits, a bounded trace transition, output correction and encoded costs remain
separate. The [bridge note](../../docs/legacy-completion-backend.md#remaining-interface-to-the-canonical-defect-trace)
records the exact transition and reference-choice obstructions.

## Verification and replay

The [receipt](attempt-02/verification.json) records a successful ordinary
Lean 4.34.1 compilation and an environment-derived audit of all 36 module
declarations, including 18 theorems, with four complete headline dependency
closures. The three backend closures all contain
`Math115.LatticeSampler.draw_spec`. Only `propext`, `Classical.choice` and
`Quot.sound` occur. The [separate AI review](REVIEW.md) checked frozen source
and receipts without a second compiler run. No human review, new Linux
default build or strict Comparator acceptance is claimed.

The failed first tactic attempt and the successful run's one `letI` style
warning are retained. Source and audit bytes are unchanged on publication;
the receipt's source location is updated to the identical public copy, and
diagnostic paths use `<repo>` and `<packet>` with trailing whitespace removed.
Compiler and reused dependency
objects remain trusted. No executable objects or caches are distributed.

Prepare the pinned compiler and matching dependency objects, including
`Math115.LatticeSampler`, the pinned upstream `ListedCompletion`, and
`ResearchAudit.EnvironmentAudit`. Set `LEAN_PATH` to those object roots and
the required package roots, then run from this directory:

```sh
bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

`LEAN_BIN` can override the repository's compiler path. The script compiles
only the adapter, runs the existing environment auditor, and checks standard
axioms throughout the headline closures. It neither downloads dependencies
nor rebuilds the baseline. It was syntax-checked; the saved compile used the
same options and exact source before publication. The repository's existing
`scripts/claims_ledger.py --check-readme` validates the saved receipt, exact
types, full dependency closures, object inventory and public source binding.
