# Initialized finite-word reference sampler

`ResearchPhysicalTraceJoin.GeneralCompleteReference` supplies the actual
defect start, feasible fallback, linear retry count and both precision
settings from the ordered input lists and requested natural accuracy.
It returns ordinary tables on the original lists through exact zero
restoration. `positiveReferenceWord_law` identifies the flat word with the
proved scheduled law; `positiveReferenceWord_accuracy` bounds its total
variation by `2^-t`.

The hypotheses are equal original natural-margin totals and the computed
positive-list reference branch. The input includes no supplied starting
state, fallback table or success/accuracy premise. The typed construction
retains noncomputable semantic components; this packet does not identify
an encoded program or bound running time.

[Attempt 01](attempt-01/verification.json) passed ordinary Lean 4.34.1
compilation and the full module/two-headline assumption audit. Only the
standard axioms `propext`, `Classical.choice`, and `Quot.sound` occur in
the audited closures. The compiler and reused imports remain trusted;
this is not a new default-target Linux build or strict Comparator replay.
The [integration guide](../../docs/hybrid-finite-word-sampler.md) describes
the surrounding construction and separate AI review.

For an additive rerun with the pinned compiler and prepared dependency
objects, set `LEAN_PATH` and run `bash REPRODUCE.sh NEW_OUTPUT_DIRECTORY`.
The new directory receives the compiler output and full environment audit;
existing evidence is not overwritten.
