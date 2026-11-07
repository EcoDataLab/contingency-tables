# All-input typed finite-word sampler

`ResearchPhysicalTraceJoin.GeneralHybridSampler` chooses a reserved bit
width and map together. On the computed positive-list reference branch it
uses the stronger chain, with actual initialization and the linear outer
schedule supplied internally. The deterministic branch consumes zero bits;
other shapes use the existing complete finite-word sampler at its own
proved scales. All branches restore original zero-margin positions exactly.

`hybridWord_accuracy` gives total variation at most `2^-t` for every
equal-total pair of natural margin lists and every natural precision `t`,
including zeros and empty lists. `hybridWord_feasible` establishes feasible
ordinary-table output for every individual word. `hybridSampler_reference`
identifies the stronger backend on the actual computed reference branch.

The map has noncomputable semantic components. This packet closes an
all-input typed sampling specification, not the revised encoded program,
its charged costs or a smaller complete-runtime exponent.

[Attempt 02](attempt-02/verification.json) passed ordinary Lean 4.34.1
compilation and the full module/three-headline assumption audit. All audited
closures use only `propext`, `Classical.choice`, and `Quot.sound`. Attempt 01
preserves a dependent-rewrite elaboration failure; factoring the finite-word
law as a function of the whole width/map pair fixed it without changing
the sampler or theorem hypotheses.

The [separate AI review](AI-SOURCE-REVIEW.md) covers all eight new integration
modules. The pinned compiler and reused imports remain trusted. This is
not a fresh default-target Linux build or strict Comparator replay. See
the [construction and remaining program interface](../../docs/hybrid-finite-word-sampler.md).

To rerun this additive module with prepared pinned dependencies, set
`LEAN_PATH` and run `bash REPRODUCE.sh NEW_OUTPUT_DIRECTORY`. Existing
evidence is never overwritten.
