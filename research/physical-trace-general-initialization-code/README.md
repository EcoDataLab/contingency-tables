# Executable reference initialization code

`GeneralInitializationCode` computes the greedy fallback matrix, searches
the ordered label pairs and constructs the initial two-view profile in
the exact small-cell catalog order. Its data-producing definitions are
ordinary computational definitions outside the noncomputable proof section.

`positiveTraceInitializationCode_initialStart` identifies the result with
`some (computedStateCode positiveTraceInitialStart)` from the original
ordered margin lists, their equal-total proof and computed reduced
reference tag. The caller supplies no table, starting state or labels.
The equal-total argument to the code is an erased proof precondition.

[Attempt 04](attempt-04/verification.json) passed ordinary compilation and
full module/three-headline assumption audits with standard axioms only.
The preserved earlier attempts record namespace, list-map and dependent
search elaboration failures. The computational definitions did not require
classical semantic decoding.

This closes the initial profile-code correspondence. It does not assemble
the complete coded walk, identify a machine-language realizer or charge
its runtime. The compiler and reused imports remain trusted. For additive
replay, set prepared `LEAN_PATH` and run
`bash REPRODUCE.sh NEW_OUTPUT_DIRECTORY`.
