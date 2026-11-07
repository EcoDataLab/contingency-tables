# Executable rational-clock neighbor selection

`GeneralRawNeighbors` supplies ordinary computational code for capped
interval selection and raw neighbor-list lookup, preserving the exact
catalog order and out-of-range behavior of the actual rational-clock
proposal. Its runtime path does not call the semantic state decoder.

The pointwise theorem on actual encoded physical states says that the raw
result equals `Option.map computedStateCode` of the typed proposal. The
full ordered-neighbor-list equality preserves multiplicities; accepted
unused proposal slots stay `none` rather than triggering another retry.
The zero-attempt and zero-width cases follow the existing capped-index
and fresh-word conventions.

[Attempt 04](attempt-04/verification.json) passed ordinary Lean compilation
and the full module/two-headline assumption audit, with standard axioms
only. Earlier namespace and dependent-width elaboration failures are
preserved. The pinned compiler and reused imports remain trusted; the
separate AI review is not independent kernel replay.

This verifies a computational proposal component on valid encoded input.
It does not assemble the accepted trace walk or revised encoded sampler,
nor establish its running time. Set prepared `LEAN_PATH` and run
`bash REPRODUCE.sh NEW_OUTPUT_DIRECTORY` for an additive rerun.
