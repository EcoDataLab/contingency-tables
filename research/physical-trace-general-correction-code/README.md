# Executable terminal correction on matrix codes

`GeneralCorrectionCode` defines an ordinary computational subroutine on
margin lists, a retained full source-row matrix, ordered defect labels,
natural scales and Boolean bits. It repairs the matrix, checks every large
entry for padding, unpads successful output, counts the ordinary inverse
labels and applies the existing integer-threshold correction coin.

`terminalCorrectionCode_eq` proves pointwise equality with the matrix code
of `terminalBitCorrection` on each actual defect/completion joint and every
reserved suffix. Padding and coin failures remain `none`. The full matrix
and ordered labels are supplied through semantic encoders in this theorem;
extracting them from raw state and residual-draw data is a separate interface.

[Attempt 04](attempt-04/verification.json) passed ordinary Lean compilation
and full assumption audits, with standard axioms only. Attempts 01–03
preserve failed dependent-list and arithmetic-normalization proofs; the
final program uses literal list-range matrix operations. Source and receipt
review is separate AI review, with pinned compiler/imports trusted.

This is a pointwise executable component theorem, not a complete encoded
sampler or running-time bound. For additive replay, set prepared `LEAN_PATH`
and run `bash REPRODUCE.sh NEW_OUTPUT_DIRECTORY`.
