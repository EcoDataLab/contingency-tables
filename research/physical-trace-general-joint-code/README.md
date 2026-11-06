# Reconstructing the retained completion on codes

`GeneralJointCode` computes the full retained row-view matrix from the
reached physical state's list code and the actual residual matrix code.
It reuses the existing listed reconstruction with output padding set to
zero, preserving entries below the padding threshold until the repaired
matrix is tested. Premature unpadding would change the required failure rule.

`jointSourceMatrixCode_eq` identifies that reconstruction pointwise with
the actual retained full source matrix. `jointSourceMatrixCode_draw`
identifies its residual input with the frozen executable completion draw.
`jointTerminalCorrectionCode_eq` then composes the computational repair,
padding test, unpadding, inverse count and bounded coin.

The ordered repair labels remain supplied through their semantic encoder.
The frozen-draw theorem also uses the existing typed coarse-margin
parameters; computing those parameters from raw state data is a further
program interface. No extra probability error or runtime bound is asserted.

[Attempt 03](attempt-03/verification.json) passed clean ordinary compilation
and full module/three-headline assumption audits with standard axioms only.
Earlier namespace and catalog-rewrite failures are retained. The pinned
compiler and reused imports remain trusted. Set prepared `LEAN_PATH` and
run `bash REPRODUCE.sh NEW_OUTPUT_DIRECTORY` for an additive replay.
