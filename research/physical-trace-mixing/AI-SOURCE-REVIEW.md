# Separate AI source review

Final checked source SHA-256: `800fe9713c5a4a757bd5e7d5c5f8ddeefbb1d20c172cd898dc64d77e10401ea1`.

Reviewed frozen source: `revisions/attempt-02/formal/ResearchPhysicalTraceJoin/Mixing.lean`.

Source SHA-256: `800fe9713c5a4a757bd5e7d5c5f8ddeefbb1d20c172cd898dc64d77e10401ea1`.

Final-source reconciliation: attempt 02 adds only `open Math115.PhysicalStationarySuccess` to resolve `Fibre`. The definitions, theorem statements, hypotheses, proofs, and mathematical scope are otherwise unchanged from the reviewed first attempt.

A separate AI reviewer checked the source and found no semantic or hypothesis mismatch in the stated mixing interface. The rational stationary law normalizes completion-fibre counts over defect vertices only. Its real cast agrees with the stationary law of the same computed-reference defect trace used by the ideal joined kernel. The lower bound on stationary mass follows from positive integral fibre counts and the existing full physical-mass allowance; the balanced-versus-defect partition is used in the correct direction.

The ideal walk bound uses the existing aggregate Poincare theorem, with `K = 32 * p^3 * aggregateCT` and the proved lower bound on stationary mass. The literal fair-word walk bound then adds the previously proved finite-walk perturbation error, giving `T * dyadic t + B * exp(-T / K)`, where `B` is the existing physical mass allowance. The source reserves exactly `T * uniformStepWidth` input fair bits. No new runtime or inverse-gap exponent is asserted.

The final theorem explicitly requires equal original totals, `U >= 2`, `L >= 7`, at least two small cells, nonempty computed large-row and large-column lists, nonempty defect support, and a supplied starting defect. It does not impose positivity on every original margin. No comparison between different reference pairs or assumed Poincare premise is introduced.

This is a bound for chosen finite parameters `(T, t)` and a completion-weighted target law on defects. It does not assert that the actual fixed-precision kernel has that law as its stationary distribution or converges exactly to it as `T` grows at fixed `t`: the displayed perturbation allowance grows as `T * dyadic t`. It supplies neither a uniform table law nor initialization, terminal table sampling, output correction, whole-attempt restart, a complete sampler, or encoded-machine cost bounds.

Compilation and assumption auditing are separate evidence. The parent reported successful compilation of this frozen source; its assumption audit was pending when this reconciliation was written. This is AI source review, not human expert review or an independent kernel check.

The final ordinary compilation and full assumption audit are recorded separately in this packet.
