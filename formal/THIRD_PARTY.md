# Formal source attribution

The source checkout is pinned to
[OpenAI math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb),
whose Lean code is licensed under Apache-2.0.

The following local files adapt its proofs, with new statements and changes
marked in their headers:

- `Math115/TransportRefinement.lean` and `Math115/WidthWeightedTransport.lean`
  adapt `IntegerRootTransport.lean` and use its unchanged exported definitions.
- `Math115/GlobalDisplayOwnership.lean` restates the existing
  `IntegerLeafEnergy.max_removeOne` proof before adding global special-slot,
  adjacent-level, and prefix recovery statements.
- `Math115/RepairCoefficient.lean` generalizes the scalar argument in
  `IntegerRootEstimate.root_coefficient_after_repair`.

The original proof tree is downloaded by the bootstrap script and is not
vendored into this repository. The new formal files retain Apache-2.0 licensing.
Mathlib and Lean are obtained from their original repositories/toolchain and
retain their own licenses.
