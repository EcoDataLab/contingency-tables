# Separate AI source review

Final checked source SHA-256: `bdadea07b6035b42fa6b5a018bd0833e1a7115481562e4afa5b94646453ec53f`.

Reviewed frozen source: `formal/ResearchPhysicalTraceJoin/ZeroMarginMatrix.lean`.

Source SHA-256: `bdadea07b6035b42fa6b5a018bd0833e1a7115481562e4afa5b94646453ec53f`.

The packet's README and claim/hypothesis table were also checked against this source. The code identity is limited to valid filtered-table codes; malformed-code defaults are not claimed to preserve feasibility or accuracy.

A separate AI reviewer checked the literal matrix-list definitions, retained-position ranks, default behavior, and exact code correspondence. No mathematical or hypothesis mismatch was found. The executable rank is `idxOf` in the actual retained original-index list at threshold one. For every positive original position, the rank theorem identifies it exactly with the inverse of the checked ordered index equivalence. Nodup is used on positions, not possibly repeated margin values, so repeated positive rows and columns remain distinct.

The restoration function builds the original matrix shape with ordinary list code. A cell reads the reduced matrix only when both original margins are positive; otherwise it inserts zero. In a reading branch, the rank theorem supplies valid reduced indices, and the existing `matrixEntry_code` theorem recovers the corresponding reduced-table entry. The resulting exact code equality agrees pointwise with the checked list-table restoration equivalence. It requires an actual reduced table but no separate probability, accuracy, total-equality, or nonempty-support premise.

For arbitrary matrix lists, the definition remains total: the pinned `matrixEntry` uses an empty-list default for a missing row and zero for a missing entry. These defaults do not validate malformed input or establish its feasibility or output accuracy. The separate length theorems state the original row count and column width for every input matrix. Empty lists and zero-margin rows or columns are covered by the literal construction; absent retained ranks are never needed in a positive reading branch.

The two executable definitions occur outside the noncomputable proof section. This supplies an ordinary Lean list function and a semantic identity on valid table codes. It does not supply a codec realizer, a polynomial-time or charged-cost certificate, a complete preprocessing machine, a defect initializer, physical-state or scale transport, a repair/acceptance map, a sampler branch, or a full table-sampling theorem.

The saved attempt-01 receipt reports successful full compilation and assumption auditing of nine declarations, seven theorems, and three complete headline dependency closures, using only standard axioms. Its source hash matches this reviewed source. This is separate evidence from AI source review, which is not human expert review or an independent kernel check.

The final ordinary compilation and full assumption audit are recorded separately in this packet.
