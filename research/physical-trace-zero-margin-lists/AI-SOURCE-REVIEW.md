# Separate AI source review

Final checked source SHA-256: `8c6b303ed16f6880cdf264c98b539caa51775a9bc12467cf8194684e23652b22`.

Reviewed frozen source: `formal/ResearchPhysicalTraceJoin/ZeroMarginLists.lean`.

Source SHA-256: `8c6b303ed16f6880cdf264c98b539caa51775a9bc12467cf8194684e23652b22`.

The packet's README and claim/hypothesis table were also checked against this source and preserve its ordinary-table, ordered-position scope.

Final-source reconciliation: attempt 02 adds the elementary `ofFn_listMargin` and `ofFn_filteredMargin` identities and uses them in total preservation. Other repairs make the strict-monotonicity goal and `getD` arguments explicit and unfold the filter in an induction hypothesis. Existing definitions, theorem statements, and hypotheses are unchanged; the added identities introduce no new premise or mathematical scope.

A separate AI reviewer checked stable filtering, retained-position indexing, table restoration, and probability-law targets. No mathematical or hypothesis mismatch was found. `positiveMargins` is the literal order-preserving filter of positive values. `positiveIndices` filters the original index range at threshold one. The map identity relates these two actual lists without assuming distinct margin values. The nodup/get equivalence is applied only to retained original positions, so repeated positive values remain separate rows or columns.

The explicit index equivalence uses the proved filtered-length equality, the nodup retained-index list, and a membership equivalence to positive original positions. Its value, coverage, and strict-monotonicity statements establish the intended ordered correspondence. `filteredMargin_at_retained` identifies each filtered value with the original value at that precise retained position. Sum preservation and the equal-total transport include empty and all-zero lists.

The ordinary-table equivalence composes the checked zero-margin restriction with reindexing along these ordered position equivalences. The generic predicate helper matches the checked restricted-table subtype finite instances before specialization. The private margin-congruence equivalence changes only margin proofs and leaves every matrix entry unchanged; its equality directions correctly identify retained original margins with the filtered margins. The literal restriction and inverse-entry statements therefore restore the same indexed entries at positive rows and columns and insert zeros elsewhere.

Restoration of rational laws uses the inverse of this table bijection. The exact TV identity compares any two filtered-table laws. Under equal original totals, the separately proved filtered-total equality derives nonempty original and filtered table spaces, and uniform transport compares uniform laws on those exact spaces. Neither conditioning nor an error-amplifying normalization is introduced. The table equivalence itself needs no equal-total, nonempty-support, or positive-original-margin premise.

This is an ordered-list semantics and ordinary-table law interface. It does not identify a finite-word or encoded preprocessing program, prove a machine-cost bound, recompute or transport cutoff-dependent physical states or masks, preserve trace kernels, initialize a defect walk, repair a physical completion joint, or complete a sampler. Scale and branch decisions must be considered on the selected lists separately; no universal defect initializer follows from filtering.

The saved attempt-02 receipt reports successful full compilation and assumption auditing of 59 declarations, 48 theorems, and four complete headline dependency closures, using only standard axioms. Its source hash matches this reviewed source. This is separate evidence from AI source review, which is not human expert review or an independent kernel check.

The final ordinary compilation and full assumption audit are recorded separately in this packet.
