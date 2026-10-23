# Separate AI source review

Final checked source SHA-256: `047a8e15ba90420b042257e88614a77516b7eed81a539a0df2e168e8f627743b`.

Reviewed frozen source: `revisions/attempt-02/formal/ResearchPhysicalTraceJoin/Terminal.lean`.

Source SHA-256: `047a8e15ba90420b042257e88614a77516b7eed81a539a0df2e168e8f627743b`.

Final-source reconciliation: attempt 02 only annotates the right-hand lambda argument in `hterminal` as `DefectVertices r c U L`. This proof-elaboration repair changes no definition, theorem statement, hypothesis, or mathematical scope.

A separate AI reviewer checked the definitions, target normalization, word-law construction, and error composition. No mathematical or hypothesis mismatch was found. `DefectJoint` retains the reached defect and a member of that same defect's physical completion fibre. The base stationary law weights each defect by its fibre cardinality, normalized over defects only. Following it with a uniform same-defect completion therefore gives the uniform law on this dependent pair type, by the existing `dependentJointLaw_uniform` theorem.

The literal program splits one uniform word into a walk bank and an independent terminal bank. The reached defect depends only on the walk bank. Its terminal completion receives only a prefix of the second bank, using the proved uniform completion-width bound. The existing padding and dependent-product identities identify this program with the dependent joint of the actual bounded-walk law and the actual frozen legacy completion laws. No ideal completion oracle is substituted into the exact program law, and padding adds no approximation. The construction also covers zero walk steps.

The terminal comparison reuses `variation_dependentJoint_uniform`: the error is at most the base-law error plus `dyadic hTerm`, without dividing by a stationary mass or conditioning on a success event. Combining it with the checked scheduled walk interface gives `T * dyadic t + B * exp(-T / K) + dyadic hTerm`. The reserved input bank is exactly `T * uniformStepWidth + uniformCompletionBits(hTerm)`. This is an input reservation, not a bound on inspected bits or machine time.

The exact program-law and local completion statements require the two computed large-line lists to be nonempty and a supplied defect, with arbitrary natural parameters. The final scheduled bound additionally requires equal original totals, `U >= 2`, `L >= 7`, at least two small cells, and nonempty defect support. Original margins need not all be positive. The starting defect is supplied before the fresh input word.

The target is uniform on defect-labelled completion pairs, not original tables. The result is a finite-parameter bound for chosen `(T, t, hTerm)`; it does not assert exact stationary convergence of the actual fixed-precision walk. It supplies no initialization, table-output projection or correction, whole-sampler restart, complete table sampler, or runtime exponent.

Compilation and assumption auditing are separate evidence and were pending for this frozen source when this reconciliation was written. This is AI source review, not human expert review or an independent kernel check.

The final ordinary compilation and full assumption audit are recorded separately in this packet.
