# Integer codec for lattice completion dilation

Direct Lean compilation and all 44 named declaration axiom audits passed
on 9 October 2026 with pinned Lean 4.34.1. Eight declarations are axiom-free;
the remainder use only `propext`, `Classical.choice`, and `Quot.sound`, or
subsets. This is an author module check using existing dependency objects,
not aggregate integration, a dependency-closure rebuild, or Comparator
replay. The [author receipt](../formal/results/lattice-completion/verification.json)
retains commands, raw logs, exact exports, source hashes, and timings. The
[independent review](../formal/results/lattice-completion-review.json)
records its separate mathematical and interface assessment.

[`LatticeCompletion.lean`](../formal/Math115/LatticeCompletion.lean)
isolates the integer arithmetic behind adjacent-cycle rounding.
For a prefix-offset array `u`, define

\[
 D u_{ij}=u_{i+1,j+1}-u_{i,j+1}-u_{i+1,j}+u_{i,j}.
\]

Rectangular prefix sums invert `D` when the top and left prefix boundaries
are zero, and `D(prefix X)=X` for any signed integer array. Row and column
sums telescope to the boundary values. Zero values on all four prefix
boundaries therefore preserve the margins.

For a positive integer `k`, encoding and decoding are

\[
 Z=k(X+2\mathbf1)+D u,\qquad
 X=D\bigl(\operatorname{prefix}(Z)\mathbin{/}k\bigr)-2\mathbf1,
 \qquad u=\operatorname{prefix}(Z)\bmod k.
\]

Division is Euclidean integer division: it agrees with floor division for
positive `k`, including negative prefix numerators. The module checks both
codec inverse statements and exact recovery of the residues. Its universal
codec equivalence uses arrays indexed by natural numbers and bounded digits
at all those prefix coordinates; that equivalence alone makes no finite-count
claim.

If every offset digit lies between zero and `k−1`, then

\[
 -2(k-1)\le D u_{ij}\le2(k-1).
\]

Every nonnegative original entry consequently encodes to an integer at least
two. The encoded row sums are `k(rowSum X+2b)` and column sums are
`k(columnSum X+2a)`. Conversely, divisible full row and column sums imply
zero residue boundaries; under those boundaries the decoded margins are
the fine margins divided by `k`, less the stated per-cell shift. These
array hypotheses explicitly include the chosen outside extension.

The finite digit family is
`Fin(a−1) → Fin(b−1) → Fin k`. Its extension is zero whenever a prefix
coordinate is zero, is on a last boundary, or is outside the interior.
Its cardinality is exactly `k^((a−1)(b−1))`, and the module proves that,
for a fixed original integer array, distinct finite digits produce distinct
encoded arrays. `encodedFamily_card` counts **the constructed image only**.
It does not identify that image with the entire accepted fine-table fibre.
Natural subtraction handles empty and singleton dimensions in this finite
digit type. Finite-table assertions must restrict the arrays to the stated
rectangle; arbitrary outside entries are not implicitly table cells.

To obtain the full equal-preimage theorem for actual finite table types,
add an explicit finite-table extension and restriction adapter, prove its
prefix congruence inside the rectangle, establish that each fine table's
recovered residue has exactly the finite-offset support, and show the
accepted decoder has the original nonnegative margins. The existing codec
identities would then supply the inverse maps. That adapter and accepted
fibre surjectivity are separate from the image-count statement here.

No volume comparison, constant rejection-success bound, invocation of the
original dense sampler, finite-bit realizer, or machine-cost theorem is
claimed by this module. Those are separate interfaces in the completion
oracle research.
