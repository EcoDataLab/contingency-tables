# Verified completion by dilation and rounding

The completion oracle's finite-table counting and geometric acceptance proofs
now compile in Lean. At the smaller outer padding `L=3d`, a uniform draw from
the enlarged table problem has acceptance at least one quarter. The actual
integer decoder, with bounded independent retries and an accurate approximate
fine-table law, has the requested output accuracy. The count and acceptance
bounds are proved within this result; they are no longer oracle hypotheses.

This closes a central gap behind using the `80,000d¹⁷` auxiliary-chain bound.
The remaining connection is to the canonical dense sampler, every physical
state's completion problem, and finite-bit programs with charged costs.

An additional [executable Boolean codec/retry component](completion-boolean-program.md)
now identifies the actual signed decoder and an ordered bank of independent
trial words with the retry law. Its 25 isolated audits supplement checkpoint 8.
The subsequent [binary-list decoder](completion-list-decoder.md), with 52
isolated audits, proves exact table semantics and polynomial charged work
for decoding. Canonical dense integration and composed sampler costs remain
open.

The [explicit schedule arithmetic](completion-schedules.md) also now compiles:
56 isolated audits cover the walk/retry counts, separate completion
precisions, four scalar error budgets, and a polynomial bound on the full
reserved bit bank. Its physical-program identification and composed machine
cost remain separate obligations.

## Why equal representation matters

For a small example, take a 2×2 table whose row and column margins are both
`(1,1)`. There are two original tables. At dilation `k=3`, the enlarged
margins are `(15,15)` on both sides, giving sixteen fine tables. The decoder
accepts exactly six: three decode to each original table. The other ten are
rejected. Equal numbers of accepted representations ensure that acceptance
does not favor one original table.

The Lean proof establishes the corresponding identity for arbitrary finite
margins and every positive `k`: each original table has exactly
`k^e` accepted preimages, where `e=(a−1)(b−1)` uses natural, truncated
subtraction: `e=0` if either dimension is at most one. It covers the entire
accepted fine-table fiber, including empty and singleton dimensions. The tiny example
illustrates that identity; its margins do not satisfy the stronger hypotheses
used for the general quarter-acceptance guarantee.

## The theorem's inputs and conclusion

For natural margins `R : Fin a → ℕ` and `P : Fin b → ℕ`, the actual
[`chosen_dilation_accuracy`](../formal/Math115/LatticeCompletionAccuracy.lean)
theorem takes:

- An integer `d≥2`, equal margin totals, and `e≤d−1`.
- Strong margins `R_i≥3bd` and `P_j≥3ad`.
- A feasible original table to use as the fallback.
- A normalized rational fine-table law within `2^(-h_fine)` of uniform.

The enlarged margins are exactly `d¹²(R_i+2b)` and `d¹²(P_j+2a)`. For
requested precision `h≥0`, set

\[
J=4(h+2),\qquad h_{\rm fine}=h+2+\lceil\log_2J\rceil.
\]

Draw independently from the fine law, return the first accepted decoded
table, and use the fallback after `J` failures. The resulting actual-table
law is within `2^(-h)` of uniform. The general theorem proves the stronger
bound `2^(-(h+1))`; its geometry permits any `k≥2d` and `d≥1`.

The law of the *whole* fine draw must meet the precision bound. Its own
failure fallback cannot be discarded or silently conditioned away. Fresh
independence is part of the product-law retry construction. The new Boolean
component identifies the ordered word segments for a supplied fine draw;
the canonical dense draw's specialization remains separate.

## How the counting proof closes

All volume statements use interior rectangular-prefix coordinates directly.
Their half-open cells are ordinary boxes. There is no unproved change of
coordinates or determinant premise in the count theorem.

Let `N` count original tables, `N_f` count fine tables, and let `V_-` and
`V_+` be the prefix-coordinate volumes with respective margins
`(R−2b,P−2a)` and `(R+(2+2/k)b,P+(2+2/k)a)`. With
`λ=(L+2+2/k)/(L−2)`, the compiled proof gives

\[
\frac{N_f}{k^e}\le V_+\le\lambda^e V_-\le\lambda^e N.
\]

The first and last inequalities come from actual finite-table cell covers.
The middle inequality constructs a nonnegative table with the difference
margins and applies translation and scalar volume rules. The proof works
in nonnegative extended-real measure until the finite final comparison.
It never divides by the volume of a region. A supplied fallback encodes to
a fine table, proving `N_f>0` before division by the count.

At `L=3d`, `e≤d−1`, and `k≥2d`, Lean proves `λ^e<4` using an exact
logarithm inequality. Combining this with the equal-preimage identity yields
the exported acceptance bound `k^e N/N_f≥1/4`. The retry error is then

\[
\operatorname{TV}\le(3/4)^J+J2^{-h_{\rm fine}}
\le2^{-(h+1)}.
\]

## Proof modules and evidence

| Module | New audited exports | Role |
| --- | ---: | --- |
| [LatticeCompletionFinite](../formal/Math115/LatticeCompletionFinite.lean) | 52 | Full finite-table equivalence and complete accepted preimage counts |
| [LatticeCellVolume](../formal/Math115/LatticeCellVolume.lean) | 19 | Disjoint prefix cells and exact cell-family volume |
| [CompletionRetryBudget](../formal/Math115/CompletionRetryBudget.lean) | 23 | Finite-law retries and the concrete dyadic schedule |
| [LatticeCompletionLaw](../formal/Math115/LatticeCompletionLaw.lean) | 11 | Actual decoder law, exact success masses, and retry law |
| [PrefixTransportation](../formal/Math115/PrefixTransportation.lean) | 48 | Real prefix geometry, actual margins, translation, and scaling |
| [PrefixFloorCover](../formal/Math115/PrefixFloorCover.lean) | 22 | Integer floor rounding and the lower cell cover |
| [CompletionCountBound](../formal/Math115/CompletionCountBound.lean) | 16 | Upper cell cover and complete fine-table count comparison |
| [CompletionAcceptance](../formal/Math115/CompletionAcceptance.lean) | 13 | Symbolic constant and rational quarter bound |
| [LatticeCompletionAccuracy](../formal/Math115/LatticeCompletionAccuracy.lean) | 8 | Actual quarter acceptance and completion accuracy at `k=d¹²` |

These 212 new declarations have separate compilation and axiom-audit
receipts. The [checkpoint receipt](../formal/results/completion-geometry-checkpoint.json)
and [independent agent review](../formal/results/completion-geometry-review.json)
record frozen source hashes and distinguish source review from compilation.
The [formal ledger](formal-verification.md) records aggregate verification,
independent Linux coverage, trusted dependencies, and Comparator status.
The geometry's classical source and the construction's derivation remain
attributed in the [dilation guide](completion-oracle-dilation.md).

## Remaining implementation bridges

1. Reindex the canonical dense sampler's `Option (Fin n)` table types to
   the codec's `Fin a` types, and convert its real-valued total-variation
   bound to the rational dyadic bound here. Its output law is already a
   rational law; a new probability construction is unnecessary.
2. Supply this completion law for every actual physical state and terminal
   fiber. Existing residual-margin lemmas provide the strong margins;
   dimension bounds, fallbacks, and unique-completion branches still need
   to be assembled into the `OracleFamily` interface.
3. Compose the verified binary-list decoder with Boolean retries and dense
   draws, then charge random bits, arithmetic, dense-call, and outer-walk
   costs.

The `d¹⁷` result continues to describe an auxiliary-chain inverse gap.
Neither a complete runtime exponent nor practical competitiveness follows
from this checkpoint.
