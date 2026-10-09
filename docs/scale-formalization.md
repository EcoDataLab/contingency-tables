# Formal scale interfaces and stronger padding thresholds

Later integration: the [current formal ledger](formal-verification.md) records actual chain theorems at both dense-compatible `d²⁵` and ideal-only `d¹⁷` scales. The conditional scope statements below refer to this earlier scale module, not the present project-wide result.

Follow-up to [the scale audit](scale-audit.md), 8 October 2026. All upstream
definitions refer to `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

The numerical certificate now has reusable Lean interfaces. A separate bridge
connects the new small-entry counting theorem to the **actual upstream
ordinary-table padding construction**. This is stronger than checking
polynomial identities: the bridge proves that the number of enlarged tables
is at most twice the number of original tables, under explicit scale and
margin hypotheses. It does not reparameterize the complete small-state chain,
the dense sampler implementation, or the exact-correction machine.

## 1. Generic numerical interfaces

[`ScaleCertificate.lean`](../formal/Math115/ScaleCertificate.lean) defines
`DenseScaleConditions d A B L` and exports consequences matching the dense
proof's interfaces:

- A positive integer width `s/B` for every cell scale `s≥L`.
- The real floor-width bounds `s/(2B)≤floor(s/B)≤s/B`.
- Within-bin exponent change `Ad/B≤1`.
- Interior-volume loss `4d³/B≤1/2`.
- Layer exponent budget `2d²/A+2d³/B≤1/4`.

`proposed_dense_scales` discharges these conditions for every natural `d≥14`
with `A=16d²`, `B=16d³`, and `L=32d³`. The generic integer-width proof is
adapted from upstream `DenseScales.integer_width_bounds`; the source remains
unchanged.

`PaddingScaleConditions` records the earlier, conservative denominator
`U−L+1`. Its constructor `proposed_padding_scales` certifies `U=128d⁵`.
It provides both a real union-bound error at most one half and a natural
cardinality interface: from

\[
 \mathrm{bad}(U-L+1)\le\mathrm{total}\,gLe,
 \quad g,e\le d,\quad \mathrm{bad}+\mathrm{good}=\mathrm{total},
\]

it derives `total≤2 good`. The small-entry counting premise is explicit in
this interface, rather than silently assumed to follow from parameter values.

## 2. The marked cell's own padding permits `U=64d⁵`

For a marked cell `(i,j)∈K`, upstream `largePadding K L` adds `L` in that
cell. Therefore the actual upstream margins satisfy

\[
 \operatorname{paddedRows}_i\ge r_i+L,\qquad
 \operatorname{paddedColumns}_j\ge c_j+L.
\]

If the original two incident margins are at least `U`, the small-entry
lemma may be applied with `a=U+L` and `t=L`. Its simple denominator is
then `a−t+1=U+1`. This replaces the coarser use of `a=U`.

`EnlargedMarginPaddingConditions` explicitly records the changed premise.
`sharper_enlarged_margin_padding_scales` certifies

\[
 U=64d^5=2Ld^2,\qquad \frac{gLe}{U+1}\le\frac12
 \quad(g,e\le d).
\]

The old `PaddingScaleConditions` is deliberately **not** asserted for this
choice: its stronger denominator requirement fails. Both constructions are
retained, so comparisons cannot silently conflate their hypotheses.

[`PaddedMarginBridge.lean`](../formal/Math115/PaddedMarginBridge.lean) proves:

1. `marked_row_margin`, `marked_column_margin`, and `marked_incident_margins`
   for upstream `paddedRows`, `paddedColumns`, and `largePadding`.
2. `enlarged_bad_count`, applying the all-donor theorem from
   `SmallEntrySwitching` separately to each marked cell and taking a finite
   union bound. It proves
   `bad·(U+1)≤total·|K|·L·(m−1)(n−1)` for actual ordinary-table fibers.
3. `large_padding_good_card`, identifying the successful enlarged tables with
   original tables through the upstream padding bijection.
4. `padded_count_le_twice_original`, deriving the successful-count comparison
   when `mn≤d` and the generic enlarged-margin scale conditions hold.
5. `sharper_padded_count_le_twice_original`, specializing to the new `64d⁵`
   threshold and `32d³` padding for every `d≥14`.
6. `enlarged_bad_count_strong` and
   `shape_aware_padded_count_le_twice_original`, connecting the stronger
   conditional-shift tail theorem to actual enlarged-table counts at the
   shape-aware threshold described below.

Empty marked sets, singleton dimensions, and zero margins away from marked
cells are permitted. No equal-total premise is needed for the natural
cardinality inequality: if the fiber is empty, both counts are zero. A
probability statement additionally needs nonemptiness, supplied by equal
nonnegative total margins in the sampler. Cell caps and structural zeros
remain outside the all-donor theorem's domain.

The `64d⁵` choice preserves the conditional ideal-chain exponent `25`.
It halves `U` compared with the conservative constructor; it does not
establish a new exponent for the whole sampling program.

## 3. Exact Python tail and shape-aware refinements

The source-preserving [Python helpers](../src/contingency115/scales.py) expose
the choices separately:

| API | Meaning |
|---|---|
| `proposed_scales(d)` | Original follow-up choice `U=128d⁵` |
| `sharper_scales(d)` | Enlarged-margin choice `U=64d⁵` |
| `padded_margin_scale_probability_bounds(s)` | Uses `U+1`, explicitly requiring the enlarged-margin argument |
| `sharper_scale_certificates()` | Exact nonnegative-coefficient certificates for every `d≥14` |
| `shape_aware_scales(m,n)` | Stronger explicit threshold using the linear tail below and full dimensions |

The additional analytic tail argument conditions on `X_ij≥k` and subtracts
`k` at that cell. This is a bijection to another unrestricted uniform fiber.
Applying the zero-entry estimate successively, with `e=(m−1)(n−1)`, gives

\[
 \Pr(X_{ij}<t)\le
 1-\prod_{k=0}^{t-1}\frac{a-k}{a+e-k}
 \le\frac{te}{a+e}.
\]

The exact product and linear upper bounds are available as
`small_entry_tail_product_bound` and `small_entry_bound_linear`.
`small_entry_mean_lower_bound` returns `a/(e+1)`, obtained by summing the
survival bound. The actual-fiber shift bijection and the strong count, product,
and mean statements are now formalized in
[`SmallEntryTail.lean`](../formal/Math115/SmallEntryTail.lean). Their exact
compiled declarations and axiom audit are recorded separately from the global
sampler guarantee.

The [independent second review](second-checkpoint-review.md) gives the product
and mean derivations, including the composition examples that attain them.

Applying the linear bound with `a=U+L`, `t=L`, and `g≤mn` gives the explicit
shape-dependent choice

\[
 U=\max\{2L,\ 2Lmn\,e-L-e\}.
\]

Its bad-unpadding bound is `mn·L·e/(U+L+e)≤1/2`. The threshold depends
only on the full dimensions; it does not depend circularly on the large-cell
set that the threshold will subsequently select. If `e=0`, the helper uses
`U=2L` and the unpadding bad fraction is zero; the actual one-dimensional
sampling problem is deterministic. Empty dimensions bypass the algorithm and
are excluded from this helper's domain.

`ScaleCertificate.shapeAwareU` and `shape_aware_linear_tail_budget` formalize
this threshold arithmetic. The corresponding real error inequality is
`shape_aware_linear_unpadding_error_le_half`. The arithmetic interface remains
separate from its combinatorial premise. `PaddedMarginBridge` now supplies that
premise using `SmallEntryTail.all_donor_small_entry_count_strong`, then proves
the actual successful-count comparison in
`shape_aware_padded_count_le_twice_original`. This comparison needs each marked
original incident margin to be at least the explicit threshold; it has no assumed
count bound, no equal-total premise, and no nonempty-fiber premise.

All arithmetic is exact. Twelve scale tests pass, including the complete
small-fiber catalog from the original audit, checking all four tail bounds
and the mean bound. Exact witnesses use `2×(e+1)` tables with row margins
`(a,ea)` and every column margin `a`: the first row is uniform on weak
compositions of `a`. The survival product and mean bounds are equalities in
these examples; the linear tail is also exact at every threshold when `e=1`.

## 4. Remaining formal integration

These modules do not prove a new dense conductance theorem from generic
parameters, nor do they discharge the new global physical transport energy
bound, the complete chain's mixing schedule, finite-law tabulation, or machine
runtime. The dense numerical interfaces are ready to be substituted into the
upstream volume and normalizer arguments; that substitution still needs a
checked theorem connecting their conclusions to the concrete sampler.

The `O(d²⁵)` statement consequently remains an analytic ideal-chain result
conditional on those stated construction and transport inputs. Axiom audits,
tool versions, and exact compiled declarations belong to the shared
[formal verification record](formal-verification.md); a secure Comparator
pass and an updated global machine theorem are separate verification levels.
