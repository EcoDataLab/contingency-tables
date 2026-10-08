# Sequential ordinary-table padding

The new sufficient threshold is `U = 47 d⁵`, with the existing
`L = 32 d³` padding. The argument compares the full ordinary-table count
after each added unit. It retains the same dimension exponent as the earlier
`64 d⁵` threshold.

All table definitions are the unchanged OpenAI definitions at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The new proof lives in
[`PaddingGrowth.lean`](../formal/Math115/PaddingGrowth.lean), with its exact
rational arithmetic in
[`PaddingGrowthAlgebra.lean`](../formal/Math115/PaddingGrowthAlgebra.lean).
Both modules compiled successfully on 8 October 2026. A separate audit of
19 declarations found only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` axioms; no `sorryAx` or added axiom was present.

Let `K` be a finite set of marked cells, with original incident row and
column margins at least `U`, and put `e = (m−1)(n−1)`. Add one unit in a
marked cell. The old fiber is in bijection with the enlarged fiber's tables
whose entry at that cell is positive. This is the existing
`SmallEntryTail.shiftEquiv`, applied in reverse at the raised margins.
Both new incident margins are at least `U+1`. The strong zero-entry bound
and the partition into zero and positive entries therefore give

\[
N_{s+1}(U+1)\le N_s(U+1+e).
\]

Induction through the `L` additions at a cell, then through the marked set,
proves the actual-table inequality

\[
N_{\rm padded}(U+1)^{|K|L}
\le N_{\rm original}(U+1+e)^{|K|L}.
\]

The intermediate fibers have the actual progressively raised margins. The
proof does not substitute a conditional law on a large block. It also
does not divide by a table count: equal margin totals and nonempty fibers
are unnecessary for this natural-number inequality. With positive original
count, the existing upstream padding bijection turns it into the success
probability lower bound

\[
\Pr(\text{unpadding succeeds})\ge
\left(1+\frac e{U+1}\right)^{-|K|L}.
\]

The numerical certificate uses the rational function

\[
E(t)=\frac{t^2+4t+6}{6-2t}
=1+t+\frac{t^2}{2(1-t/3)},\qquad 0\le t<3.
\]

For nonnegative `t,x` with `t+x<3`, the numerator of
`E(t+x)−(1+x)E(t)`, over the two positive denominators, is

\[
2xt^3+x^2(2t^2+6t+18)\ge0.
\]

Finite induction gives `(1+x)^q ≤ E(qx)`. When `qx ≤ 32/47`, exact
rational arithmetic gives

\[
(1+x)^q\le\frac{10147}{5123}<2.
\]

This is the same envelope as the finite-binomial derivation in the
[independent review](third-checkpoint-review.md), proved directly by a
polynomial certificate. No exponential, logarithm, numerical approximation,
or assumed count ratio enters the proof.

Taking `q=|K|L`, `x=e/(U+1)`, `|K|≤d`, `e≤d`, `L=32d³`, and
`U=47d⁵` establishes `47qe≤32(U+1)`. The count inequality then gives
`N_padded≤2N_original`. The scale arithmetic itself holds for every natural
`d`; the dense algorithm's separate `d≥14` requirement does not enter this
count comparison.

The shape-dependent version uses the full cell count `mn` and the donor
count `e` before selecting `K`:

\[
U=\max\{2L,\ 47d^3 mn\,e-1\}.
\]

It satisfies the same count-growth budget because `|K|≤mn`. At `e=0`
the threshold is `2L`. The formal interfaces are `sequentialShapeU`,
`sequential_shape_scale_budget`, and
`sequential_shape_padded_count_le_twice_original`.

The exact Python counterparts in
[`padding_growth.py`](../src/contingency115/padding_growth.py) are
`growth_envelope`, `sequential_padding_bound(q,e,U)`, `sequential_scales(d)`,
and `sequential_shape_scales(m,n)`. They keep the new sequential certificate
separate from the earlier union-bound scale APIs.

[`experiments/padding_growth.py`](../experiments/padding_growth.py) generates
the source-hashed [comparison report](../reports/padding-growth.json).
It includes exact dimension and shape threshold comparisons and replays all
64 marked subsets, at padding one and two, in a small ordinary `2×3` fiber.

The exponent-zero case covers an empty marked set or zero padding. The
donor-zero case gives a growth factor of one; a one-row or one-column
ordinary fiber is included. The denominator `U+1` is positive even at
`U=0`. Empty fibers are included throughout.

The result applies to ordinary uniform uncapped tables. It does not prove
the same bound for weighted tables, cell caps, structural zeros, or the
complete revised sampler. Reparameterizing the sampler and its remaining
transport, edge-acceptance, and runtime obligations are separate work.

## Checked interfaces

The compiled declarations in `Math115.PaddingGrowth` are:

- `one_unit_count_growth`, using the actual cell-shift bijection and zero-entry count.
- `one_cell_count_growth`, repeating the unit bound `L` times.
- `largePadding_insert`, `paddedRows_insert`, and `paddedColumns_insert`, identifying the final margins in the marked-set induction.
- `large_padding_count_growth`, the cross-multiplied count inequality after `|K|L` additions.
- `large_padding_count_eq_of_zero_donors`, the exact equality when `e=0`.
- `sequential_scale_budget` and `sequential_padded_count_le_twice_original`, the universal `47d⁵` construction.
- `sequential_shape_scale_budget` and `sequential_shape_padded_count_le_twice_original`, the construction using the full dimensions.

The audited arithmetic interfaces in `Math115.PaddingGrowthAlgebra` are
`envelope_eq`, `envelope_step`, `one_add_pow_le_envelope`,
`envelope_32_div_47`, `envelope_le_10147_div_5123`,
`one_add_pow_le_10147_div_5123`, `one_add_pow_lt_two`, and
`count_le_twice_of_growth`.

The final direct compilation commands, run sequentially from `formal/`, were:

```sh
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean -j1 -DautoImplicit=false -o .lake/build/lib/lean/Math115/PaddingGrowthAlgebra.olean Math115/PaddingGrowthAlgebra.lean
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean -j1 -DautoImplicit=false -o .lake/build/lib/lean/Math115/PaddingGrowth.olean Math115/PaddingGrowth.lean
```

Both exited with code zero and no warnings. A separate scratch module
imported `Math115.PaddingGrowth` and ran `#print axioms` on all 19 declarations
listed above, using the same `-j1 -DautoImplicit=false` options. That audit
also exited with code zero. The harness toolchain is Lean 4.34.1; the upstream
source and mathlib revisions remain the project's existing pinned revisions.
