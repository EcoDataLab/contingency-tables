# Reference completion acceptance with free padding

**Status:** compiled and axiom-audited on 2026-10-08 in
[ReferenceEdgeAcceptance.lean](../formal/Math115/ReferenceEdgeAcceptance.lean).
Lean 4.34.1 accepted the complete module with `autoImplicit=false` and no
warnings. All 13 exported declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`; none use `sorryAx` or a new axiom.

The target is the original sampler's actual completion translation. If its
reference block has `m` rows and `n` columns, put

\[
e=(m-1)(n-1).
\]

For an actual physical edge, the signed reference adjustment changes at most
three cells, each by one, and decreases at most two cells. If every incident
row and column of a decreased cell has margin at least `L`, then a uniformly
chosen source completion is rejected with probability at most

\[
\frac{2e}{L+e}.
\]

Consequently **`L ≥ 3e` suffices for at least one-half directional acceptance**,
provided `L+e>0`. When `L=e=0`, the source-to-target reference translation is
deterministic and always accepted; that case has its own proof rather than an
application of the displayed fraction.

For example, a reference block with three rows and four columns has `e=6`, so
this acceptance condition requires only `L≥18`. Other parts of a sampler may
still impose a larger padding value.

This replaces a hardcoded padding scale at one specific interface. It does not
by itself prove a new full-sampler complexity exponent or implement a sampler.

## The source objects used

The unchanged upstream
[`Accepted`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Transport/TranslatedCompletions.lean)
is exactly

\[
\{X\in\operatorname{Table}(R,P):
      X_{ij}+D_{ij}\ge0\text{ for every cell}\}.
\]

Its `translate` function applies the signed matrix `D` cellwise and converts
the nonnegative integer entries back to natural numbers. `between_rows` and
`between_columns` establish the target margin equations for the source's
literal reference-row/reference-column `between` map. The source
`acceptedEquiv` pairs this operation with its inverse using `-D`; it proves an
exact bijection of accepted subsets, not a comparison based on a surrogate
weight ratio. `betweenAcceptedEquiv` specializes that same bijection.

The source
[`reference_edge_acceptance`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Transport/ReferenceEdgeAcceptance.lean)
fixes padding to `d^12`. Its proof uses an entrywise bound of `10d` and tests
the reference row and column. The new bridge retains the same actual
`physicalAdjacent`, `referenceRows`, `referenceColumns`, `blockCount`, and
`acceptedCount` definitions, and makes `L` a free parameter.

## Count the actual rejected tables

Let `T = Table(R,P)`, `N = |T|`, and let `A` be its accepted subset. Let `S`
contain the cells where `D` is negative. Because `D` has integer entries with
absolute value at most one, its negative entries are exactly `-1`. Therefore

\[
X\notin A
\quad\Longleftrightarrow\quad
\exists(i,j)\in S:\ X_{ij}=0.
\]

`CompletionAdjustment.translation_rejection_iff` supplies this actual
predicate identity. `rejected_card_eq_zero_union` transfers it to a finite
subtype equivalence. The proof never introduces an assumed rejection count.

The ordinary-table all-donor theorem, specialized to threshold one, gives

\[
|\{X\in T:X_{ij}=0\}|(L+e)\le Ne
\]

when both incident margins are at least `L`. For `L=0`, this same count
inequality follows directly from the event's cardinality being at most `N`;
the threshold-one theorem is used only when `L≥1`.

Sum over the actual negative cells and use `|S|≤2`. Writing `C=N-|A|` for the
rejected count gives

\[
C(L+e)\le N|S|e\le2Ne.
\]

This is `rejected_count` and `rejected_count_le_two`. These natural-number
inequalities also hold when the fiber is empty. For a uniform probability
statement, the proof uses equal source totals to obtain a nonempty ordinary
fiber and requires a positive denominator before division.

If `L≥3e`, then `L+e≥4e`. With `L+e>0`, the preceding count inequality implies
`2C≤N`. The exact partition `C+|A|=N` therefore gives

\[
N\le2|A|.
\]

`accepted_half_count` proves this directly with natural counts. The proof
connects to the real-valued source interface only at the final step.

## Connect every physical edge

The proof follows the three branches of the actual source finite edge set:

1. Integer exchanges use `exchange_reference_adjustment_bounds`.
2. Designated repairs recover their `defectLabels`, `repairWord_profile`, and
   small-cell capacity evidence, then use `repair_reference_adjustment_bounds`.
3. Reverse repairs use the corresponding actual inverse-repair theorem,
   `repair_reverse_reference_adjustment_bounds`.

The inverse case matters. The abstract `Bounds D` fields alone do not imply
`Bounds (-D)`: three positive entries and no negative entries would satisfy
those fields in one direction. The reverse-repair proof instead retains the
actual elementary signed-margin classification and negates that
classification. It does not assume that reversing an arbitrary bounded
adjustment preserves the two-negative-cell property.

`physical_reference_adjustment_bounds` assembles those branches. The source
`reference_row_padding` and `reference_column_padding` then supply every
required incident-margin lower bound. `reference_totals` supplies the feasible
target needed in the degenerate branch.

The main export is:

```lean
Math115.ReferenceEdgeAcceptance.reference_edge_acceptance_reduced
```

Its conclusion has exactly the source form

```text
(blockCount R P x : ℝ) / 2 ≤ acceptedCount R P x y
```

for arbitrary `U,L`, with the actual graph-edge premise, the source's capacity
premises, and

```text
3 * (card nonreferenceRows * card nonreferenceColumns) ≤ L.
```

The nonreference types are the large-row and large-column types with the fixed
reference index removed. Their cardinalities are `m-1` and `n-1`, respectively.

## Degenerate shapes and scope

If `e=0`, the reference block has a single row or a single column. For any
source table and feasible target table, the actual `between` adjustment is the
entrywise target-minus-source difference. The translation therefore lands
exactly on the target table and every source table is accepted.
`singleton_between_accepted_card` proves equality of accepted and source
cardinalities, including zero padding and zero total. This discharges the
`L=e=0` branch of `between_accepted_half_count`.

If the large completion rectangle has no rows or no columns, no reference pair
can be chosen. The reference-edge theorem does not silently manufacture one.
That separate deterministic branch is handled by
`CompletionAdjustment.physical_empty_completion_weight`, which identifies its
one completion under the actual positive-state and capacity premises.

The reference fibers in this argument are **ordinary nonnegative integer tables
with fixed margins**. Source capacity hypotheses make the physical completion
block identifiable with those ordinary fibers. They do not extend the
all-donor count to arbitrary cell caps, structural-zero patterns, or weighted
laws. All probabilities here are uniform on the ordinary source completion
fiber.

The remaining integration work is to instantiate this acceptance interface in
a reduced-scale chain, connect the corresponding dense draw and
unpadding branches, and check the final sampler theorem with its actual
parameters. The acceptance bound alone does not complete those steps.
