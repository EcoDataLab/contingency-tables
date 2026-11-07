# Separate AI review of the inverse-count bound

6 November 2026. This is a separate AI agent's mathematical review of the replacement
`p - 1` proposal, independent of its Lean implementation. It does not validate
the earlier rejected augmented expression, and does not change the sampler.

## Conclusion

The proposed inequality `inverseSupportCount r c U X >= p - 1` is correct for
an ordinary nonnegative integer table with every row and column margin positive.
Here `p` is the number of small cells, `small(i,j)` means `r_i < U or c_j < U`,
and subtraction is truncated natural subtraction. The proof needs no lower bound
of 2 on either dimension and no positive padding hypothesis: it operates on the
ordinary support count. Relating that count to the actual terminal fibre uses
the separate existing theorem with `1 <= L`.

## Exact definition and orientation

`research/physical-trace-general-support/formal/ResearchPhysicalTraceJoin/GeneralInverseSupport.lean`
defines the count over ordered pairs `(s,t)` of small cells, with `s != t`.
The tested donor is `(t.row, s.column)`, **not** `(s.row, t.column)`.
If that donor is small, its table entry must be positive. If it is large,
both relevant ordinary small-part row and column sums must be strictly below
their full margins. All labels below use a positive small donor, so none relies
on the strict-slack branch. No factor of 2 is removed: the count is ordered.

Let `a` be the number of small rows and `b` the number of small columns.
The small-cell union decomposes into small rows and large rows in small columns,
so `p = a*n + (m-a)*b`.

## Injection when a > 0

Choose a fixed small row `i0`. For each small row `i`, positivity of its actual
row margin supplies a column `d(i)` with `X[i,d(i)] > 0`. For each small column
`j`, positivity of its actual column margin supplies a row `k(j)` with
`X[k(j),j] > 0`. Use these three parameter families:

| Family | Parameters | Ordered label `(s,t)` | Size |
|---|---|---|---|
| A | small row `i`, column `l != d(i)` | `((i,d(i)),(i,l))` | `a*(n-1)` |
| B | small row `i != i0` | `((i0,d(i)),(i,d(i)))` | `a-1` |
| C, usual | large row `i`, small column `j`, `i != k(j)` | `((i,j),(k(j),j))` | part of `(m-a)*b` |
| C, special | large row `i=k(j)`, small column `j` | `((i0,j),(k(j),j))` | remainder of `(m-a)*b` |

Both endpoints are small in every case. A and B have donor `(i,d(i))`,
which is positive and small because row `i` is small. Both C cases have donor
`(k(j),j)`, which is positive and small because column `j` is small.
The endpoints differ by the excluded parameter in A and B; in usual C they
differ by `i != k(j)`; in special C they differ because `i0` is small while
`k(j)=i` is large.

Injectivity and disjointness can be checked from these visible row signatures:

* A has equal small endpoint rows, and the two rows plus `t.column` recover its parameters.
* B has distinct small endpoint rows, with `s.row=i0`; `t.row` recovers its parameter.
* Usual C has large `s.row`; `s` recovers `(i,j)`.
* Special C has small `s.row=i0` and large `t.row`; `t` recovers `(i,j)`.

Thus all labels are distinct. The cardinality is
`a*(n-1) + (a-1) + (m-a)*b = p-1`.
There is no hidden truncation step: `a>0` and a positive row donor imply `n>0`,
so `a*(n-1)+(a-1)=a*n-1` is valid in the naturals.

## Remaining cases and scope

If `a=0`, then `p=m*b`. For `b=0`, `p-1=0`. For `b>=1`, the already proved
column-family lower bound `b*(m*b-1)` is at least `m*b-1=p-1`.
This case also makes no strict-slack assumption. A zero dimension paired with
a nonzero dimension cannot admit an ordinary table with all margins positive;
for the `0 by 0` case every relevant count and the truncated bound is zero.
For `p=1`, the proposed bound is correctly zero, not a positive-count claim.

The useful refined allowance is `max(c0,p-1)`, since `p-1` does not dominate
`c0` on every shape. For example, with all cells small and many small rows the
old row bound may be much larger. The current sampler still uses the existing
`c0`: a new count bound by itself does not improve its actual acceptance rate,
retry count, or runtime theorem.

## Independent bounded diagnostic

`independent-check.py` reimplements the exact ordinary support/slack predicate
and the explicit A/B/C map. `independent-check.json` records 2,798 passing cases:
all positive-margin binary tables of dimensions 1 through 3 in both directions,
all 2 by 2 tables with entries 0 through 3, and all integer thresholds from zero
through one above the largest margin. It verifies actual count >= p-1, label
validity, injectivity, family cardinality, and the a=0 reduction.

There are 306 sampled cases where p-1 exceeds c0. A tight nontrivial example is
`X=[[0,1],[2,1]], U=2`: `r=[1,3]`, `c=[2,2]`, `p=2`, and the exact count is
`1=p-1`. Therefore no universal strengthening to `>= p` can hold under these
same hypotheses. Enumeration is diagnostic evidence, not a universal proof.

## Lean receipt status

Attempt 03 compiled successfully in 25.541 seconds and its existing full
environment audit passed in 32.510 seconds. I independently read both the
receipt and the compressed audit output, rather than relying on the worker's
summary. Both headline statements match the receipt exactly and require only
an ordinary table and positive row and column margins. Their dependency
closures contain 5,346 and 5,369 declarations respectively, with only `propext`,
`Classical.choice`, and `Quot.sound`; no nonstandard axioms occur anywhere in
either recorded closure. The module audit reports 32 declarations, 22 theorems,
and 11,953 imported modules/objects.

I recomputed source, object, audit-byte, and imported-manifest SHA-256 hashes;
all match the receipt. The working source is byte-identical to the frozen
attempt-03 source. Source hash is
`e2072c4cea1923f0e73dbd8679a9e5373341b1df1e1c5d2467f41354f9f5b408`;
object hash is
`3d45df7836b8debcf5b670ea3c252a6ffb8435b46d8187a56a6b6cb5fe16cbf0`.
The exact readback is appended in `independent-check.json`.

This was independent mathematical review plus receipt and audit readback;
I did not rerun the compiler. Existing compiler and imported dependency trust,
Linux/Comparator acceptance, sampler integration, and runtime claims remain
separate.

## Draft implementation inspection

The draft `formal/ResearchPhysicalTraceJoin/GeneralAugmentedLower.lean`
was read independently. It combines A and B into `RowSpanningParameters`, which
indexes every small-row cell except the root's chosen donor cell. Its label has
`t=w`; if `w.column` is its row's chosen donor column, `s` uses the root row,
otherwise `s` uses that same row. Thus `t` directly recovers the index and the
excluded root donor is precisely the only potentially coincident case.
`ColumnAttachmentParameters` supplies family C. The source proves the two
families injective and disjoint and counts them. Its headline
`inverseSupportCount_spanning_lower` has exactly `X : Table r c`,
`hr : forall i, 0 < r i`, and `hc : forall j, 0 < c j`; its stronger-allowance
corollary takes the maximum with the old bound. No substantive mathematical
issue was found in this source review. Compilation and assumption audit are separate evidence checked in the receipt
section above.
