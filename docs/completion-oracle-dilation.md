# A completion oracle at the smaller padding scale

The completion problem can be enlarged numerically, sampled by the unchanged
upstream dense sampler, and rounded back without favoring particular tables.
This gives a route around the old dense interface's requirement
`L≥32d³`: the outer chain keeps `L=3d`, while the dense sampler receives
different, larger margins.

The construction and constant acceptance bound below are independently
reviewed mathematics. They are not yet a complete Lean proof or a compiled
finite-bit replacement for the original sampler. The exact integer codec,
finite checks, and formal components have separate verification records.

The geometric starting point is the adjacent-rectangle lattice basis and
equal-volume rounding cells in Dyer, Kannan, and Mount,
[*Sampling Contingency Tables* (1997), Section 4](https://www.math.cmu.edu/~af1p/Teaching/MCC17/Papers/contingency.pdf).
Their cell error bound, volume comparison, and rejection idea are classical.
Here we apply that geometry to a finite dilated lattice and the pinned
OpenAI dense sampler, using the stronger margins of the actual completion
block. The continuous sampler from that paper is not required by this
construction.

## The actual completion margins

Let the large block have `a` rows and `b` columns. Its residual margins
`R,P` are ordinary unrestricted table margins, with equal total `H`.
Every large row receives padding in all `b` columns, and every large column
in all `a` rows. Thus

\[
 R_i\ge bL,\qquad P_j\ge aL,\qquad H\le M+abL,
\]

where `M` is the original total margin. This retains more information than
the weaker exported bound that each margin is at least `L`.
The actual capacity excludes no ordinary completion table.

At `L=3d`, the free dimension `e=(a−1)(b−1)` satisfies `e≤d−1` and
`ab≤d`, so `H≤M+3d²`. Empty blocks or blocks with one row or column have
a unique completion; they can be handled directly. Below assume `a,b≥2`.
Then the ambient dimension allowance satisfies `d≥19`.

## Enlarge, sample, round, and test

Choose an integer dilation `k≥1`. The fine table `Z` has margins

\[
 R_i^{\rm fine}=k(R_i+2b),\qquad
 P_j^{\rm fine}=k(P_j+2a).
\]

Its total is **`k(H+2ab)`**. For a matrix `W`, let `C(W)_(i,j)` be the
sum of entries in its first `i` rows and first `j` columns, including zero
prefixes. For prefix values `V`, define the mixed difference

\[
 D(V)_{i,j}=V_{i+1,j+1}-V_{i,j+1}-V_{i+1,j}+V_{i,j}.
\]

The integer decoder is

\[
 V_{i,j}=\left\lfloor C(Z)_{i,j}/k\right\rfloor,
 \qquad X=D(V)-2\mathbf1.
\]

Bottom and right prefix sums divide exactly by `k`, so `X` has margins
`R,P`. Accept if every entry of `X` is nonnegative. Only integer prefix
addition, division, subtraction, and feasibility tests are required.

The reason the output is uniform is an exact counting identity. For any
original table `X`, choose one digit in `{0,…,k−1}` at each of the `e`
interior prefix positions, and extend this array `u` by zero on its entire
boundary. Then

\[
 Z=k(X+2\mathbf1)+D(u)
\]

has the fine margins and decodes to `X`. Each mixed difference lies between
`−2(k−1)` and `2(k−1)`, so the fine entries are at least two. Conversely,
the remainders `C(Z) mod k` recover the digits uniquely. Each original
table therefore has **exactly `k^e` accepted fine-table preimages**.
An exact uniform fine draw gives an exact uniform output conditional on
acceptance. This statement concerns the ideal fine law; an approximate
draw retains an explicitly charged error below.

## Constant acceptance at `L=3d`

Write `N` for the original table count and `N_f` for the fine count.
Use volume in the `e` free-entry coordinates obtained by deleting the last
row and column. Prefix coordinates have a triangular integer change of
variables with determinant one. The half-open rounding cells consequently
have volumes one and `k^(−e)` on the two lattices.

Each coarse cell changes an entry by strictly less than two; each fine
cell changes it by strictly less than `2/k`. If `V(R,P)` denotes the
coordinate volume of the ordinary real transportation polytope, these
cell inclusions imply

\[
 V(R-2b,P-2a)\le N,\qquad
 N_f/k^e\le V(R+(2+2/k)b,P+(2+2/k)a).
\]

The first inclusion rounds points whose entries are at least two to
feasible integer representatives. For the second, attach a fine cell to
each `Z/k` and translate the union by `(2/k)\mathbf1`.
The different affine origins do not change coordinate volume.

Increasing both margin vectors coordinatewise cannot decrease this volume:
add a nonnegative real table with the difference margins to embed the
smaller polytope in the larger. Such a table exists because the difference
margins are nonnegative and have equal totals. Scalar dilation multiplies
volume by its `e`th power.

Set

\[
 \lambda=\frac{L+2+2/k}{L-2}.
\]

The strong margin bounds give
`λ(R_i−2b)≥R_i+(2+2/k)b`, and the analogous column inequality.
The smaller polytope has positive volume: a completion of the remaining
nonnegative real margins, plus `(L−2)\mathbf1`, is strictly positive.
It follows that

\[
 s=\frac{k^eN}{N_f}\ge\lambda^{-e},\qquad
 \log(\lambda^e)\le\frac{e(4+2/k)}{L-2}.
\]

For arbitrary `k≥1`, `L=3d` and `e≤d−1` give `s≥exp(−2)>1/8`.
For the actual choice **`k=d¹²`**, we have `k≥2d`, and

\[
 \frac{e(4+2/k)}{3d-2}
 \le\frac{(d-1)(4+1/d)}{3d-2}\le\frac43.
\]

Hence **`s≥exp(−4/3)>1/4`**. This is a counting/volume bound, not a
measured acceptance rate or a new mixing theorem.

## Reuse the existing finite-bit dense sampler

With `k=d¹²`, every fine margin is at least `d¹²`. The unchanged
`canonicalDenseDraw_variation` interface in
[`DenseCanonicalSemantics.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Dense/DenseCanonicalSemantics.lean) also
requires `d≥14`, equal totals, and row, column, and free dimensions at
most `d`; all hold here. Its analytic inputs are the same source-proved
Prékopa–Leindler and Cheeger statements used by the original theorem.
The routine computes its own initialization and handles margin reordering.

For a desired completion accuracy `2^(−h)`, with integer `h≥0`, use a fixed feasible fallback
and at most

\[
 J=4(h+2),\qquad h_{\rm fine}=h+2+\lceil\log_2J\rceil
\]

independent fine draws of accuracy `2^(−h_fine)`. Take the first accepted
decoded table, or return the fallback. Comparing the entire retry procedure
to ideal independent fine draws gives

\[
 \operatorname{TV}(\text{completion output},\operatorname{Uniform})
 \le (3/4)^J+J2^{-h_{\rm fine}}
 \le 2^{-(h+1)}\le2^{-h}.
\]

This accounts for the fine sampler's own fallback bias and the new
rejection fallback. Each call uses fresh bits; no approximate draw is
silently treated as exact after conditioning on acceptance.

Only `O(log d)` bits are added to each input margin. A uniform bound on
the fine total over physical states is
`d¹²(M+3d²+2d)`. The source's
`normalizedDrawBits_polynomial` in
[`DenseNormalizeSemantics.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Dense/DenseNormalizeSemantics.lean)
bounds its dense word count by `25(d+ℓ+h_fine+1)^62`, where
`ℓ=ceil(log₂(C+2))` for a bound `C` on the fine row margins.
This is a random-bit allowance, **not** the compiled machine-time degree.
`polynomial_canonicalDenseDraw` in
[`DenseCanonicalProgram.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Dense/DenseCanonicalProgram.lean) supplies a
polynomial realizer cost; the new codec and bounded retries still need
their own formal realizer and composition proof.

## Exact codec and reproduction

The Python [codec and planner](../src/contingency115/lattice_completion.py)
implement the integer maps above for ordinary unrestricted margins.
`plan_lattice_completion` accepts any positive integer `k`;
`plan_dense_completion` checks the strong residual margins and chooses
`k=d¹²`. Its acceptance allowance is conditional on the reviewed geometry.
Neither function draws a dense table.

For example, this represents an original table by one chosen digit array:

```python
from contingency115.tables import TableProblem
from contingency115.lattice_completion import (
    plan_lattice_completion, encode_completion, decode_completion,
)

plan = plan_lattice_completion(TableProblem((1, 1), (1, 1)), k=3)
original = ((1, 0), (0, 1))
fine = encode_completion(plan, original, ((2,),))
assert decode_completion(plan, fine).table == original
```

Run the [focused tests](../tests/test_lattice_completion.py) and regenerate
the [finite report](../reports/lattice-completion.json):

```sh
PYTHONPATH=src python3 -m unittest discover -s tests -p test_lattice_completion.py -v
PYTHONPATH=src python3 experiments/lattice_completion.py --output /tmp/lattice-completion.json
```

The report exhausts 13 small fibers, with 293 fine tables and 44 constructed
table/digit pairs. It preserves one deliberate budget failure and separately
checks ten actual-scale roundtrips, reaching 8,639-bit fine entries. These
large examples do not enumerate or sample their fibers. The small examples
test the codec; their margins need not satisfy the constant-acceptance
hypotheses. The [independent review](../reports/completion-oracle-dilation-review.json)
records the mathematical argument, frozen source hashes, test replay, and
an additional exhaustive 3×3 check.

The [approximate-oracle interface](physical-approximate-oracle.md) connects
normalized completion laws with the actual proposal and translation test.
It charges completion error before the outer success test and permits
separate transition and terminal accuracies. Its finite-law proof supplies
the interface this new completion construction must eventually instantiate.

The [Lean codec core](lattice-completion-codec.md) checks the signed integer
inverses, boundary-dependent margin formulas, positivity, and cardinality
of the constructed finite-digit image. It has not yet identified that image
with the whole accepted finite-table fibre. The separate
[physical-margin module](../formal/Math115/DilatedCompletionMargins.lean)
derives the strong residual bounds above and the enlarged inputs' equal
totals and dense minimum, directly from actual physical states.
The [source review](../formal/results/lattice-completion-review.json) and
the [codec](../formal/results/lattice-completion/verification.json) and
[margin](../formal/results/dilated-completion-margins/verification.json)
receipts keep those formal claims separate from the volume argument.

## What this resolves and what remains

The construction supplies a mathematically justified completion route
at the smaller outer scales, using an existing finite-bit dense sampler
after dilation. It preserves polynomial dependence on binary margin length
and requested precision. It does not turn `d¹⁷` into a complete runtime
exponent: outer retries, walk length, dense-call cost, and bit arithmetic
must all be charged.

The remaining formal work includes the full finite-table equal-preimage
bijection, the lattice-cell volume/count bounds, and identification of the
integer codec and retry routine with
their finite-bit realizers. The approximate-oracle error bridge must then
be instantiated with this completion law and linked to the full outer
program. These obligations remain visible even where individual algebraic
lemmas or finite examples have already been checked.

Two narrow next steps are to restrict the integer codec to actual finite
table types and to prove the volume of the finite union of its half-open
prefix cells. The latter can use prefix-coordinate volume throughout:
the cells are ordinary boxes, and translation and scalar volume rules
then give the count comparison without a separate determinant lemma.
