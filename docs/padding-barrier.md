# A necessary scale for uniform padded rejection

Consider ordinary `2 × n` integer tables with row margins `(U,(n−1)U)` and all `n` column margins equal to `U`, where `n ≥ 2`, `U ≥ 1`, and `L ≥ 1` are integers. Add `L` to every cell's padding, sample uniformly from all tables with the enlarged margins, and accept only when every cell is at least `L` so that the padding can be removed.

For this particular proposal-and-rejection construction,

\[
\boxed{\Pr(\text{unpadding succeeds})
\le\frac{U+1}{U+1+Ln(n-1)}.}
\tag{1}
\]

The inequality is exact when `n=2`. Consequently success probability at least one half requires

\[
\boxed{U\ge Ln(n-1)-1.}
\tag{2}
\]

This is an elementary counting obstruction with an explicit proof below, exact counting code, and independent finite incidence checks. No novelty or priority claim is made, and no Lean verification is claimed here. It is a necessary condition for this uniform padded rejection step, **not** a lower bound on all contingency-table algorithms, an inverse-gap exponent, a different proposal distribution, a different padding rule, or the choice of `L` itself.

## 1. Reduce the padded tables to their first row

Let `y=(y_1,…,y_n)` be the first row. The padded column sum is `C=U+2L`, so the second row is determined as `C−y_j`. The padded first-row sum is `S=U+nL`. Thus the full proposal space is

\[
\mathcal T=\{y\in\mathbb Z_{\ge0}^n:\sum_jy_j=U+nL,\quad y_j\le U+2L\}.
\]

Write `G` for successful rows and `B=T\G` for unsuccessful rows. Success is equivalent to `y_j ≥ L` for every first-row entry. Indeed, if `z_j=y_j−L≥0`, then `sum z_j=U`, so `y_j≤U+L` and the second-row entries are also at least `L`. Conversely successful unpadding requires those first-row lower bounds. Therefore

\[
G=\{L\mathbf1+z:z\in\mathbb Z_{\ge0}^n,\ \sum_jz_j=U\}.
\tag{3}
\]

This also gives a bijection from successful padded tables to the original ordinary tables.

## 2. A switching from every good table to a bad table

Fix `y=L1+z` in `G`. Choose an ordered pair `j≠k` and an integer `h` in `0,…,L−1`. Transfer `v=y_j−h` units from first-row cell `j` to first-row cell `k`:

\[
Y_j=h,\quad Y_k=y_k+y_j-h,\quad Y_i=y_i\quad(i\notin\{j,k\}).
\tag{4}
\]

The transfer is positive, preserves the first-row sum, and never violates the cap:

\[
Y_k=2L+z_j+z_k-h\le U+2L.
\]

All other first-row cells remain at least `L`, and `Y_k≥L+1`, so `j` is the **unique** first-row cell below `L`. This is a valid bad target. Each good row has exactly

\[
Ln(n-1)
\tag{5}
\]

labeled outgoing incidences. Counting incidences avoids any need to assume injectivity of the switching map.

## 3. Bound the incoming incidences

A target with no unique first-row entry below `L` receives no incidence. Otherwise that entry identifies `j` and its value `h`. For any `k≠j`, reverse (4), setting the original source entry to `y_j=L+x`. The other changed entry is `y_k=Y_k−L−x+h`. Both are at least `L` exactly when

\[
0\le x\le Y_k-2L+h.
\]

Every such inverse has all first-row entries at least `L` and the correct sum, so (3) also guarantees the original cell caps. The number of preimages for this receiving column is therefore

\[
\max(Y_k-2L+h+1,0).
\tag{6}
\]

Set `a_k=Y_k−L≥0` for `k≠j` and `b=L−h−1≥0`. The sum constraint gives

\[
\sum_{k\ne j}a_k=U+b+1.
\]

The total indegree is `sum_k (a_k−b)_+`. If every summand is zero, the required bound is immediate. Otherwise let `I={k:a_k>b}`. Since `|I|≥1`,

\[
\sum_k(a_k-b)_+
=\sum_{k\in I}a_k-|I|b
\le\sum_ka_k-b
=U+1.
\tag{7}
\]

Double counting now yields

\[
|G|Ln(n-1)\le |B|(U+1).
\]

Rearrange and use `|T|=|G|+|B|` to obtain (1). If the actual success probability is at least one half, its upper bound must also be at least one half, which gives (2). Condition (2) is not asserted to be sufficient.

## 4. Equality for two columns

For `n=2`, the first row sums to `U+2L` and each entry lies between zero and that same number. Hence

\[
|T|=U+2L+1,\qquad |G|=U+1,
\]

so success is exactly `(U+1)/(U+2L+1)`, equal to (1). Every bad target has a unique low entry and indegree exactly `U+1`. At `U=2L−1`, the success probability is exactly one half.

For larger `n`, some bad rows may be outside the switching image, and the upper bound can be loose. For example, the exact counts at `n=3,L=2,U=11` give success strictly below one half even though (2) holds at equality. The count tool verifies this distinction.

## 5. Consequence when the padding remains cubic in dimension

For this `2 × n` family, the dimension convention in the sampling manuscript is

\[
d=10+(2+1)(n+1)=3n+13.
\]

Holding the [scale audit's](scale-audit.md) padding `L=32d^3` fixed, half-acceptance requires

\[
U\ge32d^3n(n-1)-1
=\frac{32}{9}d^3(d-13)(d-16)-1.
\tag{8}
\]

Thus `U=Omega(d^5)` is necessary **within this fixed uniform padded rejection construction**. A smaller power of `d` cannot guarantee half-acceptance over this family while retaining that padding. This explains why improving only a failure-probability union bound cannot reduce the threshold below the fifth-power order for this construction.

Here `U` denotes the family's actual smallest original margin. If an algorithm classifies a margin as large only when it strictly exceeds a threshold `T`, use the member `U=T+1`; the resulting necessary inequality changes by one, leaving the order unchanged. The argument does not assume that a boundary-equality case belongs to a particular implementation's large rectangle.

The result does not prove any fifth-power lower bound when `L` is also changed. Nor does it prove that a sufficient fifth-power threshold has its best constant, that padding is essential to every sampler, or that an ideal-chain inverse-gap exponent is optimal. The source context is the pinned [sampling manuscript](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf); the obstruction itself is the elementary family and proof in this note.

## 6. Exact counting and resource guards

Stars and bars gives the good count from (3):

\[
|G|=\binom{U+n-1}{n-1}.
\]

For `S=U+nL`, `C=U+2L`, inclusion–exclusion on coordinates exceeding `C` gives

\[
|T|=\sum_{k=0}^{\min(n,\lfloor S/(C+1)\rfloor)}
(-1)^k\binom nk\binom{S-k(C+1)+n-1}{n-1}.
\tag{9}
\]

[`src/contingency115/padding.py`](../src/contingency115/padding.py) evaluates these counts with Python integers and returns the success probability as an exact `Fraction`. It never evaluates the alternating sum in floating point. A preflight plan bounds the number of terms, the sum of symmetric binomial lower arguments, and the bit lengths of binomial results, signed terms, and partial sums before calling `math.comb`. These are declared work/size guards, not bounds on every internal temporary or a claim that Python's binomial algorithm uses exactly that many operations. Resource rejection returns no count.

The separate inexpensive bound and necessary-threshold functions need no table enumeration or binomial coefficients. All APIs reject booleans, floating-point parameters, and values outside the stated integer domain.

## 7. Reproduction and evidence

```sh
PYTHONPATH=src python3 -m unittest discover -s tests -p 'test_padding_barrier.py' -v
PYTHONPATH=src python3 experiments/padding_barrier.py
```

The tests directly enumerate small first-row boxes, independently build every labeled switching, and compare actual target indegrees with (6). They verify cap preservation, unique low cells, both-row unpadding, outgoing totals, the `U+1` indegree bound, exact counts, and `n=2` equality. Guard tests replace `math.comb` with a failing stub to establish that excessive requests are rejected before binomial evaluation.

[`reports/padding-barrier.json`](../reports/padding-barrier.json) includes these finite incidence records and exact count ratios for `n` up to 100. Growth cases use `L=32d^3` with `U=Ln`, `U=Ln^2`, and `U=2Ln^2`, plus the necessary threshold in (2). The report retains integer counts, rational probabilities, reproducible input parameters, and source hashes. Decimal probabilities are display aids only. Finite computations corroborate the universal proof; they do not replace it or establish formal verification.
