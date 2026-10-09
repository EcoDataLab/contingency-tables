# The quadratic stationary rejection cost is necessary for this rule

Reviewed mathematical derivation, 9 October 2026. This combines the existing
[exact repair count](defect-transport-research.md) with the proved
[small-entry bound](small-entry-formalization.md). The resulting asymptotic
obstruction is not a new Lean theorem. Its scope is the unchanged physical
state space and stationary success rule.

The [stationary-output proof](physical-stationary-success.md) gives success
at least `1/[2(1+p²)]` at the smaller ideal scales. The dependence on `p²`
cannot be replaced by a smaller worst-case order for this success rule:
there are nontrivial ordinary table fibers at these same scales for which
the stationary success probability `s` satisfies

$$
p^2s\longrightarrow1.
$$

## Exact count and two-sided bound

Take an `n×n` table with every row and column margin equal to an integer
`M`, where `n≥2` and `1≤M<U`. All `p=n²` cells are small. The large block is
empty, each physical state has one completion and weight one, and padding
does nothing. Let `N` count ordinary tables and `D` count physical defects.
Then `P=N`, `Z=N+D`, and the stationary success probability is `N/(N+D)`.

For a fixed balanced table `A`, the existing inverse repair formula is

$$
x=A+e_b-e_v,\qquad q=A+e_a-e_v,
\qquad v=(\operatorname{row}(b),\operatorname{col}(a)),\quad a\ne b.
$$

It is feasible exactly when `A_v>0`. For a fixed receiver `v`, there are
`n²−1=p−1` ordered pairs `(a,b)`: choose the row of `a` and the column of
`b`, then exclude `a=b=v`. The labels and repaired table recover the
original defect, including cases where `v=a` or `v=b`. Thus

$$
\frac DN=(p-1)\,\mathbb E_{A\text{ uniform}}|\operatorname{supp}(A)|.
\tag{1}
$$

Write `e=(n−1)²`. The compiled theorem
`SmallEntrySwitching.all_donor_small_entry_probability_refined`, with
threshold one and incident-margin lower bound `M`, gives

$$
\Pr(A_{ij}=0)\le\frac e{M+e},\qquad
\frac{pM}{M+e}\le\mathbb E|\operatorname{supp}(A)|\le p.
$$

Combining these inequalities with (1) proves

$$
\boxed{\quad
\frac1{1+p(p-1)}\le s\le
\frac{M+e}{M+e+p(p-1)M}.
\quad}
\tag{2}
$$

This uses the exact support identity, not an assumption that table entries
are independent. In the `2×2` equal-margin family, the upper bound is
attained: `N=M+1`, `D=12M`, and `s=(M+1)/(13M+1)`.

## A family at the actual smaller ideal scales

Choose

$$
d=10+(n+1)^2,\qquad U=5d^3,\qquad L=3d,\qquad M=d^3.
$$

Here `M<U`, so all cells remain small and `L` has no effect. Since
`e≤d`, inequality (2) implies

$$
\frac{p^2}{1+p(p-1)}\le p^2s\le
\frac{p^2}{1+p(p-1)d^2/(d^2+1)}.
$$

Both endpoints tend to one as `n` increases. These are not singleton
output fibers: varying the top-left `2×2` block while putting `M` on the
remaining diagonal already gives `M+1` different ordinary tables.

For the bounded independent stationary retry rule with a fixed fallback,
the exact uniform/fallback mixture has total variation error
`(1−s)^R(1−1/N)` after `R` trials. Consequently any fixed target error
`0<ε<1/2` requires at least order `p²` trials in this family. The exact stationary
draws themselves are still oracle operations. This gives no mixing-time,
physical-clock, bit-runtime, or all-samplers lower bound; changing the state
space, output rule, or fallback law is a different method.

## Exact finite evidence

The [report](../reports/stationary-success.json) freshly reruns the existing
independent graph enumeration on eight bounded synthetic cases, checks the
rational inequalities in (2), and records its source hashes. For example:

| `n` | `M` | Original tables `N` | Defects `D` | Stationary success |
| --- | --- | --- | --- | --- |
| 2 | 1 | 2 | 12 | `1/7` |
| 2 | 2 | 3 | 24 | `1/9` |
| 3 | 1 | 6 | 144 | `1/25` |
| 4 | 1 | 24 | 1440 | `1/61` |

Unpadding acceptance from the ordinary padded table fiber is one in all
these examples. The smaller physical success probability comes entirely
from the additional defect states. The large asymptotic family above is
proved by the count inequalities; it is not enumerated in this report.

```sh
PYTHONPATH=src python3 experiments/stationary_success.py --output reports/stationary-success.json
```

The [independent review](../reports/stationary-success-obstruction-review.json)
records the checked assumptions, count identity, squeeze, and scope.
