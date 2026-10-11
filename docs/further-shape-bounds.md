# Further bounds from the actual table geometry

The general rational defect trace now has a [compiled `431d⁸` theorem](physical-defect-trace.md).
The [aggregate incidence proof](aggregate-incidence.md) improves the reviewed
bounded-aspect allowance to `15488 A^(3/2)d^(13/2)` when `(m+n−2)²≤Ad`.
More structure gives the further bounds below. These refinements have separate
AI mathematical review; their physical Lean assembly and sampler/runtime
integration remain open.

Here `d=10+(m+1)(n+1)`, `s=m+n−2`, `p` is the number of small cells, and
the cutoff is chosen before classification. The displayed dimension powers
use `U=11ds,L=7`. All statements concern the accelerated defect trace with a
nonempty defect space, rather than the original normalized chain's d⁹ theorem.

| Actual geometry | Rational inverse-gap allowance | Additional conditions |
|---|---|---|
| General reference branch | `3872d⁵s²(3s+2)`; combined with the unit branch, `15488 A^(3/2)d^(13/2)` | `m,n≥2`, `s²≤Ad`, actual ordinary residual-table constraints and ideal completions |
| Exactly one small column and no small rows, or the transposed graph | `96p³U²`; sharper repair-load formula below | Small-line margin `1≤H<U`, ordinary equal-total margins, ideal completions |
| Entire row side or column side below `U` | `4[2(m+n)−3]p³U²`, hence `1210 A^(3/2)d^(13/2)` when `s²≤Ad` | Empty completion block, `m,n≥2` |
| One small column, exactly one remaining column; or full transpose | `4p+16C H(H+p)`, hence `O(d⁴)` at the displayed cutoff | All rows ≥`U`, `1≤H<U`; universal constant `C` from Morris’s zero-range theorem, not extracted numerically |
| Both sides below `U`, at any aspect ratio | `15488d⁷` | Positive margins on both sides; use the variable-capacity context described below |

Each dyadic allowance is at most twice its rational counterpart. The minimum
of applicable old and new allowances may be taken; a smaller power need not
give the smaller numerical value on every small instance.

## One small line: count occupied donors

Suppose column `j₀` has margin `H<U`, all rows and all other columns have
margins at least `U`, and `H≥1`. The small mask is this full column, with
`p=m≥2`. A balanced profile `A` is a composition of `H` into `p` entries.

Every defect repaired to `A` has the form
`(x,q)=(A,A+e_s−e_t)` with `s≠t` and `A_t>0`. Conversely every such pair is
feasible: donor positivity bounds the incremented receiver by `H<U`.
The repair crossing is `t` itself, so repair leaves `x=A` and the dense
completion unchanged. Thus its completion weight is exactly `w_A`.

The exact weighted repair load is

```
Σ_(z:R(z)=A) w_z = (p−1)|supp(A)| w_A ≤ D w_A,
D=(p−1)min(p,H).
```

The generic repair proof can use a fixed label set of size `D`: rank the
donor within `supp(A)` and the receiver among the other `p−1` cells. Given
the repaired `A` and those ranks, the original defect is determined. This is
an injectivity argument at fixed `A`; the rank map may depend on `A`.

In the original row-major context, the actual correction at level `l` is

```
c_l = Σ_(A in left child) w_A Σ_(t later) A_t(U+1−A_t)
    ≤ H(U+1) z_(l−1).
```

The estimate is pointwise before summing completion weights. Positive support
has diameter at most `H`, so the retained spectral theorem gives

```
T=H(H+1)+2H(U+1)≤3U²,
C_full≤T+(sqrt(DT)+1)².
```

For rational defect proposal `β=1/(2Q)`, the general accepted-trace comparison
gives the inverse-gap allowance `4Q C_full`, where `Q≤4p−3`. The factor two
for half acceptance is included. There is no additional full/defect mass
ratio: normalized variance and energy both divide by defect mass.

Retaining the generic `p²` repair labels gives `96p³U²`; the compressed labels
also give the convenient bound `144p(p−1)min(p,H)U²`. Either can be used,
or the exact square-root expression retained.

For a single small row, transpose the **whole graph**, swapping `x,q` and
the defect labels. Its completions, neighbors and accepted conductances
correspond. The original row-major correction on that row instead contains
`(A_t+1)(U−A_t)` terms, including contributions from zero entries. It does
not satisfy the preceding left-child identity; the transpose is essential.

When exactly one large column remains, every completion is unique. The
[zero-range correspondence](zero-range-subclass.md) then gives the much
stronger reviewed allowance `4p+16C H(H+p)`. This narrower family can also
be sampled directly by weak compositions; its main role here is to show how
using actual exchange geometry can remove the generic repair losses.

## Empty completion: retain the smaller degree and exact conductance

If one entire margin side is below `U`, every cell is small and every actual
completion weight and accepted conductance is one. A defect has at most
`2(m+n−2)` defect neighbors and exactly one balanced repair neighbor. Use
`Q=2(m+n)−3=2s+1`.

The harmonic extension has exactly the trace energy, with no loss for half
acceptance. The [compiled full variance](physical-spectral-chain.md) has
coefficient `C≤2p³U²`; variance restriction therefore gives

```
K_rational≤C/β=2QC≤4Qp³U².
```

At the displayed cutoff this is `484(2s+1)d²p³s²`. Since `s≥2,p≤d`, it is
at most `1210d⁵s³`. A fixed aspect class with `s²≤Ad` gives
`1210A^(3/2)d^(13/2)`. Squares can take `A=4`, but square shape is not required.
Arbitrary aspect gives the conservative `45d⁸` rational / `90d⁸` dyadic
allowances from `3s<d`.

## Both sides small: sum the actual coordinate widths

Assume every margin is positive and below `U`. Put `a=min(m,n)` and
`B_ij=min(r_i,c_j)+1`. The [variable-capacity argument](rectangular-defect.md)
preserves all actual states, repairs, edges and energies with these capacities.
For the new spectral argument, use the literal current capacity `B_s` and
suffix capacities `(B_t:t>s)` in the same boxed kernel. The repair injection
bounds the actual correction by `Σ_(t>s) floor((B_t+1)²/4)` times the larger
adjacent child mass. Consequently

```
T_s≤(B_s−1)B_s+2Σ_(t>s)floor((B_t+1)²/4)≤Σ_t B_t².
```

The last inequality uses integer `B_t≥2`. If `t_ij=min(r_i,c_j)`, positive
margins give `B_ij≤2t_ij`, and the common total `M≤aU` gives

```
Σ B_ij²≤4U Σ t_ij≤4a²U².
```

Finite exposure over the variable alphabets, unchanged unique edge ownership
and the existing repair inequality give `C_full≤8p²a²U²`. Exact unit trace
normalization gives `K≤32(m+n)p²a²U²`. Since `m+n≤2p/a`, `s≤m+n`, `p≤d` and
`a≥2`, substitution of `U=11ds` yields

```
K≤30976d²p⁵/a≤15488d⁷.
```

This applies at every both-small aspect ratio. The variable-alphabet exposure
and its link to the retained spectral theorem still need formal assembly;
the uniform `wordWeight` API cannot simply be reused unchanged. Positivity
is essential to the width sum: adding arbitrarily many zero-margin coordinates
and flooring their capacities at two would invalidate that step.

## Evidence and the next unrestricted obstacle

The [exact report](../reports/direct-defect-variance.json) checks weighted
incidence/trace identities on three actual graphs and the one-column moment,
repair load and complete transpose on a fourth graph with nonconstant
completion weights. It also distinguishes a generic graph obstruction from
actual table examples. Replay with:

```sh
python3 experiments/direct_defect_variance.py \
  --output .local/reports/direct-defect-variance.json
```

The [generic repair limitation](generic-repair-limit.md) explains why another
unrestricted power reduction needs more actual table geometry. None of the
finite checks proves a general mixing theorem or practical speed advantage.
