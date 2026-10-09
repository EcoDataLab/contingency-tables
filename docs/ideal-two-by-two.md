# An exact small example of the ideal #115 chain

The ordinary `2 × 2` fiber with both margins `(t,t)` has only `t+1`
tables. Nevertheless, the source's all-small ideal chain uses `13t+1`
physical states. Its behavior can be calculated exactly. This gives a
useful test of the implementation, explains why short trajectories can be
misleading, and supplies a lower bound on this chain's possible mixing
improvement.

The argument below concerns `1 ≤ t < U`, so every cell is small. The
completion block is empty, all physical states have weight one, and padding
has no effect. For the literal source parameters, `d=19`, `U=19^20`, and the
per-neighbor proposal probability is `β=1/16384`. The source graph and its
unchanged dyadic proposal are documented in the
[implementation crosswalk](ideal-chain-experiment.md).

This is a mathematical derivation with an exact rational certificate and
finite implementation checks. It is not a Lean theorem or a runtime bound
for the complete finite-bit sampler.

## The graph is a row of identical finite blocks

Write a physical state as `(X,Q)`, where the rows of `X` and the columns of
`Q` sum to `t`. A balanced state has `X=Q`. A defect has exactly one `+1`
and one `−1` in `Q−X`. The doubled source coordinates are `(X,U−Q)`.

Let `(a,b,c,d)=(X00,X11,Q00,Q11)`. The four entries of `Q−X` are

```
(c−a, a−d, b−c, d−b).
```

A balanced state has all four diagonal coordinates equal to some
`k ∈ {0,...,t}`. In a defect, those coordinates take the two values `k`
and `k+1`, with a unique `k ∈ {0,...,t−1}`. There are twelve permitted
nonconstant binary patterns. The other two nonconstant patterns,
`(0,0,1,1)` and `(1,1,0,0)` in the displayed order, would create four
nonzero differences and are excluded.

Each interval between balanced tables `k` and `k+1` therefore contains
exactly twelve defect states. More explicitly, add

```
(k, t−k−1, t−k−1, k)
```

to both row-major views of the `t=1` graph. This produces that interval's
fourteen states, including its two endpoints. Neighboring intervals share
only their balanced endpoint.

A feasible unit exchange within `X` must preserve its row sums; within `Q`
it must preserve its column sums. It changes exactly one of the four
diagonal coordinates. A mixed exchange between `X` and `U−Q` changes a
view's fixed total and is infeasible. Consequently an exchange cannot jump
between the interiors of two intervals: changing the unique minimum or
maximum first reaches the common balanced endpoint. The designated repair
`X−e_t+e_(t.row,s.column)` also reaches one of that interval's endpoints.

The independent base enumeration has fourteen vertices and twenty-eight
undirected edges. Thus the whole graph has

```
physical vertices = 13t+1
undirected edges  = 28t
balanced tables  = t+1.
```

## A rational certificate determines the return chain

Set the left balanced endpoint's potential to zero and the right one's to
one. The [saved certificate](../reports/ideal-two-by-two.json) lists the
potential at every base vertex. Each defect satisfies the exact harmonic
identity

```
degree(v) h(v) = sum of h(w) over neighbors w.
```

The sum of squared potential differences over undirected edges is `32/15`.
This is the unit-conductance Schur complement between the two endpoints.
Gluing blocks therefore makes the balanced-state first-return kernel the
reflecting path on `0,...,t`, with

```
q = 32β/15
P(k,k−1) = q when k>0
P(k,k+1) = q when k<t,
```

and all other mass holding. At the literal proposal, `q=1/7680`.
This includes immediate returns caused by holding at a balanced state.
Drawing directly from this small return matrix bypasses physical
excursions; its draw time is not the runtime of the source chain.

Every defect has exactly one balanced neighbor. At any defective state the
next physical step therefore returns with probability `β`, regardless of
the preceding path. Its time to hit balance is geometric with mean `1/β`.
The endpoints have six defect neighbors and interior balanced states have
twelve. The expected first-return lengths, counting the initial step and
all holds, are consequently seven at each endpoint and thirteen inside.
Their stationary average is

```
(13t+1)/(t+1) = 1 / stationary_probability(balance).
```

A short trajectory often holds at its starting table for a long time. A
rare departure can then produce a much longer excursion. This explains why
the benchmark records exhausted excursion budgets explicitly and does not
turn successful short runs into a claimed speed advantage.

## Exact accuracy and a quadratic obstruction

For the table observable `k=X00`, the stationary variance is `t(t+2)/12`.
Solve the path Poisson equation using differences

```
g(k+1)−g(k) = (k+1)(t−k)/(2q).
```

The finite identity
`sum_{j=1}^t j²(t+1−j)² = (t+1)((t+1)^4−1)/30`
then gives the exact stationary asymptotic variance inflation

```
lim n*Var(mean of n returned observations) / Var(k)
    = ((t+1)^2+1)/(5q) − 1.
```

It is **7,679** at `t=1` and **15,359** at `t=2`. These are exact
stationary accuracy comparisons, not measured effective sample sizes from
a short run. An iid uniform-table draw has inflation one. The benchmark's
full-line heat bath also has inflation one here: this single rectangle
spans the entire fiber, so each update draws a fresh uniform table. Each
method has its own preprocessing and draw cost.

There is also a direct Rayleigh witness for the full physical chain.
Extend the observable to each block by `H(k,v)=k+h(v)`. The twelve interior
base potentials have sum `6` and sum of squares `734/225`. Summing across
blocks gives mean `t/2`, unnormalized variance

```
t*(13t²+3t−514/75)/12,
```

and unnormalized Dirichlet energy `β*t*32/15`. Normalizing both by the
number of physical states cancels. Therefore the full physical chain's
inverse spectral gap is at least

```
5*(13t²+3t−514/75)/(128β).
```

Taking `t=U−1` shows an `Ω(U²)` obstruction for the same free-cutoff
all-small chain family at fixed `2 × 2` dimensions and proposal. This does
not prove that the current universal `U⁴` upper bound is optimal, and does
not constrain other table samplers. It identifies a real quadratic
contribution that any sharper analysis of this chain must retain.

## Reproduce and scope

[The exact experiment](../experiments/ideal_two_by_two.py) builds its base
catalog independently from binary row-valid and column-valid views and
checks the rational harmonic certificate without a numerical solver. For
`t=1,...,6`, it compares the complete glued state and edge catalogs with
the separate ideal-chain implementation, then checks the exact censored
kernel, all return-time means, Poisson variance, and full-chain Rayleigh
quotient. Source hashes accompany the report.

```sh
PYTHONPATH=src python3 experiments/ideal_two_by_two.py --output reports/ideal-two-by-two.json
```

The general graph decomposition is justified above; the six finite cases
check the implementation and algebra, not every integer margin by
exhaustion. Caps, structural zeros, nonuniform weights, nonempty dense
completion blocks, and the complete finite-bit correction program are
outside this example.
