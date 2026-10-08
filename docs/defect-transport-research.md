# Can defect transport remove another factor of p?

Research assessment, 8 October 2026. The reviewed #115 proofs, implementation,
and full-chain milestone are unchanged. This note gives method obstructions,
an exact special-case repair count, and a conditional route worth investigating.
It does not establish a sharper general spectral gap or a new Lean theorem.

The answer so far is specific: **averaging direct repairs cannot remove the
factor on the unchanged graph. Aggregated transport through defect-to-defect
edges remains plausible, but #114's defect-mean theorem leaves an essential
within-type variance term uncontrolled for #115.**

All source statements below use OpenAI `math` commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The current #115 comparison is

$$
 C_T=\frac{U(U+1)}2\left(2+\frac{(p-1)(U+1)^2}{2}\right),
 \qquad C_{\rm full}=(1+2p^2)C_T+2.
$$

Thus $C_T=O(pU^4)$ and the existing repair comparison gives
$C_{\rm full}=O(p^3U^4)$. The unchanged Dirichlet comparison then contributes
the additional $O(d^2)$ factor. No constant in that milestone is replaced here.

## What the pinned #114 proof already does

[`defect_conditional_transport`][common-conditional] compares a defect-type
mean to a transversal mean conditional on one assignment in the two affected
binary pairs. [`defect_mean_bound`][common-mean] then averages all four
assignments using their masses. If their masses are $s_o$, then
$\sum_o s_o=Z_0$, and weighted Cauchy--Schwarz gives

$$
 Z_0(\mu_{\rm defect}-\mu_0)^2
 \le\sum_o s_o(\mu_{\rm defect}-\mu_o)^2.
 \tag{1}
$$

This averaging is already in the pinned Lean source. Its conditional
coefficient is $4s_o/Z_0+1+8(p-2)$ before its displayed relaxations.
Summing the four assignments gives $8+32(p-2)$; the exported theorem weakens
this to $8+32p$. A proposed transfer should begin from this baseline.

The resulting observable is a projection: individual transversal values are
kept, but each defect type is replaced by its mean. This distinction is
material. A bound on its variance does not bound arbitrary fluctuations
inside a defect type, which the #115 full-chain theorem must handle.

## The generic repair argument cannot yield a label-free constant

Take two base vertices of unit weight, joined by an edge. Attach $D$ unit-weight
defect leaves to each base vertex, using one label per leaf position. Repair
each leaf to its adjacent base. Weight domination, injectivity within each
label, and distinct repair edges all hold.

Give one base and its leaves value $+1$, and the other side value $-1$.
The unnormalized base variance is $2$, full variance is $2(D+1)$, repair
energy is zero, and graph energy is $4$. Therefore a repair-only argument
cannot replace its order-$D$ multiplier by a constant. This example omits
the physical exchange structure; it obstructs the abstract repair route,
not a stronger theorem using those extra physical edges.

There is also an obstruction to improving the lifted base-mass step by an
arbitrary randomized repair. In a uniform-weight example, let $Q(x,b)$ be
any probability distribution over base targets for each defect. Its load is
$a_b=\sum_xQ(x,b)$, so

$$
 \sum_ba_b=|\mathcal D|,\qquad
 \max_ba_b\ge\frac{|\mathcal D|}{|\mathcal T|}.
 \tag{2}
$$

Even a centered quadratic comparison
$\sum_ba_b(H_b-\bar H)^2\le D'\sum_b(H_b-\bar H)^2$
for all $H$ requires $D'\ge|\mathcal D|/|\mathcal T|$ when
$|\mathcal T|>1$. To see this, sum the comparison over the centered
indicator functions $H^{(a)}_b=\mathbf1_{a=b}-1/|\mathcal T|$.
For each $b$, their squared values sum to $1-1/|\mathcal T|$.
This cancels the same factor on both sides and yields (2)'s lower bound.

## Actual #115 instances attain quadratic repair load

Consider an $n\times n$ instance with all row and column margins equal to an
integer $M<U$. The large block is empty, every feasible weight is one, and
$p=n^2$. Transversals are exactly the ordinary contingency tables with those
margins. Write a defect as $(x,q)$, with negative cell $s$ and positive cell
$t$, so $q=x-e_t+e_s$. Put $v=(\operatorname{row}(t),\operatorname{col}(s))$.

For a fixed transversal table $A$, the source's inverse repair is

$$
 x=A+e_t-e_v,\qquad q=A+e_s-e_v.
 \tag{3}
$$

For $s\ne t$, this is feasible **if and only if $A_v>0$**. Positivity of
$A_v$ makes both views nonnegative. The first view has the old row margins,
and the second the old column margins, so both remain at most $M<U$.
If $A_v=0$, at least one view has a negative entry, including the cases
$v=s$ or $v=t$. For each receiver $v$, there are $n^2-1=p-1$ ordered pairs
$(s,t)$ with that receiver. Therefore the exact count is

$$
 |\mathcal R^{-1}(A)|=(p-1)\,|\operatorname{supp}(A)|,
 \qquad
 \frac{|\mathcal D|}{|\mathcal T|}
 =(p-1)\,\mathbb E_{A\in\mathcal T}|\operatorname{supp}(A)|.
 \tag{4}
$$

A fully positive $A$ attains $p(p-1)$ incoming defects. This is possible
within the physical construction, for example when $M\ge n$.

Quadratic average load also occurs under the published scales. Let
$d=10+(n+1)^2$, $U=d^{20}$, and choose $M=8d^3<U$. The source
[small-entry lemma][model] applies to $a=M,t=1$ and gives
$\Pr(A_{ij}=0)\le4d^3/M=1/2$. Summing over cells and applying (4) gives

$$
 \frac{|\mathcal D|}{|\mathcal T|}\ge\frac{p(p-1)}2.
 \tag{5}
$$

Thus even a randomized repair allowed to target arbitrary transversals cannot
turn the lifted base-mass coefficient into $O(p)$ uniformly. This is a
statement about that comparison step; additional edge energy can still make
the full Poincare constant substantially better than the repair bound.

Equation (4) does give a useful special-case refinement. Since a table of
total $N$ has at most $\min(p,N)$ positive entries,

$$
 |\mathcal R^{-1}(A)|\le(p-1)\min(p,N)
 \qquad\text{in this all-small setting}.
 \tag{6}
$$

For permutation margins, $N=n$ and the load is exactly $n(p-1)$ rather than
$p(p-1)$. This is an instance-sensitive improvement for sparse margins, not
a general reduction of the worst-case exponent. It has not been substituted
into the formal repair theorem.

## Multiple direct repairs are absent from the unchanged physical graph

In the same all-small family, **every defect has exactly one transversal
neighbor in the full physical graph: its designated repair.**

A doubled-coordinate unit exchange either changes two $x$ coordinates, two
$y$ coordinates, or one of each. A mixed move changes the total of $x$, so
cannot be feasible when every row-view margin is fixed. A move of two $x$
coordinates must stay in one row and leaves $q$ unchanged. To end at a
transversal, its new common table must therefore be $q$. That has the
required row margins only if $s,t$ share a row, in which case $q$ is exactly
the designated repair. Similarly, a move of two $y$ coordinates changes $q$
within one column and leaves $x$ unchanged. It can reach a transversal only
if the labels share a column, again giving the designated repair. If neither
coordinate is shared, no unit exchange reaches a transversal. The graph then
adds precisely the one designated repair edge.

Other balanced tables may be obtainable by a different table-repair formula,
but their edges are not automatically in the published graph. Averaging such
edges would change the chain. Routes through existing defect vertices are
the relevant alternative if the graph is to remain fixed.

## The missing within-type term is real

Let $QH$ retain $H$ on transversals and replace each positive-mass defect
class $\mathcal D_\lambda$ by its weighted mean $\mu_\lambda$. Finite
conditional-variance decomposition gives the exact unnormalized identity

$$
 \operatorname{Var}_{\rm full}(H)
 =\operatorname{Var}_{\rm full}(QH)
   +\sum_\lambda\sum_{X\in\mathcal D_\lambda}
       f(X)(H(X)-\mu_\lambda)^2.
 \tag{7}
$$

Zero-mass classes contribute zero and need no probabilistic conditional mean.
The second term is absent from a projected-observable theorem.

An exact $2\times2$ example with all margins two makes the issue explicit.
It has three transversals and 24 defects. Set $H=0$ on transversals and, on
each defect type, set $H=x_{11}$ minus that type's mean of $x_{11}$. Then

$$
 \operatorname{Var}_{\rm full}(QH)=0,
 \qquad \operatorname{Var}_{\rm full}(H)=6,
 \qquad E(H)=6.
 \tag{8}
$$

Its defect-to-defect energy is zero; all six units of energy occur on edges
to transversals. Hence a proposed bound of the within-type term solely by
defect-to-defect energy also fails. A new argument may use all physical
energies, but cannot omit this term or automatically charge it to those edges.

There is a related obstruction to simply rerunning the transversal exposure
proof inside a fixed defect class. With four slots and $U=2$, consider a leaf
display with pairs $(0,1),(1,2),(1,2),(1,1)$. Its occupancies are
$(1,3,3,2)$: an existing negative and positive slot, plus the newly exposed
excess slot. Removing one unit from the fourth ordinary slot leaves
$(1,3,3,1)$, with two positive and two negative slots. This is outside the
one-defect state space. It is a combinatorial interface obstruction, not an
assertion that this template has positive weight in a specific table instance.
The current transport theorem cannot silently charge such auxiliary edges to
the physical graph.

## A precise target for aggregated transport

Let $V_0$ be the unnormalized transversal variance, $Z_\lambda$ the mass of
defect type $\lambda$, and $W$ the within-type sum in (7). Centering at the
transversal mean gives

$$
 \operatorname{Var}_{\rm full}(H)
 \le V_0+W+\sum_\lambda Z_\lambda(\mu_\lambda-\mu_0)^2.
 \tag{9}
$$

Thus a concrete sufficient new result is

$$
 W+\sum_\lambda Z_\lambda(\mu_\lambda-\mu_0)^2
 \le C_*p^2U^4 E(H)
 \tag{10}
$$

with an absolute constant $C_*$ under the actual source hypotheses. Together
with the existing $C_T$, it would remove one factor of $p$ from the current
full-variance order, giving $O(d^4U^4)$ after the unchanged transition
comparison. Equation (10) is a target, not an established inequality here.

For the mean part, the #114 method suggests retaining actual conditional
masses and localized edge energies. Suppose, for each type $\lambda$, a
partition of the transversal has masses $z_{\lambda a}$ and means
$m_{\lambda a}$, and a proved local transport bound has the form

$$
 z_{\lambda a}(\mu_\lambda-m_{\lambda a})^2
 \le c_{\lambda a}\,E_{\lambda a}(H),
 \qquad\sum_a z_{\lambda a}=Z_0.
$$

Applying (1) before discarding normalizations yields

$$
 \sum_\lambda Z_\lambda(\mu_\lambda-\mu_0)^2
 \le\sum_{\lambda,a}\frac{Z_\lambda}{Z_0}
                 c_{\lambda a} E_{\lambda a}(H).
 \tag{11}
$$

If each $E_{\lambda a}$ is the energy of a literal subset of physical edges,
the right side is at most $\Gamma E(H)$, where

$$
 \Gamma=\max_e\sum_{\lambda,a:\ e\in E_{\lambda a}}
                   \frac{Z_\lambda}{Z_0}c_{\lambda a}.
 \tag{12}
$$

This exposes the needed proof objects: a valid integer-slot conditional
transport, its actual physical leaf-edge classification, the weighted
multiplicity in (12), and a separate bound on $W$ using the same graph.
Replacing every local energy by $E$ first loses precisely the aggregation
information. Conversely, a good multiplicity calculation alone does not
establish the transport inequality or the within-type bound.

## Exact checks and practical conclusion

[`defect_transport.py`](../experiments/defect_transport.py) enumerates synthetic
all-small instances by two independent descriptions: ordinary tables followed
by inverse repairs, and row views followed by the defect equation and column
margin tests. The state sets agree. It checks the support count (4), unique
transversal neighbor, and the absence of same-type exchange edges. Selected
cases independently enumerate literal doubled-coordinate exchanges too.

| Dimension | Common margin | Transversals | Defects | Largest repair load |
|---|---:|---:|---:|---:|
| $2\times2$ | 1 | 2 | 12 | 6 |
| $2\times2$ | 2 | 3 | 24 | 12 |
| $2\times2$ | 4 | 5 | 48 | 12 |
| $2\times2$ | 8 | 9 | 96 | 12 |
| $3\times3$ | 1 | 6 | 144 | 24 |
| $3\times3$ | 2 | 21 | 792 | 48 |
| $3\times3$ | 3 | 55 | 2,520 | 72 |
| $4\times4$ | 1 | 24 | 1,440 | 60 |

For $2\times2$ margins $M$, the exact formulas are
$|\mathcal T|=M+1$ and $|\mathcal D|=12M$. The report records exact
observable variances and energies, including (8), but computes no spectral
eigenvalue and makes no inference about a universal gap from these ratios.
Increasing $U$ above the margins changes only the complementary $y$
coordinates, so these graphs also occur at the published threshold.

```sh
PYTHONPATH=src python3 experiments/defect_transport.py --output reports/defect-transport-research.json
```

The [report](../reports/defect-transport-research.json) contains only synthetic
parameters and exact arithmetic. The feasible next mathematical step is to
design a transport for (10) that moves among defect labels while controlling
the within-type term. Replacing deterministic repair with a convex combination
of existing direct repair edges cannot achieve that step in general.

[common-conditional]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/MatroidCounting/CommonBases.lean#L4239
[common-mean]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/MatroidCounting/CommonBases.lean#L4396
[model]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/model-and-graph.tex
