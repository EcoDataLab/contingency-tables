# Scale audit and an improved small-entry estimate

Research snapshot: 8 October 2026. Source: OpenAI `math`, commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, *Exact Uniform Sampling of
Contingency Tables with Arbitrary Margins*. The initial review is preserved
unchanged in [115/115-contingency-tables-review.md](../115/115-contingency-tables-review.md).

**Result.** A direct counting argument improves the paper's small-entry
probability bound from `4td³/a` to

$$
 \Pr\{X_{ij}<t\}\le
 \frac{t(m-1)(n-1)}{a-t+1},\qquad 1\le t\le a.
 \tag{1}
$$

This is a proved elementary lemma for unrestricted uniform integer tables.
It uses the classical switching method; we do not claim priority for the
inequality. Combined with the source's dense-bin construction and the
[localized transport derivation](transport-localization.md), it permits the
manuscript-level parameter choice

$$
 A=16d^2,\quad B=16d^3,\quad L=32d^3,\quad U=128d^5,
 \qquad d=10+(m+1)(n+1)\ge14.
 \tag{2}
$$

The resulting **conditional ideal small-chain inverse-gap bound is
$O(d^{25})$**, improving the review's `O(d³³)` candidate. The word
conditional refers to its dependence on the upstream signature/transport
results and the local-energy derivation, plus an uncompleted integration
into the complete sampler. It is not a new end-to-end bit-complexity
exponent or a Lean-verified replacement for the upstream program.

The Python checks provide exact rational finite examples and finite
polynomial certificates valid for every integer `d ≥ 14`. They do not
certify the full analytic or machine implementation theorem. The upstream
source and original review have not been altered.

## 1. Count every switching, instead of selecting one donor pair

Let `Ω` be the nonempty finite set of all nonnegative integer `m × n`
tables with prescribed margins. Mark cell `(i,j)` and suppose its two
incident margins `r_i,c_j` are at least an integer `a`. No other margin
has to be positive. Let `t` be an integer with `1 ≤ t ≤ a`.

For a source table `X` with `h=X_ij<t`, choose any `i'≠i`, `j'≠j`, and

$$
 1\le v\le\min(X_{i j'},X_{i' j}).
$$

Subtract `v` at the two donor cells `(i,j')`, `(i',j)`, and add it at
`(i,j)`, `(i',j')`. These four positions are distinct. The output `Y`
is nonnegative and has exactly the same margins. Repeated target tables
are allowed: we count an incidence relation with labeled switchings.

The number of choices from `X` is

$$
 D(X)=\sum_{i'\ne i,\,j'\ne j}
       \min(X_{i j'},X_{i' j}).
$$

For nonnegative finite lists `(u_k),(v_l)`,

$$
 \sum_{k,l}\min(u_k,v_l)
 \ge\min\!\left(\sum_k u_k,\sum_l v_l\right).
 \tag{3}
$$

To see this, first use
`Σ_l min(u,v_l) ≥ min(u,Σ_l v_l)` for each `u`, then apply the same
inequality to the outer sum. The one-list inequality follows by two
cases: if one summand reaches the cap, the sum reaches it; otherwise
the capped sum equals the uncapped sum. Empty lists cause no problem.
Consequently,

$$
 D(X)\ge\min(r_i-h,c_j-h)\ge a-t+1.
$$

Conversely, fix a target table `Y` and the label `(i',j',h)`. The amount
must be `v=Y_ij−h`; reversing the four changes recovers a unique source,
if it is valid. There are at most `t(m−1)(n−1)` such labels. Double
counting gives

$$
 |\{X\in\Omega:X_{ij}<t\}|(a-t+1)
 \le |\Omega|\,t(m-1)(n-1),
$$

which proves (1). A right-hand side larger than one is simply a weak
upper bound. The useful corollary, when `t ≤ a/2`, is

$$
 \Pr\{X_{ij}<t\}\le\frac{2t(m-1)(n-1)}a
 <\frac{2td}a.
 \tag{4}
$$

The exact denominator in (1) is preferable when optimizing constants.
Unlike the source proof, this argument needs neither `a ≥ 4d` nor a
rounding lower bound for a single chosen donor interval.

**Refinement using the target's value.** Put `e=(m−1)(n−1)` and let
`F=|Ω|`. For a target with marked value `y`, a reverse label must have
`0≤h<min(t,y)`, since the switching amount is positive. There are therefore
at most `e min(t,y)` incoming labels. Summing the incoming and outgoing
bounds over the same incidence relation yields

$$
 \sum_{X:\,h<t}(a-h)
 \le e\sum_{Y\in\Omega}\min(t,Y_{ij})
 =e\left[tF-\sum_{X:\,h<t}(t-h)\right].
$$

Each summand on the left after rearranging is
`a−h+e(t−h)≥a−t+1+e`. Hence the stronger bound is

$$
 \Pr\{X_{ij}<t\}\le\frac{te}{a-t+1+e}.
 \tag{1a}
$$

For `2×2` tables with both margin vectors `(a,a)` and `t=1`, the
marked value is uniform on `0,…,a`; (1a) is the exact probability
`1/(a+1)`. Both (1) and (1a) are retained in the code. The parameter
choice below uses the simpler (1), so this refinement changes no other
claimed bound or prerequisite.

**Boundary and scope checks.** If there is one row or one column,
`X_ij` is a prescribed incident margin, so the event is empty; (1) gives
zero. Zero margins elsewhere may remain in the table or be removed.
An empty dimension has no marked cell and uses the source's deterministic
completion convention. The proof does not apply to arbitrary cell caps,
structural zeros, or nonuniform weights: a switch may leave that fiber or
change its mass. For example, with row and column margins `(5,5)` and
cell `(1,1)` forbidden, that cell is always zero, contradicting an
unjustified capped use of the `1/5` bound. Thus this improvement does not
by itself improve the cell-bounded companion FPRAS.

## 2. Exact reference completion adjustments

Fix a reference cell `(i₀,j₀)` in a nonempty large rectangle. Write
`E_ab` for a matrix unit. The paper's reference-star map sends changes
in residual margins to the following forms:

| Graph change | Residual changes | Reference adjustment |
|---|---|---|
| Exchange two row-view coordinates | `ΔR=e_a−e_b`, `ΔP=0` | `E_a,j₀−E_b,j₀` |
| Exchange two column-view coordinates | `ΔR=0`, `ΔP=e_a−e_b` | `E_i₀,a−E_i₀,b` |
| Exchange between row and column views | `ΔR=εe_a`, `ΔP=εe_b` | `ε(E_a,j₀+E_i₀,b−E_i₀,j₀)` |
| Repair whose receiving cell is small | zero | zero |
| Repair whose receiving cell is large | `ΔR=e_a`, `ΔP=e_b` | `E_a,j₀+E_i₀,b−E_i₀,j₀` |

Here `ε ∈ {−1,+1}`; inverse repairs negate the corresponding matrix.
Coincident positions in each expression are combined before counting
support. A row/column outside the large rectangle has residual zero at
both feasible endpoints. Thus its change is zero: a same-view exchange
either cancels on such a line or both changed lines are large. In the
mixed-view case each individually changed line must be large. This is
the missing feasibility qualification in an argument that merely lists
coordinate changes.

It follows for every actual graph edge that

$$
 \|D_{XY}\|_\infty\le1,\quad
 |\operatorname{supp}D_{XY}|\le3,\quad
 |\{(i,j):D_{XY,ij}<0\}|\le2.
 \tag{5}
$$

At least one of the two orientations has at most one negative entry.
These conclusions remain true if the large block has a single row or
column: the matrix units cancel in the displayed formulas, and the
adjustment equals the difference of its unique completions. Their
translation is then accepted with probability one. If the rectangle is
empty, both completion fibers contain only the empty table and every
proposal is accepted; no reference cell is selected.

Every nonempty completion margin is at least `L`. A negative entry in
`D` rejects only when the source completion entry is zero. Applying (1)
inside the large rectangle, whose dimensions are at most the global
`m,n`, gives the uniform directional estimate

$$
 \Pr(\text{reject }X\to Y)\le \frac{2d}{L}.
 \tag{6}
$$

With (2), this is `1/(16d²)`, well below one half. Translation has an
inverse, so its accepted cardinality `c_XY=c_YX` is symmetric; all the
source's detailed-balance statements still apply. In fact the orientation
with at most one negative entry yields

$$
 c_{XY}\ge(1-d/L)\min(f(X),f(Y)).
 \tag{7}
$$

We keep the simpler published comparison
`E_P ≥ E/(128d² Λ)` for compatibility. Even the old small-entry lemma,
together with (5), would give directional rejection at most `8d³/L=1/4`
for (2). The new small-entry lemma is essential for reducing `U`, rather
than for getting half acceptance with this choice of `L`.

## 3. Generic dense-bin argument: every numerical dependency

In this section the completion rectangle has `a,c ≥ 2` and
`e=(a−1)(c−1)≤d`. All scales are positive integers and `K₀=4B`.
The following conditions are sufficient for the analytic dense sampler:

$$
 L\ge2B,\quad B\ge8d^3,\quad Ad\le B,\quad
 \frac{2d^2}{A}+\frac{2d^3}{B}\le\frac14.
 \tag{8}
$$

These inequalities must be used together with the constructions below;
checking them alone is not a proof of the whole sampler.

1. **Widths and containment.** For `s_ij=min(R_i,P_j)≥L`,
   `w_ij=floor(s_ij/B)` satisfies `s_ij/(2B)≤w_ij≤s_ij/B` and is positive.
   Hence every feasible free entry has a unique bin/offset representation
   with bin coordinate at most `2B<4B`. The continuous feasible polytope
   lies in `[0,2B]^e`. Sorting the largest row and column last is retained.
2. **Slack and regularity.** The source constructs a point with every
   normalized affine entry `T_ij≥1/(2d)`. Each entry has at most `d`
   coefficients, each at most `1/B` in magnitude. Thus its sup-norm
   Lipschitz constant is `d/B`. The penalty
   `p=max(0,max_ij(−T_ij−d/B))` is convex, is `d/B`-Lipschitz, and satisfies
   `0≤p≤4d` on `[0,4B]^e`. These steps use no original hard-coded powers.
3. **Density comparison.** `ρ=2^(−Ap)`, `E_v=floor(Ap(v))`, and
   `W(v)=2^(−E_v)` give `W(v)=1` for every bin meeting the feasible
   polytope. Across one bin,
   `|Ap(u)−E_v|≤1+Ad/B≤2`, so `W(v)/4≤ρ(u)≤4W(v)`.
4. **Inner volume.** Contracting toward the slack point by
   `α=4d²/B≤1` gives normalized slack at least `2d/B` and retains
   volume at least `(1−α)^e≥1−4d³/B≥1/2`. Its bins are completely
   feasible, apart from null boundary choices. With (2), this bound is
   actually `3/4`, but half is sufficient.
5. **Normalizer.** The relaxed polytope with slack `−γ` has volume at
   most `exp(2d²γ)V`, where `V` is the original volume. Put
   `u=2d²/A`, `v=2d³/B`. Summing penalty layers gives
   `Z_B≤4 exp(u+v)/(1−exp(u)/2) V`. By (8), `u+v≤1/4`, and
   `exp(u),exp(u+v)≤4/3` (the geometric power-series bound suffices).
   Therefore `Z_B≤16V≤32V`. The retained source guarantee for an ideal
   bin-and-offset trial is at least `1/64`, with a uniform output
   conditional on success. Uniqueness of the integer representation is
   needed for that last assertion, including points on faces.
6. **Conductance.** The finite-box interpolation statement is unchanged.
   For the source face-cover radius `r=1/(4d)`, a cut-face neighborhood
   has volume at most one. The density factor there is at most
   `2^((Ad/B)(1+r))≤4`, using `Ad/B≤1` and `d≥14`. Thus the source
   cut comparison and proposal `q_B≥1/(16d)` still give
   `κ_B≥1/(10⁵d²K₀)` and
   `K_B=2(10⁵d²·4B)²=O(d¹⁰)` under (2). Sharper numeric constants are
   recorded in [error-budgets.md](error-budgets.md).
7. **Minimum mass and finite bits.** `0≤E_v≤4Ad` implies
   `π_B,min≥2^(−4Ad)/(4B)^e`. A safe base-two mass allowance is
   `4Ad+d ceil(log₂(4B))`, which is `O(d³)` under (2). All exponents
   are integer floors of rational inputs and can be computed exactly.
   Adjacent bins satisfy `|Ap(v)−Ap(v')|≤1`, hence
   `|E_v−E_v'|≤1`: an accepted/rejected Metropolis proposal needs at
   most one acceptance bit. The offset lengths, restart count, mixing
   length, common denominators, and exact-law tabulation must all be
   recomputed or explicitly upper-bounded for the chosen implementation.

This covers bin containment, positive volume, layer convergence, local
density changes, cut geometry, rejection, minimum mass, and random-bit
encoding. It does not replace a formal integration check of their
interfaces. The one-row, one-column, and empty dense cases remain
deterministic and do not invoke the positive-dimensional volume proof.

## 4. Unpadding and the new threshold

Apply (1) to all unrestricted tables with the enlarged **full** margins,
not separately conditioned on a small state. Every large cell has two
enlarged margins at least `U`. If `g` is the number of large cells and
`e₀=(m−1)(n−1)`, a union bound gives

$$
 \Pr\{\text{some large entry}<L\}
 \le \frac{gLe_0}{U-L+1}
 \le \frac{Ld^2}{U-L+1}.
 \tag{9}
$$

Thus it suffices that

$$
 U\ge L-1+2Ld^2.
 \tag{10}
$$

The simpler `U=4Ld²` in (2) satisfies this and `L≤U/2`. The proof
requires no independence between cells. If the large block is empty,
the bad event is empty. If the full table has a singleton dimension,
the original problem is handled deterministically.

The source's repair injection gives `Λ≤(1+d²)Z₀` for arbitrary positive
`U,L`: it depends on the small-slot definition and feasibility, not their
powers. Its capacity proof uses the fact that a small cell has an
incident original margin **strictly below `U`**. The source's bijection
between successful enlarged tables and original tables also remains
valid. At least half of all enlarged tables are successful by (9), and
their count bounds `Z₀` above. Consequently stationary unpadding success
is at least `1/[2(1+d²)]` with exactly uniform output conditional on
success, just as in the source.

Set `C=N+dL+U+2`, `b=d+ceil(log₂(C+2))` using the **new** values.
Every completion's total is at most `N+gL<C`, so its formal capacity
excludes no completion. Joint states still use fewer than `2d`
coordinates in `[0,C]`, giving `π_min≥(C+1)^(−2d)`.
Because (2) is polynomial in `d`, `b=O(d+log(N+1))` is preserved.

The localized transport bound has the form `K_small=O(d⁵U⁴)`.
Substitution of `U=128d⁵` gives `O(d²⁵)`. With the old small-entry
argument, `U=8Ld⁴` and `L=32d³` instead give `O(d³³)`; the review's
more conservative fallback `L=128d⁵,U=1024d⁹` gives `O(d⁴¹)`.
The original transport comparison, without localization, would give
`O(d⁶U⁶)=O(d³⁶)` under (2). These are distinct analytic statements.

## 5. Exact certificates and reproducible tests

Run:

```sh
PYTHONPATH=src python3 -m unittest discover -s tests -p 'test_scales.py' -v
```

The nine tests pass. They include:

- Every unrestricted fiber with total `0,…,6` in shapes `1×1,1×3,3×1,
  2×2,2×3,3×2,3×3`: 2,835 fibers, 7,238 tables, and 20,083 exact
  marked-cell/threshold cases, checking both the basic and refined
  small-entry bounds with exact fractions.
- All 33,836 labeled switches in those examples, checking that targets
  remain in the same fiber, outdegrees have the claimed lower bound,
  and `(target,i',j',h)` never has two source preimages.
- Every elementary residual-change family and every reference cell for
  block dimensions `1,…,5`, checking margins, antisymmetry, norm,
  support, and the negative-support bounds. Empty rectangles are checked
  separately.
- A capped negative control and an old-unpadding negative control. In
  particular, the new `U` fails the old `4Ld⁴/U≤1/2` criterion; (1)
  is essential, and cannot be silently replaced with the initial review.
- Equality of the refined zero-entry bound in every equal-margin `2×2`
  example with margin `1,…,19`.

The universal arithmetic certificate in
[`src/contingency115/scales.py`](../src/contingency115/scales.py) is stronger
than a finite sweep over dimensions. It substitutes (2) into every
cross-multiplied inequality, expands each residual as a polynomial in
`x=d−14`, and checks that **every integer coefficient is nonnegative**.
This proves those arithmetic inequalities for every `d≥14`, with no
floating-point logarithms or probability estimates. The analytic
switching proof above supplies its universal combinatorial premise.

For transparency, its main residual polynomials are
`L−2B=0`, `B−8d³=8d³`, `B−Ad=0`,
`AB−8d²B−8d³A=0`, `L−4d=32d³−4d`,
`U−L+1−2Ld²=64d⁵−32d³+1`, and
`U−2L=128d⁵−64d³`. Their signs can also be checked directly by factoring;
the coefficient certificates make the finite exact verification explicit.

## 6. Source map and remaining integration work

All references below use the pinned source. The manuscript section files
are under
[`preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections`](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections).

| Obligation | Manuscript source | Formal integration targets; not a claim of completed verification |
|---|---|---|
| Replace selected-donor proof with all-switchings lemma | `model-and-graph.tex`, `lem:small-entry`, lines 199–223 | `Sampling/SmallEntries.lean`, then `Sampling/Padding.lean`; reuse `fourCycle`, `fourCycle_marked`, and `fourCycle_injective`, introduce the incidence relation and reverse-label injection |
| Exact elementary reference adjustments | `algorithms.tex`, reference adjustment before `prop:small-chain`; `model-and-graph.tex`, `lem:repair` | `Transport/ReferenceCompletionEntries.lean`, `Transport/ReferenceCompletionBlock.lean`, `Transport/ReferenceCompletionBounds.lean`; prove edge-family classification |
| Acceptance from small-entry counts | `algorithms.tex`, `prop:small-chain` | `Transport/TranslatedCompletionAcceptance.lean`, `Sampling/SmallCompletionAcceptance.lean`; replace hard-coded `d¹²,10d` interface |
| Bin widths, geometry, volume, normalizer | `dense.tex`, `eq:width-bounds` through `prop:bin-acceptance` | `Dense/DenseScales.lean`, `DenseGeometry.lean`, `DenseInteriorVolume.lean`, `DenseNormalizer.lean`, `DenseLayerArithmetic.lean` |
| Conductance, minimum mass, mixing | `dense.tex`, `prop:bin-gap` | `Dense/DenseLocalGeometry.lean`, `DenseCutParameters.lean`, `DenseMixing.lean`; retain integral interpolation and face-cover hypotheses |
| Repair feasibility, stationarity, and success ratio | `model-and-graph.tex`, `lem:repair`, `prop:stationary-success`, lines 98–188 and 225–268 | `Sampling/FirstPaperStationaryMass.lean`, `FirstPaperSuccessRatio.lean`, `Transport/BalancedCompletionMass.lean`; carry generic `U,L` through physical encoding |
| Input bounds and state capacity | `model-and-graph.tex`, `eq:parameters`, completion total bound | `Parameters.lean`, `Sampling/FirstPaperBinaryParameters.lean`; redefine `C,b` coherently |
| Bounded draws and exact implemented law | `dense.tex`, `eq:dense-schedule` through `eq:dense-offset-count`; `algorithms.tex`, bounded sampler and tabulation sections | `Dense/DenseBitBudget.lean`, `DenseDrawTabulation.lean`, `Sampling/FirstPaperOuterBudget.lean`, `FirstPaperImplementedLaw.lean`, `ExactSamplingParameters.lean`, `ExactExpectedTime.lean` |
| Global output theorem and checked dependencies | `algorithms.tex`, exact correction and running time | Rebuild the changed import closure and rerun the configured Comparator; no such updated global theorem is supplied by this audit |

The formal file names are source-navigation targets. We inspected selected
interfaces and hard-coded powers, not their entire import closure. In
particular, changing just the constants in `Parameters.lean` is not an
adequate implementation: the old powers occur in analytic bounds,
program schedules, integer arithmetic, law tabulation, and machine costs.

Two barriers remain substantive. First, even `O(d²⁵)` is far too large
to establish usefulness on LEHD-scale tables; those applications need
separate executable methods and benchmarks. Second, bounded or weighted
fibers require a different argument that preserves their support and
target masses. Neither barrier is resolved by the ordinary-table scale
certificate.
