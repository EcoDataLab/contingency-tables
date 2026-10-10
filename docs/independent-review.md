# Independent review of the first #115 refinements

Review provenance: “independent” here means a separate AI agent reviewing AI-produced research or code within this project. This is not outside human peer review. Compiler and execution receipts have the narrower scopes stated below.

Review date: 8 October 2026. The pinned upstream revision is
`openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
This targeted review was performed by a separate AI agent from the agents
developing the transport, scale, and schedule notes. It is a mathematical
review of the stated deductions, not an independent certification of the
entire upstream result.

## Outcome

I found no invalid step in the targeted conditional derivations below.
The strongest combined conclusion is an **O(d^25) upper bound on the inverse
spectral gap of the ideal small-state chain**, conditional on the upstream
signature, recursion, and repair results and the reparameterized construction.
It is not an O(d^25) running-time theorem for the complete sampler.

| Claim reviewed | Assessment | Essential boundary |
|---|---|---|
| All-donor switching bound | Valid elementary double-counting argument | Uniform ordinary tables; no cell caps or structural zeros |
| Localized transport and global edge ownership | Valid conditional on the source current construction | Preserve literal leaf energies through the hard-weight limit |
| Path constant `U(U+1)/2` and root constant `floor((U+1)^2/4)` | Valid | Child support is an interval; local log-concavity alone is insufficient |
| Repair coefficient `(sqrt((1+p(p-1))*C_T)+1)^2` | Valid | Source repair injections and edge conductances are retained |
| `A=16d^2, B=16d^3, L=32d^3, U=128d^5` | Satisfies the identified analytic scale obligations | Integers `d>=14`; source definitions of `C` and `b` must follow the chosen scales |
| Bounded-paper localized trace and observable constants | Valid conditional on source lift and transport lemmas | Restricted observable and trace bounds do not imply a full enlarged-chain gap |
| Bernstein constant below `16` for the correction average | Valid | Independent ideal observations in `[1/8,4]` and `sigma<=1/200` |
| Exact-correction precision and finite-law arithmetic | Valid conditional identities | The complete actual output law and its rare-branch cost still need certification |

The detailed derivations are in [transport-localization.md](transport-localization.md),
[scale-audit.md](scale-audit.md), and [error-budgets.md](error-budgets.md).
The original manuscript's explicit inverse-gap estimate is `O(d^126)`;
its simpler displayed allowance is `d^160`. Localization alone gives
`O(d^85)` at the original `U=d^20`. Combining localization with the revised
scales gives the conditional `O(d^25)` estimate.

## 1. Switching: proof and a sharp domain restriction

Let `Omega` be all nonnegative integer tables with fixed ordinary margins.
At a marked cell `(i,j)`, assume its incident margins are at least the
integer `a`, and let `1<=t<=a`. For a bad table with `h=X_ij<t`, put
`u_j'=X_(i,j')` and `v_i'=X_(i',j)` for the other row and column entries.
For every donor pair and every integer
`1<=q<=min(u_j',v_i')`, perform the four-cell move

$$
X_{ij}\mathrel{+}=q,\quad X_{i'j'}\mathrel{+}=q,\quad
X_{ij'}\mathrel{-}=q,\quad X_{i'j}\mathrel{-}=q.
$$

All resulting tables belong to `Omega`. For nonnegative numbers,

$$
\sum_{i',j'}\min(u_{j'},v_{i'})
\ge\min\left(\sum_{j'}u_{j'},\sum_{i'}v_{i'}\right).
$$

For completeness, first sum `min(u_j',v_i')` over `i'` to obtain at least
`min(u_j',sum(v))`; then sum over `j'` and apply the same inequality again.
Thus every bad table has at least `a-h>=a-t+1` labeled outgoing moves.
An output table together with `(i',j',h)` determines `q=Y_ij-h` and the
entire source table uniquely. Each output has at most
`t(m-1)(n-1)` incoming labels. Double counting gives

$$
\Pr\{X_{ij}<t\}\le
\frac{t(m-1)(n-1)}{a-t+1}.
$$

With a single row or column, the bad event is empty under `t<=a`, consistent
with the zero numerator. No minimum size assumption such as `a>=4d` is
needed by this proof.

Retaining the target value strengthens this bound. Put `e=(m-1)(n-1)` and
`F=|Omega|`. For a target `Y`, a reverse label must have
`0<=h<min(t,Y_ij)`, so the incoming degree is at most `e*min(t,Y_ij)`.
Counting the same switches in both directions gives

$$
\sum_{X:\,h<t}(a-h)
\le e\left[tF-\sum_{X:\,h<t}(t-h)\right].
$$

Every rearranged summand is at least `a-t+1+e`, yielding

$$
\Pr\{X_{ij}<t\}\le\frac{te}{a-t+1+e}.
$$

This refinement is valid and attains equality at `t=1` in the ordinary
equal-margin `2x2` fiber. The scale calculation uses the weaker version,
so the refinement requires no changes to that calculation.

This proof does **not** extend to a capped or masked fiber merely because
its margins are large. For example, with both row and column margins
`(a,a)` and the cap `X_11=0`, the unique table is
`[[0,a],[a,0]]`. For `a>1,t=1`, its bad-event probability is one, while the
ordinary-table expression is `1/a`. The attempted switching would increase
the forbidden cell. Nonuniform weighting also invalidates the unweighted
double count unless a separate weight comparison is supplied.

## 2. Transport: why the repeated charges can be removed

The important new assertion is global ownership, beyond the source's
disjointness among leaves of a single transport problem. For integer leaf
endpoints `X=D-e_i` and `Y=D-e_j`, with `i!=j`, the coordinatewise maximum
of the endpoints is exactly `D`. That display has one slot with occupancy
`U+1`; this determines the special slot. Its first coordinate determines
the adjacent-child level, and the preceding balanced slots determine the
row-major context. Therefore one unordered physical edge cannot be charged
to different contexts, depths, or adjacent-child contrasts.

The current's support must remain inside the leaf cliques throughout the
proof. Replacing that support by the entire conditional graph before
summing would discard the information needed for the improvement. The
localized note instead passes to hard weights on a fixed finite family of
combinatorial leaf edges. With a fixed finite extension of the observable,
zero-weight endpoint terms vanish and positive child denominators remain
continuous. No convergence of the currents themselves is assumed.

The path argument is also valid. If `z_j<z_(j+1)`, log-concavity on a positive
interval implies `z_r<=z_j` for every earlier `r`; the symmetric statement
holds on the later side when `z_j>=z_(j+1)`. Applying this fact to the exact
telescoping cut coefficient gives `M(M+1)/2` for support diameter `M`.
It is essential to retain the interval-support hypothesis: `(1,0,0,1)`
satisfies all local log-concavity inequalities but has zero adjacent-edge
energy and can have positive variance.

The integer maximum of `v(U+1-v)` is `floor((U+1)^2/4)`. Substituting it in
the source root-potential calculation changes only that auxiliary-defect
term. The repair refinement then follows from the triangle inequality in
the weighted Euclidean norm. Distinct defects have distinct repair edges,
and each transversal has at most `p(p-1)` defect preimages. This comparison
does not require repair edges to be disjoint from transport edges.

The source integer signature and pair-summation derivations assume all slot
capacities are at least two. Both the published and proposed scales satisfy
this. During review, the arithmetic helper was tightened to require `U>=2`
so it does not silently suggest a theorem at width one. Ownership itself
works more generally, but that does not remove the source signature
hypothesis. Likewise, arbitrary fixed orders preserve ownership, whereas
the available physical repair proof still requires row-major order.

For the bounded paper, union of two leaf endpoints recovers a display with
one full pair. Following the deterministic adaptive exposure tree using
that display recovers one unique stopping node. The comparison factors
then give `C_p=1+8(p-1)q^2`. The source defect-mean construction has exactly
`p-2` ordinary slots, giving `C_d=8+32(p-2)q^3` for `p>=2`.
Centering the event indicator improves the selected conditional-mean bound
to `3 Var_mu(g)`. Keeping the total defect mass through normalization gives

$$
K_{\rm obs}=2p^2[(1+24p(p-1))C_p+8p(p-1)C_d].
$$

These bounds control the same projection and transversal trace as the
source. They do not establish mixing of arbitrary within-defect-type
observables.

## 3. Scales: independent edge-case and arithmetic checks

The completion-adjustment matrix can be checked by symbolic edge families,
without inferring a universal claim from small examples:

* An `x`-to-`x` exchange changes at most two row residuals by opposite unit
  amounts; the adjustment lies in the reference column.
* A `y`-to-`y` exchange gives the analogous reference-row adjustment.
* An `x`-to-`y` exchange changes one row and one column residual by `+1`.
  Its adjustment is
  `e_(i,j0)+e_(i0,j)-e_(i0,j0)`; coincidences coalesce to a single entry.
* Reversing the preceding exchange reverses the signs. A small-receiver
  repair has zero adjustment, and a large-receiver repair has the same
  row/column unit-increment form.

Feasibility excludes a nonzero residual change on a line outside the
completion rectangle. Thus every relevant adjustment has entries in
`{-1,0,1}`, at most three nonzero sites, and at most two negative sites in
either direction. The all-donor bound at `t=1` yields rejection probability
at most `2d/L`, since `(a_block-1)(c_block-1)<d`. For one-row or one-column
completion blocks this rejection event is empty.

I checked the scale-dependent occurrences in the source dense-bin argument.
The following conditions suffice for its displayed acceptance and
conductance comparisons:

$$
L\ge2B,\quad B\ge8d^3,\quad Ad\le B,\quad
2d^2/A+2d^3/B\le1/4.
$$

At `Ad/B=1`, the factor-four density comparisons still hold, including the
cut-face neighborhood bound: its radius is `1/(4d)` and the relevant
exponent is at most `1+1/(4d)<2`. The inner-volume loss is `4d^3/B=1/4` for
the proposed scales. The layer exponent sum is exactly `1/4`.

Unpadding uses an ordinary enlarged full table, so the improved switching
lemma applies there. A union bound gives

$$
\Pr\{\text{some large entry}<L\}
\le\frac{Ld^2}{U-L+1}\le\frac12.
$$

The proposed scales satisfy these inequalities for every integer `d>=14`,
as well as `U>=2L` and `2d/L<=1/2`. The positive-coefficient polynomial
certificates provide a universal check of these arithmetic implications;
they are not a substitute for establishing that the list of analytic
obligations is sufficient. That sufficiency is the source-level part of
the review above.

Combining `C_T=O(p U^4)`, at most `p(p-1)` repair preimages, and the unchanged
transition comparison `128d^2` gives `K=O(d^5 U^4)`. With `U=128d^5`, this
is `O(d^25)`. A complete algorithm additionally pays for mixing accuracy,
trials, dense completion calls, arithmetic, and exact correction.

## 4. Error schedules and exactness boundaries

For an ideal observation `X` in `[a,b]` with mean `mu`,
`Var(X)<=(b-mu)(mu-a)` and hence

$$
\frac{\operatorname{Var}(X)}{\mu^2}
\le\frac{(b-a)^2}{4ab}.
$$

For `[a,b]=[1/8,4]`, the bound is `961/128`. The two-sided Bernstein
denominator for relative error `sigma` is therefore at most

$$
961/64+(62/3)\sigma<16\qquad(0<\sigma\le1/200).
$$

For the ratio observations in `[1/2,1]`, the corresponding denominator is
`1/4+(2/3)sigma`. Giving those averages smaller budgets is valid. There are
at most `H` ratio averages and one correction average; only correction
observations need within-bin offsets. The reviewed draw budget
`H*N_ratio+(d+1)*N_correction` therefore covers all bin draws and scalar
offsets. The dyadic tail allocation controls all independent ideal
averages by a union bound, then separately couples their approximate draws
and applies the source's deterministic correction-rounding allowance.

This is an independent-sample statement. Applying the same Bernstein bound
directly to consecutive states of the outer chain would be unjustified.
The bounded paper's outer trajectory continues to use its restricted
observable argument.

The logarithmic mixing schedules follow from
`TV <= (1/2)*sqrt(pi_min^(-1)-1)*exp(-t/K)` for a finite lazy reversible
chain, with a proved bound `K` on its inverse gap. Supplying a numeric `K`
to the helper does not prove that it belongs to a particular chain.
The common dyadic-denominator allowance is consistent with the fact that
adjacent dense-bin exponents differ by at most one when `Ad/B<=1`.
Computing an allowance does not compute the corresponding probability law.

For exact correction with target size `M` and rare-branch probability
`delta=2^(-D)`, an additive TV guarantee `eta` suffices for pointwise
domination when

$$
\eta\le\frac{\delta}{M(1-\delta)}.
$$

The integer condition `M_bound*(2^D-1)<=2^k` is therefore sufficient when
`eta=2^(-k)` and `M_bound>=M`. It is a sharp sufficient threshold from this
TV information, not a necessary condition for every individual law.
Separately, a certified rare-branch cost
`2^(a*d*b)*poly(d,b,k)` is canceled in expectation by `D=a*d*b+s`, `s>=0`.
The published value `a=500` belongs to the original implemented sampler;
the changed sampler still needs an adapted law-tabulation and cost proof.

The residual law must be computed on the **complete feasible target fiber**.
Feasible tables with zero probability under the approximate sampler must
appear with zero numerators. Restricting the list to positive-probability
outcomes changes the target. The helper's documentation was corrected
during this review to state this explicitly.

## 5. Checks performed and remaining proof work

The general assessments above come from the displayed arguments and review
of the pinned source, not from test passage. I separately reran all 36
targeted tests: 11 transport tests, 9 scale tests, and 16 budget tests.
They passed. These checks cover exact arithmetic, finite ownership and
switching instances, deliberate counterexamples outside the hypotheses,
and finite dyadic-law identities. They do not establish general theorems
by enumeration.

The remaining obligations before an end-to-end strengthened theorem are:

1. Transfer the localized root statement through the physical prefix
   embedding, hard-weight limit, global exposure decomposition, and repair
   comparison in Lean.
2. Formalize the all-donor switching count, edge-adjustment cases, and the
   complete reparameterized scale chain.
3. Connect the revised error schedules to a concrete finite-bit sampler,
   propagate its actual law, and prove its revised rare-branch cost.
4. Run the applicable complete verification path and audit its dependencies;
   a focused local compilation does not certify the modified exported
   sampler/counting statements.

[formal-verification.md](formal-verification.md) records compiler and axiom
audit outcomes as they become available. This review does not upgrade a
pending build, local theorem, or finite test into a complete Comparator
result. The claims above also do not supply missing connectivity, mixing,
or inferential guarantees for a new weighted or masked commuting/employment model.

## Pinned source sections inspected

* [Sampling graph, repair, small entries and unpadding](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/model-and-graph.tex)
* [Sampling signatures and pair summation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/signatures.tex)
* [Sampling transport and variance](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/transport.tex)
* [Dense completion geometry, conductance and implementation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/dense.tex)
* [Sampling transitions, coupling and law tabulation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/algorithms.tex)
* [Bounded-paper transport, observables and trace](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/transport.tex)
* [Bounded-paper independent inner averages and finite-bit evaluation](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/evaluation.tex)
