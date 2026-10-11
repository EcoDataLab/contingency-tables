# Accelerating the all-small chain by eliminating repair stars

For positive ordinary margins with every row and column below the cutoff, a changed chain can remove one dimension factor from the existing inverse-gap allowance. Eliminate the balanced vertices exactly, then sample the resulting repair-fiber refresh directly. The resulting **defect-only chain** has the mathematical allowances

\[
 K_{\rm rational}\le2500d^{16},\qquad
 K_{\rm dyadic}\le5000d^{16},\qquad
 d=10+(m+1)(n+1),\quad U=5d^3.
\]

**Evidence:** mathematical derivation with independent AI-agent review and exact finite checks. The [generic star-elimination/Poincare transfer](../research/repair-accept/) and actual defect-fiber count have compiled Lean proofs. The numerical physical-chain bound is not yet a Lean theorem, and this chain is not installed in the compiled sampler. The existing selected/reference `80000d^17` theorem remains unchanged. The numerical complete machine-time exponent remains unknown.

## Scope and the existing graph

Assume `m,n>=2`, positive integer row and column margins, equal total `M`, and **every margin strictly below U**. There are no extra cell bounds, structural zeros, or weights. Put `p=mn`. The physical state is a pair of nonnegative views `(x,q)` with prescribed row sums of `x`, prescribed column sums of `q`, and either `x=q` or

\[
q-x=e_s-e_t,\qquad s\ne t.
\]

All physical weights are one. Balanced states are ordinary tables; write their set as `B` and the defect set as `D`. The designated repair of a defect is

\[
 R(x,q)=x-e_t+e_v,\qquad
 v=(\operatorname{row}(t),\operatorname{column}(s)).
\]

The existing graph has no balanced-to-balanced edges, and **each defect has exactly one balanced neighbor, its designated repair**. For an ordinary table `A`, the exact number of incoming defects is

\[
 k_A=|R^{-1}(A)|=(p-1)|\operatorname{supp}(A)|.
\]

The [defect-transport analysis](defect-transport-research.md) proves these actual graph facts. The [repair-output derivation](repair-output.md) gives the inverse-fiber formula and explains why positive entries, including coincident crossing cells, are counted exactly.

Every defect-to-defect exchange belongs to one of four families:

1. Move one unit of `x` out of `t` to another cell in its row.
2. Move one unit of `x` into `s` from another cell in its row.
3. Move one unit of `q` out of `s` to another cell in its column.
4. Move one unit of `q` into `t` from another cell in its column.

Other same-view exchanges do not cancel either of the two existing defect labels and therefore leave the one-defect state space. Same-view moves must preserve the fixed row or column sums. Mixed moves in the source's doubled coordinates change the fixed total of `x`, so cannot be feasible. Two family descriptions coincide only when their target is balanced; that target is omitted here. Consequently

\[
 \deg_{DD}(z)\le2(n-1)+2(m-1).
\]

## The changed transition

Let `h=2(m+n-2)+1` and `beta'=1/(2h)`. For distinct defects define

\[
 P'(z,w)=\beta'\left[
  \mathbf1_{\{z,w\}\in E_{DD}}+
  {\mathbf1_{R(z)=R(w)}\over k_{R(z)}}\right],
\]

and set the diagonal to make each row sum one. The kernel is symmetric and has the uniform law on `D` as its stationary law. Its entire move-attempt mass is at most `beta' h=1/2`, so it is half-lazy.

To implement one transition, hold with probability one half; otherwise choose uniformly among `h` channels. The first `h-1` channels are the four families above, indexed by their candidate cells. Invalid candidates and balanced targets hold. The last channel repairs to `A` and draws a fresh defect uniformly from `R^-1(A)`.

That refresh needs no ordinary table count or search. Choose a positive receiver cell `v` uniformly from the support of `A`, then choose uniformly among the `p-1` ordered pairs `(s,t)` crossing at `v` with `s!=t`. Reconstruct

\[
 x=A+e_t-e_v,\qquad q=A+e_s-e_v.
\]

The [exact inverse-fiber count](repair-output.md) makes this uniform on the repair fiber. Repair, support scanning and reconstruction require `O(p)` elementary operations. This is a direct transition, rather than an excursion simulated through balanced vertices.

The dyadic version uses

\[
 \beta_{\rm dy}=2^{-\lceil\log_2(2h)\rceil},\qquad
 \beta_{\rm dy}^{-1}\le4h.
\]

Draw `ceil(log2(2h))` fair bits, assign `h` labels to the channels, and assign every remaining label to holding. This channel selection is bounded. Conditional uniform support and label draws still need a finite-word implementation: rejection-based integer draws can have unbounded retries, so capped versions must include their failure and law-error budgets.

## Why the inverse gap improves

Use the source's **unnormalized** variance and energy:

\[
 V_X(H)=\min_a\sum_{z\in X}(H(z)-a)^2,
 \qquad E(H)=\sum_{\{z,w\}\in E}(H(z)-H(w))^2.
\]

The source energy is half the sum over both orientations, hence one copy per undirected edge. The existing [full physical variance theorem](../formal/Math115/PhysicalRepairRefinement.lean) proves

\[
 V_{B\cup D}(G)\le C E(G),\qquad C\le d^3U^4.
\]

For an arbitrary observable `H` on defects, extend it to each balanced table by the mean over its repair fiber:

\[
 \overline H(A)={1\over k_A}\sum_{z:R(z)=A}H(z).
\]

Variance restriction gives `V_D(H)<=V_(B union D)(Hbar)`: at the full minimizing center, the defect sum is at least its own minimum and the balanced sum is nonnegative. **No stationary-mass divisor is introduced.**

Each balanced vertex is an independent star. Its energy after this extension is exactly

\[
 \sum_{z:R(z)=A}(H(z)-\overline H(A))^2
 = {1\over2k_A}\sum_{z,w:R(z)=R(w)=A}(H(z)-H(w))^2.
\]

Therefore the full energy becomes the defect trace energy

\[
 E_{\rm tr}(H)=
 \sum_{\{z,w\}\in E_{DD}}(H(z)-H(w))^2+
 \sum_A{1\over2k_A}\sum_{z,w\in R^{-1}(A)}(H(z)-H(w))^2,
\]

and the retained physical theorem yields `V_D(H)<=C E_tr(H)`. The normalized variance of `P'` is `V_D/|D|`; its normalized Dirichlet energy is `beta' E_tr/|D|`. Thus

\[
 K'\le {C\over\beta'}=(4(m+n)-6)C
 \le4d^4U^4=2500d^{16}.
\]

Here `m+n<=mn=p<=d` for `m,n>=2`. The dyadic reciprocal is at most twice the rational reciprocal, giving `5000d^16`. Keeping `m+n` instead of replacing it by `d` gives a stronger shape-specific consequence:

| Shape | Rational inverse-gap allowance | Dyadic inverse-gap allowance |
|---|---:|---:|
| Any `m,n>=2` | `2500d^16` | `5000d^16` |
| Square, `m=n` | `5000d^(31/2)` | `10000d^(31/2)` |
| Bounded aspect ratio | `O(d^(31/2))` | `O(d^(31/2))` |

For square tables, `m+n=2m<=2sqrt(d)` and `C<=625d^15`, proving the displayed constant directly. Bounded-aspect constants depend on the fixed aspect bound. These are consequences of the same reviewed mathematical derivation, with the same outstanding physical Lean and implementation obligations. They do not give a uniform `d^(31/2)` bound for arbitrarily thin tables.

The ordinary trace of the original physical chain uses the original proposal `beta`, not `beta'`: its off-diagonal kernel is `beta [1_DD+1_samefiber/k_A]`. Skipping balanced residence retains that old trace normalization. The additional acceleration to `beta'` is a deliberate change of chain and is essential to the improvement.

For comparison, the original `d^17` allowance combines `d^2` from proposal normalization, `p^2` from repair load, `p` from localized exposure, and `U^4`. The [existing repair refinement](physical-repair-refinement.md) supplies the coefficient used here. Actual maximum-degree normalization alone cannot remove its quadratic order: fully positive balanced tables have `p(p-1)` repair neighbors.

## Uniform table output

Defect stationarity repairs to `A` with mass `k_A/|D|`. Let `b=max(m,n)`. Accept the repaired table with probability

\[
 {b\over|\operatorname{supp}(A)|}.
\]

Positive margins imply `b<=|supp(A)|<=min(p,M)`, so this is valid. Every table receives the same successful mass `(p-1)b/|D|`; accepted output is uniform. Its inverse-success allowance is at most `min(p,M)/b<=min(m,n)`. Draw uniformly from `0,...,|supp(A)|-1` and accept labels below `b`.

This rule uses the **defect-only** fiber count `k_A`. The earlier chain's count `1+k_A` would give the wrong correction here. An initial defect can be constructed from a supplied feasible table by choosing a positive receiver and crossing labels. Singleton dimensions can be returned directly.

Finite endpoint mixing, bounded retry accuracy, conditional draw errors and compiled program identification still need to be composed for this changed chain. The inverse-gap derivation alone does not supply exact finite-time uniformity or a complete machine-time exponent.

## Reproducible finite checks and remaining scope

The [experiment](../experiments/defect_trace.py) and [saved report](../reports/defect-trace.json) cover eight primary fixtures and four explicitly exploratory one-side-small fixtures. Primary fixtures are equal `2x2` margins `1,...,6`, a positive `2x3` fiber, and `3x3` permutation margins.

For each fixture, exact rational assertions verify the repair degree and unique balanced neighbor, defect-degree bound, equality of the four channel families with the backend's DD neighbors, stochasticity, half-laziness, uniform reversibility, output correction, and **every entry of the full Schur-complement matrix** `L_DD-L_DB L_BB^-1 L_BD`. The script also checks an exact observable's harmonic energy and variance restriction. Optional NumPy eigenvalues are labeled floating diagnostics. Source hashes accompany the report. Exhaustive enumeration is exponential and finite checks do not prove the general statement.

The backend uses the small diagnostic cutoff `U=max(margins)+1,L=1` on the primary fixtures. Increasing this cutoff above the margins changes only the complementary coordinates; the state set in `(x,q)` and the unit graph stay the same. This identifies those graphs with the all-small graphs at the ideal scales, rather than assuming arbitrary rescaling preserves a chain.

```sh
python3 experiments/defect_trace.py
python3 experiments/defect_trace.py --spectral --output reports/defect-trace.json
```

The default output is `.local/reports/defect-trace.json`; writing the public report requires an explicit destination. The four one-side-small cases test a possible extension and remain outside the primary reviewed claim.

Nonempty large blocks reintroduce varying completion masses, mixed exchanges and balanced-to-balanced edges. The low defect-degree argument and elementary unit-weight star elimination then need different proofs. The general selected/reference `d^17` certificate is unchanged.

A further width refinement is a research target. Reencoding each pair with capacity `min(r_i,c_j)+1` appears to preserve the all-small graph, and the [abstract width-weighted transport theorem](../formal/Math115/WidthWeightedTransport.lean) retains individual capacities. A general physical consequence still needs four bridges: variable word/context assembly, a truncated quadratic auxiliary kernel through the hard limit, weighted per-type repair-mass bounds, and owner recovery with variable capacities. Until those are proved, this route supplies no sharper uniform exponent than the `d^16` derivation above.
