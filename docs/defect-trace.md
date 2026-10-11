# Accelerating the unit chain by eliminating repair stars

For positive ordinary margins with either every row or every column below the cutoff, a changed chain can remove one dimension factor from the existing inverse-gap allowance. Eliminate the balanced vertices exactly, then sample the resulting repair-fiber refresh directly. The resulting **defect-only chain** has the mathematical allowances

\[
 K_{\rm rational}\le2500d^{16},\qquad
 K_{\rm dyadic}\le5000d^{16},\qquad
 d=10+(m+1)(n+1),\quad U=5d^3.
\]

**Evidence:** mathematical derivation with independent AI-agent review and exact finite checks. The [generic star-elimination/Poincare transfer](../research/repair-accept/) and actual both-small defect-fiber count have compiled Lean proofs. The numerical physical-chain bound is not yet a Lean theorem, and this chain is not installed in the compiled sampler. A [direct bounded finite-bit reference](direct-defect-sampler.md) now implements the one-side-small scope. The existing selected/reference `80000d^17` theorem remains unchanged.

When **both** sides are below the cutoff, the [variable-capacity refinement](rectangular-defect.md) gives `20000d^(31/2)` rational and `40000d^(31/2)` dyadic for every aspect ratio. The [weighted trace](general-defect-trace.md) separately addresses nonempty completion blocks.

## Scope and the existing graph

Assume `m,n>=2`, positive integer row and column margins, equal total `M`, and **either all row margins or all column margins strictly below U**. The completion rectangle is empty. Its residual total is zero on the empty side, forcing all residuals on the other side to zero as well. Thus both views have their prescribed margins, even when the opposite side has margins at or above `U`. There are no extra cell bounds, structural zeros, or weights. Put `p=mn`. The physical state is a pair of nonnegative views `(x,q)` with prescribed row sums of `x`, prescribed column sums of `q`, and either `x=q` or

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

Draw `ceil(log2(2h))` fair bits, assign `h` labels to the channels, and assign every remaining label to holding. The [direct implementation](direct-defect-sampler.md) uses fixed-bit support/label ranks, with an explicit transition-law discrepancy. It never retries an integer draw.

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

For square tables, `m+n=2m<=2sqrt(d)` and `C<=625d^15`, proving the displayed constant directly. Bounded-aspect constants depend on the fixed aspect bound. These shape-only consequences do not give a uniform `d^(31/2)` bound for arbitrarily thin tables. The newer [variable-capacity argument](rectangular-defect.md) supplies that exponent for all aspect ratios when both sides are small. Each applicable bound remains available: the new constant need not be best for every finite instance.

The ordinary trace of the original physical chain uses the original proposal `beta`, not `beta'`: its off-diagonal kernel is `beta [1_DD+1_samefiber/k_A]`. Skipping balanced residence retains that old trace normalization. The additional acceleration to `beta'` is a deliberate change of chain and is essential to the improvement.

For comparison, the original `d^17` allowance combines `d^2` from proposal normalization, `p^2` from repair load, `p` from localized exposure, and `U^4`. The [existing repair refinement](physical-repair-refinement.md) supplies the coefficient used here. Actual maximum-degree normalization alone cannot remove its quadratic order: fully positive balanced tables have `p(p-1)` repair neighbors.

## Uniform table output

Defect stationarity repairs to `A` with mass `k_A/|D|`. Let `b=max(m,n)`. Accept the repaired table with probability

\[
 {b\over|\operatorname{supp}(A)|}.
\]

Positive margins imply `b<=|supp(A)|<=min(p,M)`, so this is valid. Every table receives the same successful mass `(p-1)b/|D|`; accepted output is uniform. Its inverse-success allowance is at most `min(p,M)/b<=min(m,n)`. Draw uniformly from `0,...,|supp(A)|-1` and accept labels below `b`.

This rule uses the **defect-only** fiber count `k_A`. The earlier chain's count `1+k_A` would give the wrong correction here. An initial defect can be constructed from a supplied feasible table by choosing a positive receiver and crossing labels. Singleton dimensions can be returned directly.

The [direct reference](direct-defect-sampler.md) composes finite transition rounding, a supplied ideal endpoint-mixing bound, fixed-bit acceptance and bounded retries. The [both-small schedule](defect-sampler-composition.md) provides sufficient parameters and an integer-operation allowance. Physical Lean assembly and compiled program identification remain open. No complete bit-machine exponent follows from the inverse-gap bound alone.

## Reproducible finite checks and remaining scope

The [experiment](../experiments/defect_trace.py) and [saved report](../reports/defect-trace.json) cover eight primary fixtures and four explicitly exploratory one-side-small fixtures. Primary fixtures are equal `2x2` margins `1,...,6`, a positive `2x3` fiber, and `3x3` permutation margins.

For each fixture, exact rational assertions verify the repair degree and unique balanced neighbor, defect-degree bound, equality of the four channel families with the backend's DD neighbors, stochasticity, half-laziness, uniform reversibility, output correction, and **every entry of the full Schur-complement matrix** `L_DD-L_DB L_BB^-1 L_BD`. The script also checks an exact observable's harmonic energy and variance restriction. Optional NumPy eigenvalues are labeled floating diagnostics. Source hashes accompany the report. Exhaustive enumeration is exponential and finite checks do not prove the general statement.

The backend uses the small diagnostic cutoff `U=max(margins)+1,L=1` on the primary fixtures. Increasing this cutoff above the margins changes only the complementary coordinates; the state set in `(x,q)` and the unit graph stay the same. This identifies those graphs with the all-small graphs at the ideal scales, rather than assuming arbitrary rescaling preserves a chain.

```sh
python3 experiments/defect_trace.py
python3 experiments/defect_trace.py --spectral --output reports/defect-trace.json
```

The default output is `.local/reports/defect-trace.json`; writing the public report requires an explicit destination. That historical report labels its one-side-small fixtures exploratory. The newer geometry argument and [direct sampler tests](../tests/test_defect_chain.py) establish and exercise the extension, including capacity-equality entries at `U`.

Nonempty large blocks require the [weighted trace argument](general-defect-trace.md). They introduce varying completion masses, mixed exchanges and potentially two balanced neighbors per defect. **They do not introduce balanced-to-balanced edges**; the earlier concern about such edges was incorrect. Weighted harmonic elimination therefore still applies, with a different exit sampler and output analysis.

The [variable-capacity derivation](rectangular-defect.md) now supplies all four mathematical bridges for the sharper rectangular bound. Its quadratic hard-limit bridge compiles separately. The remaining formal work is assembling the changed physical word/context maps, variance decomposition and numerical bound into Lean.
