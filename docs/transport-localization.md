# Localized transport bounds for OpenAI result 115

Research note, 8 October 2026. Source snapshot:
`openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

The initial review proposed removing repeated energy charges from the
sampling and bounded-counting arguments. This note gives the missing global
ownership proof, a stronger path constant, a sharper root-potential constant,
and improved repair and observable comparisons. These are mathematical
derivations **conditional on the stated lemmas in the pinned papers**. Finite
tests accompany the arguments. The full strengthened result has not been
verified in Lean or through the upstream Comparator. Any narrower formal
verification is reported separately in the project's verification record.

Let `p` denote the number of small slots in the sampling paper, and the number
of binary pairs in the bounded paper. These are different constructions.
All graph energies below sum **unordered edges once**. Parallel descriptions
of the same physical edge do not produce multiple conductances.

## 1. Results and prerequisites

For the sampling paper, retain its graph, weights, padding and transition
rule. Write

$$
 T_U=\frac{U(U+1)}2,\qquad Q_U=\left\lfloor\frac{(U+1)^2}4\right\rfloor,
 \qquad C_T=T_U\bigl[2+2(p-1)Q_U\bigr],\quad p\ge1.
$$

Then the paper's signature, transport-recursion and repair lemmas imply

$$
 Z_0\operatorname{Var}_{\mathcal T}H\le C_T E(H),
 \tag{1}
$$

and the full-graph comparison can be sharpened to

$$
 \Lambda\operatorname{Var}_{f/\Lambda}H
 \le\left(\sqrt{[1+p(p-1)]C_T}+1\right)^2E(H).
 \tag{2}
$$

Using the **unchanged** transition comparison in the sampling paper,

$$
 K_{\rm loc}=128d^2\left(\sqrt{[1+p(p-1)]C_T}+1\right)^2
 \tag{3}
$$

is an inverse-gap upper bound for its ideal small-state chain. Since `p<d`,
this is `O(d^5 U^4)`, hence **O(d^85)** at the published `U=d^20`, versus the
paper's explicit `O(d^126)` bound. This is an improvement of a proved
upper-bound analysis, not an assertion that the true chain has either
scaling, and not a complete-algorithm bit-complexity exponent. The case `p=0`
is the singleton graph and does not need a gap estimate.

For the bounded paper, the corresponding result is

$$
 C\operatorname{Var}_\mu g\le C_p^*\mathfrak D(g),\qquad
 C_p^*=1+8(p-1)q^2,
 \tag{4}
$$

replacing `p(1+8pq^2)`. Consequently the transversal trace has inverse gap at
most `2p^2 C_p^*`, rather than `2p^3(1+8pq^2)`. This does not assert a full
enlarged-chain spectral gap. Section 7 gives strengthened restricted
observable constants without changing that distinction.

The source obligations being reused are specific (including its integer
transport's ordinary-slot widths at least two, satisfied by the paper's
published scales):

* The sampling child masses have interval support and are log-concave.
* Its recursive signed demands have the stated divergences, potential
  increment and future-form monotonicity; each leaf is routed inside its
  one-removal clique.
* Its repair preserves the required row-major prefix and injects each
  auxiliary defect fiber into one adjacent child; global repair is injective
  within each ordered defect type and does not decrease weight.
* In the bounded paper, the two factorial lifts supply their respective
  omission/addition properties, the lift comparison holds on the stated
  domains, and multipliers are good.

No claim here independently certifies the upstream proofs of these inputs.

## 2. A sharper log-concave path inequality

Let `z_a,...,z_b` be positive and log-concave, let `M=b-a`, and put
`Z=sum(z)`. Zero weights outside this interval are allowed. For arbitrary
real `h_j`,

$$
 Z\operatorname{Var}_{z/Z}(h)
 \le \frac{M(M+1)}2\sum_{j=a}^{b-1}
       \min(z_j,z_{j+1})(h_j-h_{j+1})^2.
 \tag{5}
$$

**Proof.** Expand variance into unordered pairs and telescope each
`h_r-h_s`. Cauchy--Schwarz gives

$$
 Z\operatorname{Var}(h)
 =\frac1Z\sum_{r<s}z_rz_s(h_r-h_s)^2
 \le\sum_{j=a}^{b-1}B_j(h_j-h_{j+1})^2,
$$

where

$$
 B_j=\frac1Z\sum_{a\le r\le j<s\le b}z_rz_s(s-r).
 \tag{6}
$$

If `z_j<z_{j+1}`, log-concavity makes successive positive ratios
nonincreasing, so all `z_r<=z_j` for `r<=j`. Since `s-r<=b-r` and the
right-hand mass is at most `Z`,

$$
 B_j\le\sum_{r=a}^jz_r(b-r)
 \le z_j\sum_{r=a}^{b-1}(b-r)
 =z_j M(M+1)/2.
$$

If `z_j>=z_{j+1}`, the symmetric argument gives `z_s<=z_{j+1}` for
`s>=j+1` and

$$
 B_j\le\sum_{s=j+1}^bz_s(s-a)
 \le z_{j+1}M(M+1)/2.
$$

At equality, the latter argument remains valid. These two estimates prove
(5). A single-point support has zero variance. No undefined mean at a
zero-mass child is needed. □

This halves the initial review's `U(U+1)` constant. It is not claimed to be
the optimal log-concave Poincare constant. The exact coefficients (6) can be
substantially smaller. They are calculated with rational arithmetic by
`path_cut_coefficients`; the calculation itself requires no log-concavity.

The quadratic order cannot be removed from a universal result of this
form: for uniform weights on `0,...,M` and `h_j=j`, the ratio of variance
to adjacent-edge energy is `(M+1)(M+2)/12`. A one-edge example with masses
`(1,R)` has ratio `R/(1+R)`, showing that the value `1` at `M=1` is necessary
as a supremum.

**Why the support assumption matters.** Local inequalities
`z_j^2>=z_{j-1}z_{j+1}` alone do not exclude a long zero gap: `(1,0,0,1)`
passes those local inequalities, but the right side of (5) is zero for all
`h` while the variance need not vanish. The source's interval-support
conclusion is essential and is checked separately in the implementation.

## 3. A localized and sharper adjacent-child transport

Fix a row-major context `sigma`, its next slot `s`, and adjacent positive
children `ell-1,ell` with masses `z_-,z_+`. Form every complete leaf display
`D` in the source recursion: its special slot is
`(ell,U+1-ell)`; every other slot is balanced; the prefix is fixed. In a
leaf, remove one unit at each allowed, unfixed coordinate to obtain its
valid one-hole vertices. Let `L_(sigma,s,ell)` be the union of the edges of
these cliques and define

$$
 E_{\sigma,s,\ell}(H)=
 \sum_{\{X,Y\}\in L_{\sigma,s,\ell}}
 \min(f(X),f(Y))(H(X)-H(Y))^2.
 \tag{7}
$$

This is the full clique energy, even though the source current may use only
hub edges inside each clique. Bounding the current pairing by the full
clique energy is valid.

The source root-potential estimate uses a multiplier `v(U+1-v)` for each
ordinary-slot profile. For integer `v`,

$$
 v(U+1-v)\le Q_U.
 \tag{8}
$$

The integer maximum follows by completing the square; the continuous
version `(U+1)^2/4` is also valid. Repeating the source potential calculation
with this bound, and applying Cauchy--Schwarz only on the current's actual
support, gives the stronger raw inequality

$$
 (H_--H_+)^2\le
 \left(\frac1{z_-}+\frac1{z_+}
       +\frac{2Q_U\sum_{t>s}c_{st,\ell}^\sigma}{z_-z_+}\right)
 E_{\sigma,s,\ell}(H).
 \tag{9}
$$

In particular, if `r_sigma` ordinary small slots remain after `s`, the
source conditional repair injection gives

$$
 \min(z_-,z_+)(H_--H_+)^2
 \le [2+2r_\sigma Q_U] E_{\sigma,s,\ell}(H).
 \tag{10}
$$

Here each `c_(st,ell)^sigma<=max(z_-,z_+)`. The factor `r_sigma` counts
actual remaining slots, and is at most `p-1`. Conditional repairs actually
land in a specified child; retaining that distinction and the individual
auxiliary masses can improve (9) further on a particular instance.

**Hard zeros.** First prove (9) at positive softened weights, on the fixed
finite family of box-admissible patterns. Extend `H` arbitrarily but with
fixed finite values to patterns whose hard weight is zero. The leaf edge
sets are combinatorial and do not depend on the softening parameter. Every
term `min(f_eta(X),f_eta(Y))*Delta(H)^2` therefore converges to its hard
counterpart. Edges with a zero-weight endpoint vanish; no division by that
weight survives in (9). Positive limiting child masses make its two
remaining denominators continuous. Thus the inequality passes to the hard
limit without requiring convergence of currents or recursive coefficients.

**Lean alignment.** The upstream `IntegerLeafEnergy.lean` already proves
`recursiveEnergy_eq_leafEnergySum`, `leafEnergySum_eq_edges`, and
`max_removeOne`. In that code, `leafEdges` contains both orientations and
the sum is divided by two, agreeing exactly with (7). The final relaxation
to `integerGraphEnergy` in `integer_root_graph_transport` is unnecessary
for the localized version. The new work is retaining that energy across
the physical prefix embedding and hard limit, sharpening (8), and charging
different roots globally.

## 4. Global ownership of integer leaf edges

**Lemma.** Every unordered physical edge belongs to at most one set
`L_(sigma,s,ell)`.

**Proof.** Suppose the edge has distinct endpoints
`X=D-e_i`, `Y=D-e_j`, where `i!=j` and both removals are valid. For each
coordinate `k`, at least one endpoint still has value `D_k`, and neither
exceeds it. Consequently

$$
 D=\max(X,Y)\quad\text{coordinatewise}.
 \tag{11}
$$

Thus the *unordered* edge determines its entire display, independently of
its orientation or which endpoint is called `X`. The unique slot in `D`
with occupancy `U+1` determines `s`; all other slots have occupancy `U`.
Its first coordinate determines `ell`. The balanced profiles of the slots
before `s` determine `sigma`. Therefore two purported owners have identical
`s`, `ell` and `sigma`. All later balanced profiles also agree, so the edge
belongs to only one complete leaf display. □

The proof holds for heterogeneous widths `U_t`, replacing occupancies by
`U_t` and `U_t+1`, and for any fixed exposure order. The conditional repair
estimate used in (10) still specifically requires the source's row-major
order; combinatorial ownership alone does not authorize changing it.

The requirement that **both holes lie outside the fixed prefix** is part of
the definition. An arbitrary exchange edge can have the occupancy pattern
in (11) yet fail this requirement. The implementation rejects it rather
than silently counting it as a transport edge. Removing zero-weight states
cannot create a second owner.

Apply (5) at each positive context, with its actual support diameter, and
then (10). The conditional variance identity over the entire exposure tree
has no normalization factor left: each node contributes its own mass times
its between-child variance. Global ownership gives

$$
 \sum_{\sigma,s,\ell}E_{\sigma,s,\ell}(H)\le E(H).
$$

Using the worst values `M<=U` and `r_sigma<=p-1` proves (1). In particular,
neither the number of adjacent contrasts nor the number of tree depths is
charged a second time.

A sharper instance certificate retains

$$
 C_T^{\rm instance}=\max_{\sigma,\ell} B_{\sigma,\ell-1}
 \left(\frac1{z_-}+\frac1{z_+}
 +\frac{2Q_U\sum_{t>s}c_{st,\ell}^\sigma}{z_-z_+}\right).
 \tag{12}
$$

With these exact masses, `Z_0 Var_T(H)<=C_T^instance E(H)`. This is a
diagnostic certificate, not an efficiently available counting oracle.

## 5. A sharper repair comparison

This improvement is independent of the transport construction. Suppose a
weighted graph has a transversal subset, a repair map `R` from every other
vertex into that subset, and these properties:

* `f(X)<=f(R(X))`;
* every transversal has at most `N` defect preimages;
* distinct defects have distinct repair edges.

Extend `R` by the identity on transversals. If `m` is the weighted
transversal mean, then

$$
 \sum_Xf(X)(H(R(X))-m)^2
 \le(1+N)Z_0\operatorname{Var}_{\mathcal T}H.
$$

Also `sum_X f(X)(H(X)-H(R(X)))^2` is exactly the repair-edge energy
`E_R(H)`, because each such edge has minimum endpoint weight `f(X)`.
The triangle inequality in the weighted Euclidean norm gives

$$
 \sqrt{\Lambda\operatorname{Var}_{f/\Lambda}H}
 \le\sqrt{(1+N)Z_0\operatorname{Var}_{\mathcal T}H}
       +\sqrt{E_R(H)}.
 \tag{13}
$$

Insert (1), use `E_R<=E`, and set `N=p(p-1)` to obtain (2). The source
repair lemma supplies these assumptions, since it is injective within each
ordered distinct defect type. No disjointness between repair edges and
transport edges is assumed: some may coincide in the physical graph.

An integer upper bound for (2) is `A+2*ceil(sqrt(A))+1`, where
`A=(1+p(p-1))*C_T`. The implementation uses integer square roots, avoiding
floating-point underestimation for the enormous published scales.

## 6. Adaptive ownership in the bounded paper

At a node `sigma` of the bounded paper's deterministic adaptive exposure
tree, let `k` be its chosen pair. Every leaf display in its one-hole
transport consists of both elements of pair `k` and exactly one element of
every other pair, with all fixed choices respected. Any edge has endpoints
`S=D\{i}` and `S'=D\{j}`, for distinct unfixed elements, so

$$
 D=S\cup S'.
$$

The edge therefore determines its unique full pair `k` and the singleton
choices in all other pairs. Follow the adaptive exposure tree from the
root: whenever its next chosen pair differs from `k`, take the unique
branch specified by the singleton in `D`; stop when the chosen pair is
`k`. This procedure is deterministic. Every possible owner of the edge
must be exactly that stopping node. In particular, the proof works even
when different histories choose different pair orders. A tie-breaking rule
for sink selection is enough to make the paper's tree deterministic.

The source current stays inside these leaf cliques. Preserve their energy
in its one-hole inequality, multiply by `s_0 s_1/z_sigma`, and apply the
source sink comparison to each of the at most `p-1` remaining pairs. The
local coefficient is at most `1+8(p-1)q^2`. The global ownership proof and
conditional variance decomposition give (4). The source trace Dirichlet
identity then gives the stated `2p^2 C_p^*` inverse-gap bound, with no
additional mixing or return-time assumption.

## 7. Bounded-paper observable constants

These refinements preserve the source's restricted projection `Q`, which
keeps individual transversal values and pools each defect type to its mean.
They do not control all within-type fluctuations.

For `p>=2`, the source defect-mean transport has **p-2** ordinary slots, so
its proof directly yields

$$
 C_d^*=8+32(p-2)q^3
$$

in the bound `|gbar_(il)-gbar'|^2<=C_d^* D(g)/C`. The selected joint-choice
event has probability `rho>=1/4`. Centered-indicator Cauchy--Schwarz gives

$$
 |\mathbb E[g\mid A]-\mathbb E[g]|^2
 \le\frac{1-\rho}{\rho}\operatorname{Var}_\mu g
 \le3\operatorname{Var}_\mu g,
 \tag{14}
$$

which improves the source's factor four. Indeed the covariance of `g` and
`1_A` equals `rho*(E[g|A]-E[g])`, and `Var(1_A)=rho(1-rho)`.

Put `V=Var_mu(g)` and `e=D(g)/C`. For each defect type,

$$
 |\bar g_{il}-\mathbb E_\mu g|
 \le\sqrt{C_d^*e}+\sqrt{3V}.
$$

Thus a convenient coefficient is

$$
 \operatorname{Var}_\pi(Qg)
 \le\bigl(\sqrt{3C_p^*}+\sqrt{C_d^*}\bigr)^2\frac{\mathfrak D(g)}C,
 \tag{15}
$$

and a rational, slightly larger coefficient is `6C_p^*+2C_d^*`.
For (15), the transversal contribution is `pi(A)*V` and the defect
contribution is at most `pi(D)*(sqrt(C_d^*e)+sqrt(3V))^2`; after inserting
`V<=C_p^*e`, the latter coefficient dominates the former.

Retaining total type mass gives a better rational normalized bound. Write
`N=p(p-1)`, so `(Lambda-C)/C<=4N` under good multipliers. Using
`|gbar_(il)-m|^2<=2C_d^*e+6V` and the source identity
`D(g)=2p^2 Lambda E(g)` gives

$$
 \operatorname{Var}_\pi(Qg)\le K_{\rm obs}^*\mathcal E(g),\qquad
 K_{\rm obs}^*=2p^2\left[(1+24N)C_p^*+8N C_d^*\right].
 \tag{16}
$$

For `p=1`, there are no defect types, `Q=I`, `C_p^*=1`, and one may set
`C_d^*=0`; formula (16) gives `K_obs^*=2`. The source dominated-start
trajectory-average proof uses only the restricted observable inequality,
so its `2 U K_obs Var(G)/n` bound remains valid with (16). The constant
remains a proof bound, not an empirical autocorrelation estimate.

## 8. Verification and limits

`tests/test_transport_bounds.py` checks exact rational cut coefficients,
both hard-zero negative controls, complete integer leaf-edge ownership
with multiple capacities and orders, adaptive binary ownership, covariance
centering, and the arithmetic of the new constants. It deliberately tests
the observable statements rather than claiming full-chain mixing.

These finite tests can detect an incorrect implementation or counterexample
inside the tested ranges; the arguments above establish the general claims
conditional on the upstream lemmas. There is no new universal optimality
claim, no full FPRAS runtime exponent, and no formalized end-to-end
replacement theorem in this note.

The heterogeneous-width ownership lemma is available independently, but
using heterogeneous capacities in the physical sampler also requires
rechecking its state definition, signature slices, repair injection,
completion construction and scale bounds. This note does not infer those
results from the ownership lemma alone.

### Pinned primary sources

* [Sampling transport](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/transport.tex): child support, recursion, current support, root estimate and full variance.
* [Sampling graph and repair](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/model-and-graph.tex): physical states, weight comparison, prefix preservation and repair multiplicity.
* [Sampling transition comparison](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/algorithms.tex): the factor `128d^2` retained in (3).
* [Bounded transport and observables](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/transport.tex): separate lifts, sink comparison, defect transport and trace normalization.
* [Existing literal leaf energies](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Transport/IntegerLeafEnergy.lean).
* [Existing integer root transport](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Transport/IntegerRootTransport.lean).
