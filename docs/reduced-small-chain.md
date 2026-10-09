# An ideal completion chain at the reduced scales

Later results: the [automatic branch and equal-total wrapper](reduced-all-small-chain.md) discharge reference and nonemptiness assumptions, and the [physical repair refinement](physical-repair-refinement.md) improves the dense-compatible allowance to `128·47⁴d²⁵`. The original theorem described below remains valid.

**Verification status: verified.** `formal/Math115/ReducedSmallChain.lean` compiled with Lean 4.34.1, `-j1`, and `-DautoImplicit=false`, with no diagnostics. Nine principal exports, including both chain constructors and the final $d^{25}$ theorem, were axiom-audited; every audited declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. The full physical-variance and reduced-padding acceptance dependencies were also compiled and audited.

The module constructs an actual chain using the pinned source's `completionChain`, reference completion blocks, physical adjacency graph, dyadic proposal, and capacity formula. Its cutoff $U$ and padding $L$ are explicit parameters. It is not just a substitution in a scalar inequality.

Write $d=10+(|I|+1)(|J|+1)$ and let $p$ be the number of cells classified as small at cutoff $U$. The constructed chain has the source completion weights as its stationary law. For $U\ge2$ and $L\ge3d$, the theorem proves

$$
\operatorname{Var}_{\pi}H
\le \frac{2K_{p,U}}{\beta_d}\mathcal E(H)
\le 1024d^5U^4\mathcal E(H),
$$

where $K_{p,U}$ is the localized full physical-variance coefficient and $\beta_d$ is the unchanged source dyadic proposal probability.

The acceptance step uses the actual source translations between reference completion tables. The new small-entry and adjustment results give at least half acceptance when $L\ge3e$, with $e$ the product of the numbers of nonreference large rows and columns. The proof establishes $e\le d$, so $L\ge3d$ suffices. The source capacity formula bounds every residual table, and its physical capacity theorem identifies the ordinary reference blocks without a new capacity hypothesis.

The specialization $U=47d^5$, $L=32d^3$ therefore has the bound

$$
\operatorname{Var}_{\pi}H
\le1024\cdot47^4d^{25}\mathcal E(H).
$$

The exponent $25$ records these proposed sampler-compatible scales. The generic chain inequality holds for every $U\ge2$ and $L\ge3d$; it does not assert that $25$ is an optimal exponent for an ideal chain with an unrestricted completion oracle.

The theorem assumes a nonempty positive-weight state space and chosen large reference row and column. An all-small branch would use a separate unit chain. This module does not formalize the finite-bit dense completion oracle, the complete sampler at these scales, or its end-to-end runtime. The separate [original-chain result](small-chain-gap.md) concerns the unchanged source definition at $U=d^{20}$ and $L=d^{12}$.

Verified exports in namespace `Math115.ReducedSmallChain` include the actual `chain` and `reducedChain` constructions, their stationary identity `chain_pi`, the concrete `state_variance_localized` and `chain_energy_lower` bounds, `chain_poincare_exact`, `chain_poincare_polynomial`, and `reducedChain_poincare_d25`.

## Verification command

After the pinned dependency closure is built, the target is checked directly from `formal/` with:

```sh
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean -j1 \
  -DautoImplicit=false -R "$PWD" Math115/ReducedSmallChain.lean \
  -o .lake/build/lib/lean/Math115/ReducedSmallChain.olean
```

The separate `#print axioms` audit covered `chain`, `chain_pi`, `state_variance_localized`, `nonreference_product_le_allowance`, `chain_energy_lower`, `chain_poincare_exact`, `chain_poincare_polynomial`, `reducedChain`, and `reducedChain_poincare_d25`. The pinned source definitions were not edited.
