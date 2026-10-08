# Localized Poincare bound for the original ideal small chain

**Verification status: verified.** `formal/Math115/SmallChainGap.lean` and `formal/Math115/AllSmallChainGap.lean` compiled with Lean 4.34.1, `-j1`, and `-DautoImplicit=false`, with no diagnostics. All eight exported declarations were axiom-audited: each depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The verified result concerns the unchanged `paperSmallChain` in the pinned OpenAI source. The original capacities and padding remain $U=d^{20}$ and $L=d^{12}$, where the formal source uses

$$
d=10+(|I|+1)(|J|+1).
$$

Let $p$ be the actual number of small cells. The sharper physical variance coefficient supplied by the preceding integration is

$$
K_{p,U}=(1+2p^2)\frac{U(U+1)}2
\left(2+\frac{(p-1)_+(U+1)^2}{2}\right)+2,
$$

with $(p-1)_+=\max(p-1,0)$. This deliberately retains the upstream factor-two repair estimate. The chain bridge keeps the source's stationary distribution identity and its original dyadic proposal probability $\beta_d$ unchanged:

$$
\operatorname{Var}_{\pi}H\le\frac{2K_{p,U}}{\beta_d}\mathcal E_{\mathrm{chain}}(H).
$$

The source proves $\beta_d\ge1/(64d^2)$. For $1\le d,U$ and $p\le d$, retaining $(p-1)_+\le d-1$ in the arithmetic gives

$$
K_{p,U}\le8d^3U^4,\qquad
\frac{2K_{p,U}}{\beta_d}\le1024d^5U^4.
$$

Thus the original-scale theorem is

$$
\operatorname{Var}_{\pi}H\le1024d^{85}\mathcal E_{\mathrm{chain}}(H).
$$

The pinned source's [`paperSmallChain_poincare`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/FirstPaperSmallChain.lean) gives $d^{160}$ for this same chain. Before that final weakening, its existing variance/proposal calculation gives $98{,}560d^6U^6$, hence $98{,}560d^{126}$ at $U=d^{20}$. The localized bound improves the parameter dependence to $d^5U^4$.

This is an inverse-gap upper bound for the ideal small-state chain, not an end-to-end sampler runtime. The exact coefficient $2K_{p,U}/\beta_d$ is also retained in the verified theorem. For the all-small branch with no dense completion block, the companion additionally uses the source's [`unitSmallChain`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/AllSmallChain.lean) and its exact energy identity. That branch accepts every valid proposal, giving $K_{p,U}/\beta_d$ and the stronger conservative bound $512d^{85}$.

## Source bridge

The proof reuses `paperSmallChain_pi`, `paperSmallChain_energy_lower`, `stateWeight_positive`, and `chain_poincare_of_weighted_graph`. Its physical-variance premise is discharged using `Math115.PhysicalFullVariance.physical_variance_localized`, with the actual `stateCapacity`, source residual-capacity bound, and the original paper scales. It does not assume the desired Poincare inequality as a new hypothesis in the original-chain result.

Verified declarations in namespace `Math115.SmallChainGap`:

- `fullConstant_le_polynomial`
- `smallProposal_localized_budget`
- `chain_poincare_localized`, a generic normalization helper
- `paper_state_variance_localized`
- `paperSmallChain_poincare_exact`
- `paperSmallChain_poincare_d85`
The verified companion `AllSmallChainGap.lean` retains the same namespace and adds:

- `unitSmallChain_poincare_exact`
- `unitSmallChain_poincare_d85`

## Verification command

After the pinned source dependency closure is built, the core target is checked directly from `formal/` with:

```sh
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean -j1 \
  -DautoImplicit=false -R "$PWD" Math115/SmallChainGap.lean \
  -o .lake/build/lib/lean/Math115/SmallChainGap.olean
```

The all-small companion was checked with the same command, substituting `AllSmallChainGap` for both occurrences of `SmallChainGap` in file paths. Each of the eight declarations above was then checked with `#print axioms` in a separate importing file. The source checkout and its chain definitions were left unchanged.

## Relation to the reduced scales

Substituting $U=\kappa d^5$ for a fixed positive scale coefficient $\kappa$ into the parameterized arithmetic gives $1024\kappa^4d^{25}$. The separate [reduced ideal-chain module](reduced-small-chain.md) now verifies the actual completion-chain construction and its acceptance/capacity bridges at $U=47d^5$, $L=32d^3$, yielding $1024\cdot47^4d^{25}$ for its dense/reference branch.

That is a new parameterized ideal chain. The original `paperSmallChain` definition still hardcodes $U=d^{20}$ and $L=d^{12}$, and the $d^{85}$ theorem above concerns that literal definition. The reduced ideal-chain theorem does not by itself implement the finite-bit dense completion oracle or verify the end-to-end sampler runtime.
