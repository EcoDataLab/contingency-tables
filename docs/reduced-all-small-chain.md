# The reduced ideal chain for every margin shape

Sharper chain constants are now available in [PhysicalRepairRefinement](physical-repair-refinement.md) and its wrappers. The earlier valid coefficients retained below are the ones proved by these branch and existence modules themselves.

**Verification status: direct Lean compilation and transitive axiom audit passed on 8 October 2026.** `formal/Math115/ReducedAllSmallChain.lean` compiles with the pinned Lean 4.34.1 and existing dependency objects. It adds a module without changing the previously verified chain modules. All 17 module declarations audited use only `propext`, `Classical.choice`, and `Quot.sound`. Aggregate integration and checkpoint receipts remain separate.

When there is no large row or no large column, the dense completion rectangle is empty. The actual source completion-count identity then gives weight one for every retained physical state. The new `unitChain` uses the source unit Metropolis construction on that same physical graph, accepts every valid proposal, and has the exact energy identity

$$
\mathcal E_{\mathrm{unit}}(H)=\frac{\beta_d}{Z}\mathcal E_{\mathrm{physical}}(H).
$$

Consequently, for $U\ge2$, the proved unit-branch bounds are

$$
\operatorname{Var}_{\pi}H\le\frac{K_{p,U}}{\beta_d}\mathcal E_{\mathrm{unit}}(H)
\le512d^5U^4\mathcal E_{\mathrm{unit}}(H).
$$

This branch requires no lower bound on $L$. It uses the actual empty-completion weight theorem and discharges the source capacity premise.

The `selectedChain` wrapper chooses the proved reference completion chain when both a large row and a large column exist. Otherwise it uses `unitChain`. Both branches have the same completion-weight stationary law. For $U\ge2$ and $L\ge3d$, the proved uniform bound is $1024d^5U^4$.

At $U=47d^5$ and $L=32d^3$, `reducedSelectedChain` therefore satisfies

$$
\operatorname{Var}_{\pi}H\le1024\cdot47^4d^{25}\mathcal E(H)
$$

for every margin shape, without a supplied reference row or column. The empty-completion branch has the stronger coefficient $512\cdot47^4$.

The generic `selectedChain` interface still takes a nonempty positive-weight state space. The supplemental [`PhysicalStateNonempty.lean`](../formal/Math115/PhysicalStateNonempty.lean) proves that premise from equal ordinary total margins. Its direct compilation and all seven transitive axiom audits passed on 8 October 2026 with only the standard three axioms. It constructs a padded ordinary table, its balanced small profile, and an actual completion-fibre witness. The hard marginal equals that fibre's cardinality, so the witness gives positive weight.

`states_nonempty` works for arbitrary `U,L`, including zero scales and empty row or column types. No positivity of individual margins is assumed. `feasibleReducedChain` installs that result and selects the reference or unit branch automatically. Its stationary-law theorem and `feasibleReducedChain_poincare_d25` require only `∑ i, r i = ∑ j, c j`, with no external reference row, reference column, or nonempty-state hypothesis. These existence statements concern unrestricted ordinary margins and the exact source capacities; extra cell bounds or structural zeros require separate feasibility arguments.

This is an ideal-chain construction using exact mathematical completion laws; it does not implement the finite-bit dense completion oracle or establish end-to-end sampler runtime. See the already verified [reference-branch construction](reduced-small-chain.md) and [original-scale comparisons](small-chain-gap.md).

## Verification scope

The direct command uses `lake env lean -j1 -DautoImplicit=false` from `formal/`, writing its `.olean` and `.ilean` under `formal/.lake/build/lib/lean/Math115/`. This does not rebuild the dependency closure. Local compilation diagnostics are retained under `.local/resume-formal/`; aggregate imports and public verification receipts are maintained separately.
