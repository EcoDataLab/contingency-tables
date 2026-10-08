# Sharper child-path variance bound

This additive formalization proves the bound for the original `FiniteExposureVariance.variance` and `IntegerWeightedTransport.childProfile` definitions from `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

For nonnegative weights $z_0,\ldots,z_U$, define the adjacent path energy

$$
E_{\mathrm{path}}(H)=\sum_{j=0}^{U-1}\min(z_j,z_{j+1})(H_j-H_{j+1})^2.
$$

The hypothesis is the global endpoint-minimum property

$$
\min(z_a,z_b)\le z_j\quad\text{whenever }0\le a\le j\le b\le U.
$$

This property is weaker than log-concavity with interval support and is already proved for the source's genuine hard child masses by `child_minimum_limit`. It forces every weight between two positive weights to be positive. Local log-concavity without that support condition is insufficient: $(1,0,0,1)$ violates the global property even though its local log-concavity inequalities hold.

The verified conclusion is

$$
\operatorname{Var}_{z}(H)\le\frac{U(U+1)}2E_{\mathrm{path}}(H),
$$

where the source's variance is **unnormalized**: $\operatorname{Var}_{z}(H)=\sum_jz_j(H_j-\bar H)^2$. No positivity assumption on total mass is needed; all-zero weights and singleton support are included.

## Mode-centered proof

Choose an index $m$ at which $z_m$ is maximal. On the path from $r$ to $m$, the endpoint-minimum property makes each edge weight at least $z_r$. Telescoping and the source's finite Cauchy–Schwarz lemma therefore give

$$
z_r(H_r-H_m)^2\le |r-m|E_{\mathrm{path}}(H).
$$

The weighted mean minimizes squared error, so the variance is at most the sum of these terms. The exact distance sum is

$$
\sum_{r=0}^{U}|r-m|
=\frac{m(m+1)+(U-m)(U-m+1)}2
=\frac{U(U+1)}2-m(U-m).
$$

This proves both the universal triangular coefficient and a smaller coefficient when a mode lies in the interior. The proof does not divide by an edge weight or use a value of a mean at a zero-mass child.

`weighted_path_variance_of_adjacent` retains distinct localized energies supplied for each adjacent pair. It is designed to compose with the physical leaf-energy bounds, avoiding a repeated charge of one global energy for every path edge.

## Formal files and interfaces

- `formal/Math115/PathDistanceSum.lean`: exact distance formulas and their triangular upper bound.
- `formal/Math115/PathVariance.lean`: the actual weighted path inequality, the mode-dependent refinement, localized-energy substitution, and wrappers using upstream positive-child and hard-child-limit hypotheses.

The compiled `Math115.PathVariance` exports are:

- `pathEnergy_nonneg`
- `weighted_pair_path_bound`
- `centered_at_mode_term`
- `weighted_path_variance_mode`
- `weighted_path_variance_mode_sharp`
- `weighted_path_variance_bound`
- `weighted_path_variance_of_adjacent`
- `child_variance_path_bound`
- `child_variance_limit_path_bound`

The compiled `Math115.PathDistanceSum` exports are `sum_values_eq_triangle`, `sum_dist_eq_two_triangles`, `sum_dist_eq_triangle_sub`, and `sum_dist_le_triangle`.

## Verification

On 2026-10-08, from `formal/`:

```sh
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake build Math115.PathVariance
```

The final build returned `Built Math115.PathVariance (99s)` and `Build completed successfully (9001 jobs)`, with no warnings. The larger dependency set includes the source's unchanged `FiniteRepairVariance`, whose `variance_le_center` theorem is reused directly. The formal project's pinned toolchain and dependency revisions apply.

A separate scratch module imported the compiled module and ran `#print axioms` on all thirteen declarations listed above using `lake env lean`. Every declaration depended only on `propext`, `Classical.choice`, and `Quot.sound`; none depended on `sorryAx` or a new axiom. The audit exited successfully. Physical graph exposure and repair are separate integration steps.
