# Formal all-donor switching, survival, and mean estimates

`formal/Math115/SmallEntrySwitching.lean` and `formal/Math115/SmallEntryTail.lean` prove small-entry, survival, and mean estimates for the **unchanged upstream ordinary-table model**, using OpenAI's actual `Table` and `fourCycle` definitions at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

For a uniformly selected table with fixed nonnegative integer margins, marked entry $X_{as}$, incident margins at least $a_0$, and $0\le t\le a_0$, put $e=(|I|-1)(|J|-1)$. The verified stronger linear probability statement is

$$
\Pr[X_{as}<t]\le\frac{te}{a_0+e}.
$$

The verified finite-product statement is

$$
\Pr[X_{as}<t]\le 1-\prod_{k=0}^{t-1}\frac{a_0-k}{a_0-k+e},
$$

and the verified mean bound is

$$
\mathbb E[X_{as}]\ge\frac{a_0}{e+1}.
$$

The direct incidence argument gives the intermediate denominator $a_0-t+1+e$; the simpler denominator $a_0-t+1$ is also verified for direct use in the padding scale certificate. The count versions do not need a nonempty fiber; the probability versions assume equal margin totals and use upstream's existence theorem to prove the table count is positive. Zero thresholds, zero donor capacities, and one-row or one-column cases are included. When $a_0=e=0$, the linear probability statement is the empty-event bound; Lean uses its usual convention $0/0=0$. Every denominator in a nonempty survival product is strictly positive because $k<t\le a_0$.

## What Lean checks

The incidence proof counts all positive switch amounts, for every donor row and donor column distinct from the marked ones. A source table, donor pair, and switch amount maps to its actual `fourCycle` target, donor pair, and source marked height. The target marked entry equals source height plus the positive switch amount. Those data recover the amount and then recover the source table by cancelling the integer four-cycle update. This establishes an injection into reverse labels; it does not assume a switching-degree estimate.

The donor lower bound follows from the original table's margin equations and the finite-sum inequality

$$
\min\left(\sum_i u_i,\sum_j v_j\right)\le\sum_{i,j}\min(u_i,v_j).
$$

The refined denominator retains the difference between $t$ and the number of admissible source heights at each target. `SwitchingFiniteSums.lean` supplies the finite-sum and deficit identities used in the proof.

Compiled declarations in namespace `Math115.SmallEntrySwitching`:

- `all_donor_incidence_bound`
- `donor_capacity_sum_lower`
- `donor_capacity_sum_lower_of_margins`
- `all_donor_small_entry_count_refined`
- `all_donor_small_entry_count`
- `all_donor_small_entry_probability_refined`
- `all_donor_small_entry_probability`

## Shifted-fiber proof

`shiftEquiv` adds or subtracts $k$ only in the marked cell. It gives an explicit bijection between the event $X_{as}\ge k$ in the original fiber and ordinary tables whose marked row and column margins are each reduced by $k$. The proof verifies both margin equations and both inverse identities.

Let $F_k$ be the number of original tables with $X_{as}\ge k$. Applying the verified zero-entry bound in the shifted fiber gives the cross-multiplied recurrence

$$
F_k(a_0-k)\le F_{k+1}(a_0-k+e),\qquad k<a_0.
$$

This step divides by no conditional table count. `SurvivalAlgebra.lean` proves the product and linear consequences of that recurrence. The linear induction has nonnegative slack $F_0 e k(e-1)$ when $e\ge1$; the separate $e=0$ table case follows from the already verified direct switching bound.

For the mean, the proof telescopes the potential $F_k(a_0-k)$, giving

$$
a_0F_0\le(e+1)\sum_{k=0}^{a_0-1}F_{k+1}.
$$

An explicit injection sends each counted surviving level into one unit of the corresponding marked entry. Thus the survival sum is at most the sum of marked entries over all original tables, which proves the mean bound.

Compiled declarations in namespace `Math115.SmallEntryTail`:

- `shiftEquiv` and `shiftPositiveEquiv`
- `survival_step` and `survival_step_real`
- `small_card_add_survival`
- `all_donor_small_entry_count_strong`
- `all_donor_small_entry_probability_strong`
- `all_donor_survival_product_count`
- `all_donor_small_entry_probability_product`
- `survival_sum_le_entry_sum`
- `all_donor_entry_sum_lower`
- `all_donor_entry_mean_lower`

Compiled algebra interfaces in namespace `Math115.SurvivalAlgebra` are `nat_lower_tail_linear_bound`, `nat_survival_product_bound`, and `nat_mean_tail_sum_bound`. These generic statements are applied to the actual table survival counts by the theorems above.

## Verification checkpoint

On 2026-10-08, from `formal/`:

```sh
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake build Math115.SmallEntrySwitching
```

Result: `Built Math115.SmallEntrySwitching (4.6s)` and `Build completed successfully (3095 jobs)`. Unchanged dependencies were cached. Toolchain and dependency revisions are the pinned versions recorded by the formal project.

The final tail build used the same environment and command with target `Math115.SmallEntryTail`. Result: `Built Math115.SmallEntryTail (16s)` and `Build completed successfully (3097 jobs)`.

Separate scratch modules imported the compiled modules and ran `#print axioms` using `lake env lean`: seven switching declarations, twelve shift/tail/mean declarations, and three algebra interfaces, all listed above. Every audited declaration depended only on `propext`, `Classical.choice`, and `Quot.sound`; none depended on `sorryAx` or a new axiom. Both scratch audits exited successfully. The final modules compile with the formal project's `autoImplicit=false` setting and no warnings.

The result concerns ordinary unweighted tables with fixed margins. It does not itself establish an analogous switching estimate for capped, weighted, structurally constrained, or confidential-data fibers, and does not complete verification of the full upstream sampler or counting algorithm. The padding application and end-to-end transport integration are separate declarations.
