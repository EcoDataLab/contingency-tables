# Actual physical variance, chain gap and padding counts

This additive packet connects the proved retained spectral theorem to the
original physical table graph and its existing normalized ideal-chain
construction. At `U=11d(m+n−2), L=7`, the selected-chain theorem gives
`30976d⁷(m+n−2)²`, hence **`3442d⁹`** for arbitrary aspect ratios with
`m,n≥2`. The [derivation and boundaries](../../docs/physical-spectral-chain.md)
separate it from the reviewed d⁸ defect trace and the unchanged complete
compiled sampler.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| One actual ordinary-table increment has the reciprocal product count bound. | `Research.ReciprocalCount.one_unit_count_growth` | Natural margins and marked row/column indices; no supplied count inequality or positivity premise |
| Actual marked padding at `U=11ds,L=7` has count at most twice the original count. | `Research.ReciprocalCount.shape_padding_count_le_twice` | `s=m+n−2`, `mn≤d`, original marked incident margins at least `U`; the finite increment induction is proved |
| The actual original-width context satisfies the spectral variance bound. | `Math115.RetainedContextVariance.paperCapacity_context_variance_spectral_bound` | Genuine source capacity, `U≥2`, `mn≤d`, literal small cell, valid prefix and suffix enumeration; no desired cap or variance premise |
| Exposure yields balanced variance at most `pU²` times actual physical energy. | `Math115.RetainedTransversalVariance.paperCapacity_transversal_variance_spectral` | Natural margins, `U≥2`, `mn≤d`, actual observable; conditional variance and edge ownership are derived |
| Full physical variance is at most `2p³U²` times the original graph energy. | `Math115.RetainedRepairSquare.state_variance_square` | `U,p≥2`; genuine source capacity and actual physical states; no variance or residual-cap premise |
| The actual reference chain has coefficient `4p³U²/β`. | `Math115.RetainedChainSquare.chain_poincare_square` | Nonempty states, reference large row and column, `U,p≥2`, `L≥7`; half acceptance and stationary normalization are derived |
| The actual empty-completion unit branch has coefficient `2p³U²/β`. | `Math115.RetainedChainSquare.unitChain_poincare_square` | Nonempty states, missing large row or column, `U,p≥2`; no acceptance or padding lower-bound premise |
| The actual selected chain at the smaller scales satisfies the shape and d⁹ bounds. | `Math115.RetainedChainSquare.selectedChain_poincare_shape_square`; `selectedChain_poincare_d9` | `m,n≥2`, nonempty states and at least two small cells at the preselected cutoff; both original chain branches are covered |
| Equal totals automatically supplies a chain with the d⁹ bound and its completion-weight stationary law. | `Math115.RetainedChainSquareTotal.feasibleSquareChain_poincare_d9`; `feasibleSquareChain_pi` | Finite ordered dimensions `m,n≥2`, natural margins with equal totals; no supplied state-existence or small-cell-count premise; zero margins included |

Reproduce with the pinned compiler and already-built baseline dependencies:

```sh
python3 research/repair-accept/verify.py --scope physical-spectral \
  --output .local/physical-spectral-fresh
```

Use a new output directory. The runner freshly compiles this packet and its
selected [retained-spectral](../retained-root/) and
[constant-padding](../constant-padding/) research dependencies from their
existing source locations. The [receipt](results/verification.json) binds
source/object hashes, complete selected-module declaration enumeration and
twelve headline dependency closures. The exact theorem types are included.

Only standard Lean axioms occur. Compiler and baseline imports remain trusted.
This is an ordinary additive build, not a fresh default-target build or strict
Comparator replay. Its counts overlap earlier packets and must not be added
to the historical default-target audit count. Separate AI agents reviewed the
mathematical interfaces; no outside human review is claimed.
