# The compiled physical chain at the smaller scales

The existing ideal auxiliary-chain construction now has a compiled inverse-gap
allowance **`3442d⁹`**, at `U=11d(m+n−2), L=7`, where
`d=10+(m+1)(n+1)`. Its more informative shape bound is
**`30976d⁷(m+n−2)²`**. This uses the original dyadic proposal and actual
completion-count weights. It is separate from the stronger compiled
[`431d⁸` rational defect trace](physical-defect-trace.md), which changes the
chain by eliminating balanced vertices.

This checkpoint proves a Poincare inequality for the literal
`ReducedAllSmallChain.selectedChain` at the new parameters. Its automatic
`feasibleSquareChain` wrapper requires only `m,n≥2` and equal natural-margin
totals; zero margins are included. State existence, the small-cell branch,
capacity, local transport, full variance, acceptance and normalization are
derived. A complete sampler using these parameters, its output law and its
runtime still require integration.

## What is now connected

Write `p` for the number of cells in the actual small-cell mask. The proofs
use the original common cutoff `U`; no substitution of a different effective
width inside the correction kernel is needed.

| Step | Derived quantity | Actual interface |
|---|---|---|
| Local context | Context variance at most `(r+1)U²` times its leaf energy, with `r` later cells | Same boxed kernel, actual child masses and means, actual positive support, including empty and singleton support |
| Exposure | Balanced variance at most `pU²` times physical energy | Exact conditional-variance telescoping and unique ownership of each leaf energy |
| Repair | Full unnormalized variance at most `2p³U²` times graph energy | Original physical repair, completion-weight domination, label injection and genuine paper capacity |
| Acceptance | Every directed reference edge accepts with probability at least `1/2` at `L≥7` | Compiled reciprocal zero-entry theorem on the actual residual completion table |
| Normalization | Reference/selected inverse gap at most `4p³U²/β`; unit branch at most `2p³U²/β` | Existing chain's stationary law, graph energy and original proposal `β` |

If there are fewer than two small cells, the small mask is empty: any small
row or column already contains at least two cells. The profile chain is then
a singleton and has zero variance. Its dense completion fiber may still
contain many ordinary tables. Equal totals supplies a physical state in
either branch.

The last step uses `β⁻¹≤64d²` and `p≤d`, giving `256d⁵U²` for the selected
chain. Substitution of `U=11d(m+n−2)` gives `30976d⁷(m+n−2)²`.
For `m,n≥2`, `3(m+n−2)+13≤d`; hence the rounded bound `3442d⁹`.
For any fixed aspect class with `(m+n−2)²≤Ad`, the same compiled shape
inequality gives `30976A d⁸`.

The [formal packet](../research/physical-spectral/) lists the exact Lean
statements and their hypotheses. Its selected environment audit records the
full dependency closure of each headline. These are ordinary compiler checks
with trusted pinned compiler and reused baseline dependencies; strict
Comparator replay of the complete sampler remains separate.

## Actual padding counts at the same cutoff

The new `Research.ReciprocalCount` module proves the ordinary table inequality

```
N(r+e_i,c+e_j) (r_i+1)(c_j+1) ≤ N(r,c) (r_i+n)(c_j+m).
```

It then inducts over all increments and all marked padding cells. At `L=7`
and `U=11d(m+n−2)`, the resulting theorem bounds the padded count by twice
the original count. It assumes the marked incident margins meet the cutoff;
it does not assume a count-ratio conclusion. Zero margins, zero padding,
empty marked sets and singleton or empty fibers are handled in the count
theorems. The [counting derivation](reciprocal-padding-growth.md) describes
the shape and thin-table consequences.

## Distinction between the two compiled chains

The d⁹ theorem keeps the original proposal allowance of order `d²`.
The [actual rational d⁸ trace](physical-defect-trace.md) eliminates balanced
vertices and uses the proved neighbor allowance `4p−3`. Its weighted trace,
accepted conductances and defect-mass normalization now compile. The full
variance theorem above is common to both arguments. The trace constructor
keeps nonempty positive defect support and `p≥2` explicit; the d⁹ wrapper
instead supplies the feasibility and degenerate branches automatically.

The existing complete compiled machine still uses the earlier d¹⁷ route and
re-proves upstream's existential bounded-sampling theorem. The new chain
inequality does not change that machine's theorem, prove a smaller complete
runtime degree, or measure practical mixing.
