# Effective-width scalar certificate

11 October 2026. This additive packet proves the numerical coefficient used by
the [effective-width derivation](../../docs/effective-defect-width.md).

| English claim | Lean statement | Hypotheses |
|---|---|---|
| The refined physical variance coefficient is at most `p³V⁴`, retaining the actual small-cell count. | `Math115.EffectiveWidthBound.refinedConstant_le_actual_width` | Natural `p,V`, `p≥2`, `V≥2`; `refinedConstant` is the existing explicit square-root expression. |

The exact type is

```lean
∀ (p V : ℕ), 2 ≤ p → 2 ≤ V →
  Math115.PhysicalRepairRefinement.refinedConstant p V ≤
    (p : ℝ)^3 * (V : ℝ)^4
```

Fresh ordinary Lean 4.34.1 compilation and an environment-derived audit passed.
The [receipt](results/verification.json) binds the source, compiler, imported
objects, all declarations defined by this module, and the headline's complete
dependency closure. Its axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Baseline imports and the compiler are trusted. This is not strict Comparator
replay or a rebuild of the default target.

The compiled statement bounds a scalar expression. It does not itself prove
the physical graph equivalence at the narrower cutoff, instantiate the weighted
trace, establish the new spaced-rejection lemma, or identify an encoded sampler.
Those boundaries remain explicit in the linked mathematical derivations.

With the repository's pinned compiler and built baseline dependencies:

```sh
python3 research/repair-accept/verify.py --scope effective-width \
  --output .local/effective-width-fresh
```

Use a new output directory for each attempt. The shared scoped runner does not
download dependencies or overwrite existing results.
