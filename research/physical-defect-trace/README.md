# Actual rational accepted defect trace

This additive Lean packet constructs the weighted harmonic trace on actual
positive physical defect states. It derives the physical neighbor bound
`4p−3`, uses actual completion-translation accepted conductances, and proves
the normalized coefficient **`32p⁴U²`**. At `U=11d(m+n−2), L=7`, this gives
**`3872d⁶(m+n−2)²≤431d⁸`**, with `d=10+(m+1)(n+1)`.

The [derivation and kernel](../../docs/physical-defect-trace.md) specify
the changed chain and its exact normalization. The
[independent AI source review](../../docs/physical-defect-trace-review.md)
binds all nine packet source hashes. The combined public-scope fresh build
and compiled-environment audit passed; the
[saved receipt](results/verification.json) includes the exact theorem types
and source/object bindings.

| Claim | Lean statement | Hypotheses |
|---|---|---|
| Actual defect degree is at most `4p−3`. | `Math115.PhysicalDefectDegree.physical_nonbalanced_degree_le` | Actual positive nonbalanced physical state; natural margins, finite ordered dimensions |
| Weighted harmonic extension has exactly the trace energy. | `Research.WeightedHarmonicTrace.harmonic_energy_eq_trace` | Finite DD and cross conductances, nonnegative cross conductances; zero stars handled |
| Concrete rational trace has stationary law `w/Z_D` and is lazy. | `Math115.PhysicalDefectTrace.actualRationalTrace_pi`; `actualRationalTrace_lazy` | `p≥2`, nonempty positive defect support |
| Actual normalized coefficient is at most `32p⁴U²`. | `Math115.PhysicalDefectTrace.actualRationalTrace_poincare_square` | `U≥2`, `L≥7`, `p≥2`, nonempty positive defect support; variance, capacity, acceptance and degree are derived |
| The selected cutoff gives `3872d⁶s²` and `431d⁸`. | `Math115.PhysicalDefectTrace.actualRationalTrace_poincare_shape_square`; `actualRationalTrace_poincare_d8` | `m,n≥2`, `s=m+n−2`, `U=11ds`, `L=7`, `p≥2`, nonempty positive defect support at those parameters |

Reproduce with the pinned compiler and already-built baseline dependencies:

```sh
python3 research/repair-accept/verify.py --scope physical-defect-trace \
  --output .local/physical-defect-trace-fresh
```

Use a new output directory. The runner freshly compiles this packet, the
genuine additive upstream `SmallPatternArithmetic` helper, and its selected
[physical-spectral](../physical-spectral/),
[constant-padding](../constant-padding/) and
[retained-root](../retained-root/) dependencies from existing source
locations. It records source/object hashes, selected-module declaration
enumeration and headline dependency closures. Compiler and baseline imports
remain trusted. This ordinary additive verification is separate from a
fresh default-target build and strict Comparator replay; overlapping packet
counts must not be added to the historical default-target audit count.

The saved run freshly compiled 41 research-scope modules plus
`SmallPatternArithmetic` and `EnvironmentAudit`. The audit enumerates
1,147 selected declarations, including 1,011 theorems, and checks nine
headline dependency closures. The actual d⁸ theorem's closure has 30,429
declarations. All selected declarations and headline closures use only
standard Lean axioms. The audit took 142.412 seconds; this reports
verification time, not runtime or mixing performance. Independent AI
source review is recorded; no outside human review is claimed.

The rational chain uses proposal `1/[2(4p−3)]`. Its vertices have weights
equal to actual completion counts, and its transitions include weighted
balanced-star choices. Only its mathematical finite-chain construction is
compiled here. A dyadic rounding is mathematically reviewed, but no dyadic
trace theorem, transition sampler or runtime implementation is included.
The original full-state chain and complete sampler remain separate.
