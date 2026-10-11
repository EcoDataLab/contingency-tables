# Aggregate bound for the same actual rational defect trace

This additive Lean packet bounds the actual boxed correction kernel using
original-margin donor budgets. It retains full completion multiplicities
through repair, including large-large crossings, and proves an additional
variance coefficient for the same canonical rational physical defect trace
constructed in [physical-defect-trace](../physical-defect-trace/).

Write `p` for the number of selected cells, `a,b` for the counts of original
row and column margins below `U`, and `s=m+n−2`. The proved local cap is

```text
c_l ≤ 2((a+b)U²+pU) max(z_(l−1),z_l).
```

It applies at every actual selected row-major root. The kernel, exposure
owners, full repair law, accepted conductances, and trace normalization are
retained literally. The actual source `paperCapacity` bounds and full-state
variance premise are discharged in the concrete aggregate theorems.

With `CT=U(U−1)+4((a+b)U²+pU)`, the packet derives actual full-state variance
at most `2p² CT` times physical graph energy and normalized defect-trace
variance at most `32p³ CT` times the same trace's energy. At
`U=11ds, L=7`, where `d=10+(m+1)(n+1)`, it proves

```text
Var_trace(g) ≤ 34848 d⁵ s³ E_trace(g).
```

Under the explicit aspect certificate `s²≤A d`, `A≥0`, it also proves

```text
Var_trace(g)² ≤ 34848² A³ d¹³ E_trace(g)².
```

Since variance and energy are nonnegative, this polynomial squared
certificate expresses the `d^(13/2)` coefficient for a fixed aspect
allowance. The Lean headline itself uses the displayed squared form.

| Claim | Lean statement | Explicit hypotheses |
|---|---|---|
| Full completed defects inject into the true residual child, including large crossings. | `Math115.CompletedRepairInjection.repairToChild_injective`; `repairToChild_large_crossing` | Selected fixed labels and their actual row-major order; full completion fibres |
| Actual same-box correction has the aggregate donor cap. | `Math115.AggregateCorrectionCap.physical_correction_le_aggregate_adjacent` | Uniform selected capacity, bounded actual prefix, capacities exclude no full source residual table; these are discharged for the genuine source capacity |
| Actual physical full-state variance has coefficient `2p² CT`. | `Math115.AggregateDefectTrace.state_variance_aggregate` | `U≥2`, `p≥2`; no desired variance or correction-bound premise |
| The same actual rational trace has coefficient `34848d⁵s³`. | `Math115.AggregateDefectTrace.actualRationalTrace_poincare_aggregate_shape` | `m,n≥2`, `p≥2`, nonempty positive defect support, `U=11ds`, `L=7` |
| That trace obeys the squared aspect certificate. | `Math115.AggregateDefectTrace.actualRationalTrace_poincare_aggregate_aspect_sq` | Same physical hypotheses, `A≥0`, `s²≤Ad` |

The nonempty positive-defect support and `p≥2` assumptions remain explicit.
The rational chain is exactly the existing canonical `actualRationalTrace`,
with proposal `1/[2(4p−3)]` and stationary law given by actual completion
weights normalized on defect states. Both reference-completion and unit
branches use the same proved bound. The sharper independently reviewed
`15488d⁵s³` argument is distinct from this simpler `34848d⁵s³` Lean theorem.

Reproduce with the pinned compiler and already-built baseline dependencies:

```sh
python3 research/repair-accept/verify.py --scope aggregate-defect-trace \
  --output .local/aggregate-defect-trace-fresh
```

Use a new output directory. The runner freshly compiles 49 research modules:
the eight new modules here and the 41 prior modules from their existing
source locations. It also freshly compiles the genuine pinned upstream
`SmallPatternArithmetic` helper and the compiled-environment auditor.
Sources are not copied from earlier public packets. The audit enumerates
declarations by these selected module identities and checks eight headline
dependency closures, including the prior actual `d⁸` theorem.

The [source bindings](source-bindings.json) record each public module, source
path, and frozen source hash. The fresh public-source build and compiled-environment audit passed; the
[saved receipt](results/verification.json) records exact theorem statements
and source/object hashes. Compiler and
baseline imports remain trusted. This ordinary additive verification does
not enlarge the historical default-target audit count, Linux build claim,
or strict Comparator replay scope. Packet counts overlap and must not be
added to those earlier counts.

The saved run freshly compiled 49 research modules plus the pinned helper
and auditor. It enumerates 1,264 selected declarations, including
1,118 theorems, and checks eight headline dependency closures. The actual
shape theorem's closure contains 30,453 declarations; the squared aspect
theorem's closure contains 30,456. All selected declarations and
headline closures use only standard Lean axioms. The audit took 168.205
seconds; this is verification time, not sampler runtime or mixing performance.

These are finite-chain mathematical theorems. This packet adds no trace
transition sampler, executable mixing benchmark, or runtime consequence.
No outside human review is claimed.
