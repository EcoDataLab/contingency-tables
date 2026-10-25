# AI source review of the actual rational defect trace

Independent AI source review found no mathematical or interface blocker in
the frozen sources below. It checked the actual degree proof and its use in
the concrete accepted-conductance trace, including masking, repair direction,
the balanced/defect partition and normalization. This is source review, not
outside human review, a novelty assessment, a runtime test or strict
Comparator verification. The saved combined public-scope fresh receipt and
audit bindings have also been checked and passed.

## Reviewed source identities

All files in this table are in
[`research/physical-defect-trace/formal/Research/`](../research/physical-defect-trace/formal/Research/).
Their bytes were independently hashed at review time.

| Source | SHA256 |
|---|---|
| `DefectCoordinateGeometry.lean` | `53a242f8e2109dfebe31144880afa94469d7d94c4d3eba76e1dd318a66254d17` |
| `PhysicalTraceMargins.lean` | `ae668f10683bd6d467f5812b3c2fa27709fad339aa9d236bb4a62ca3e0039eef` |
| `PhysicalDefectDegree.lean` | `6ceea40c8d116849eb5fb344acad20119c52daade2f0e9ed432ee4c82a645ba8` |
| `PhysicalTraceGeometry.lean` | `8396372acda284a4a1ac155f572a930a8d1f101be5c7601023a4c52bcda7836e` |
| `PhysicalAcceptedConductance.lean` | `cef44f4d5031d1219902bb85c57806be87ff74d01f2f04fcd4046a7a632222cc` |
| `PhysicalTraceIrreflexive.lean` | `28643dd815719eb26d7d86ee20092c0e70878b154944f7715ac6fdc306e90830` |
| `WeightedHarmonicTrace.lean` | `afead19468e408d9ef6c3469fdecfc4060698a98f01cfc1858aa7f842105af77` |
| `PhysicalDefectTrace.lean` | `b7c7c04b1d5456a95147be6b80f37ccaf1aa742b4cce0c305cc29e858d4ef8c3` |
| `PhysicalDefectTraceFinal.lean` | `ebcb0fea5128dd42b978ddd70f0e896d603dd0fbdc97b186551d657a273c0463` |

The additive upstream `SmallPatternArithmetic` helper expresses the source
balanced/defect predicates as equivalent integer cell-sum tests on bounded
profiles. Its reviewed SHA256 is
`4a06e19abdba59247a616772b5da560ec85bbde9e8f55871c28671f5971ac590`.
The selected verification scope also rebuilds that genuine helper and the
earlier physical-spectral, constant-padding and retained-root dependencies;
those dependency identities belong to the build receipt.

## Degree review

The fixed-line totals follow from actual positive physical states, genuine
paper capacity and original residual-margin bounds. They are not supplied
as extra assumptions of the final degree theorem. Natural subtraction is
handled using the corresponding original-margin bounds.

The coordinate projection is injective into the other small cells: the
fixed-line restrictions rule out both Bool views at one target cell and
rule out the anchor cell itself. The signed defect test is derived from the
actual bounded profile. The exchange orientation is correct: from
`x=removeOne(D,i)` to `y=removeOne(D,j)`, the target raises `i` and lowers
`j`. Its admissible pattern therefore forces one of the deficient/excess
anchors. The four candidate sets have total size at most `4(p−1)`.

Source-profile injectivity permits at most one designated forward repair.
A reverse repair cannot leave a defect because its source would be the
balanced repair target. Physical-profile injectivity transfers the profile
bound to the actual neighbor set. The result proves `4p−3` directly; no
desired degree conclusion or independent positivity premise is hidden in
the caller interface.

## Trace and normalization review

The partition is the balanced predicate and its complement on the actual
positive state space. The source Pattern makes the complement a genuine
single defect. Both unit exchanges and designated repairs exclude `B–B`
edges.

Reference accepted counts and the unit-weight fallback are masked by actual
adjacency. Symmetry uses genuine reference-margin totals. Off-edge and
self counts are zero, with self exclusion proved for both exchanges and
repairs. The DD block retains accepted DD conductance and the cross block
retains all accepted BD conductance; their sum is exactly the full source
row. Arbitrary multiple balanced neighbors are supported.

The generic harmonic equality eliminates every balanced star exactly and
handles zero-mass stars. Raw trace diagonal terms become holding rather
than extra moves. Restriction of unnormalized variance and the exact
`β/Z_D` energy identity cancel the defect normalizer. There is no extra
full-state partition-function ratio.

The actual full-state coefficient `2p³U²`, actual half acceptance at `L≥7`
and proved degree instantiate the generic transfer without leaving those
facts as final theorem premises. Choosing `Q=4p−3` yields `32p⁴U²`;
`U=11ds`, `p≤d` and the proved dimension inequality yield
`3872d⁶s²≤431d⁸`.

The [exact statement table](physical-defect-trace.md#energy-and-the-bound)
retains `U≥2`, `L≥7`, `p≥2` and nonempty positive defect support. The shape
and all-shape corollaries additionally require `m,n≥2`. The constructor
does not assign a chain to an empty defect branch. These are rational
changed-chain theorems; the reviewed dyadic rounding and a runtime trace
sampler remain separate.

## Saved verification bindings

The [public receipt](../research/physical-defect-trace/results/verification.json)
has SHA256
`5a5a8e5589775639e005748bf7420a48e257b09d24844bcf2b48ab638a3056d7`.
Its 43 compilation entries are the 41 selected research-scope modules,
the genuine `SmallPatternArithmetic` helper and `EnvironmentAudit`.
Every return code is zero, and all 43 current source hashes match the
receipt. The compiler is pinned Lean 4.34.1; the upstream source pin is
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

The compressed compiled-environment audit has SHA256
`060c9cbdc77657c51490e06ccfafcd139aaee2b2c5a68cf7c16109e02c0df6b4`;
the compressed imported-object manifest has SHA256
`00c7401fd488818a762762bf6198d70470f346326954e65dae6525f7a27c6d26`.
Both match their receipt bindings. The audit enumerates 1,147 selected
declarations and 1,011 theorems across 41 modules, and checks nine headline
closures. The d⁸ theorem's closure contains 30,429 declarations. Every
selected declaration and every headline dependency uses only standard
Lean axioms. The saved audit duration is 142.412 seconds.

This evidence is an ordinary fresh research-scope compilation and
compiled-environment audit with a trusted pinned compiler and reused
baseline imports. It is not a default-target rebuild or Comparator replay,
and the overlapping counts are not an addition to the historical
default-target audit. Reading these saved bindings did not rerun the
compiler or audit.
