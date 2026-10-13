# The actual rational defect trace

The concrete accepted-conductance trace on positive physical defect states now
has a Lean Poincare theorem with coefficient **`431d⁸`** at
`U=11d(m+n−2), L=7`, where `d=10+(m+1)(n+1)`. The more informative shape
coefficient is **`3872d⁶(m+n−2)²`**. This checkpoint constructs a finite lazy
reversible chain and proves its variance-to-energy bound. It changes the chain
by eliminating balanced vertices; the [original selected-chain d⁹
theorem](physical-spectral-chain.md) remains a separate result.

The combined public-scope fresh build and audit passed, alongside independent
AI source review. No complete sampler or runtime implementation is provided
by this packet.

## Vertices, conductances and kernel

Let `m,n` be the finite ordered row and column cardinalities. A cell is small
when its original row margin is below `U` or its original column margin is
below `U`; write `p` for the number of such cells. The actual physical state
space retains only profiles with positive hard completion weight. Its source
pattern makes each state balanced or a single defect. Partition these states
into `B` (balanced) and `D` (not balanced), with completion-count weights `w`.

On an actual unit-exchange or designated-repair edge, let `c(x,y)` be the
number of source completion tables whose prescribed reference translation
remains valid. It is zero off those edges, including self pairs. When a large
reference row or column is missing, the actual unit-weight branch instead
has `c(x,y)=1` on its physical edges. Capacity and ordinary completion-count
identities justify both definitions. The resulting conductance is symmetric,
nonnegative and at most `w(x)`.

There are no physical `B–B` edges. Retain the direct `D–D` conductances
`W(d,e)=c(d,e)`, and write `S(b,d)=c(b,d)`. A balanced vertex can have many
defect neighbors. Put

```text
s_b = Σ_d S(b,d)
T(d,e) = W(d,e) + Σ_b S(b,d) S(b,e) / s_b
Q = 4p−3,                 β = 1/(2Q)
P(d,e) = β T(d,e)/w(d)    for d≠e
P(d,d) = 1 − Σ_{e≠d} P(d,e).
```

A zero-mass star has every incident `S(b,d)=0`; its displayed contribution
is zero. The raw matrix `T` includes star-return terms on its diagonal. The
move kernel omits that diagonal, so those returns contribute to holding
probability. The constructed chain is lazy, `P(d,d)≥1/2`, and has stationary
law

```text
π(d) = w(d)/Z_D,          Z_D = Σ_{e∈D} w(e).
```

Thus its state law is completion-weighted on positive defects. It does not
itself specify an output law on ordinary tables.

## Why the actual degree is at most 4p−3

Positive physical states have fixed false-view totals on each small row and
fixed true-view totals on each small column. A unit exchange must preserve
these selected sums. For any fixed coordinate anchor, at most one Bool view
of each other small cell is permitted; both views would force that cell's row
and column to be large. The anchor's own cell is also excluded. Projection
into other cells is injective, giving at most `p−1` targets per anchor.

The actual signed single-defect pattern forces an exchange to raise a
coordinate of the deficient cell or lower a coordinate of the excess cell.
Their two views give four anchors, hence at most `4(p−1)` unit neighbors.
At most one designated forward repair is added, by source-profile
injectivity. A reverse repair cannot start at a defect because every repair
target is balanced. Physical-profile injectivity then gives the actual full
neighbor count `4p−3`, including both balanced and defect neighbors. The
degree theorem derives these facts from actual states and margins; a desired
degree bound is not one of its hypotheses.

The accepted source row satisfies
`Σ_e W(d,e)+Σ_b S(b,d)≤Qw(d)`. Star elimination preserves this row sum in
the raw trace matrix, including returns. Consequently the chosen `β` gives
the claimed laziness without a balanced-vertex row budget.

## Energy and the bound

Use ordered-edge energy with its factor `1/2`. Extending a defect observable
to the weighted neighbor mean at each balanced vertex gives exactly the
Schur trace energy. Restriction bounds raw defect variance by raw full
variance. The already proved actual full-state inequality has coefficient
`C=2p³U²` for the original minimum-endpoint-weight graph.

At `L≥7`, actual directed reference translations accept at least half the
source weight. Together with symmetry this supplies at least half the
masked minimum-endpoint conductance. The missing-reference unit branch
satisfies the same comparison. Thus raw defect variance is at most `2C`
times trace energy.

The exact normalized trace identities are

```text
Var_π(g) = Var_w,D(g)/Z_D
E_P(g)   = (β/Z_D) E_T(g).
```

There is no full-mass/defect-mass ratio. The normalized coefficient is
`2C/β=4QC≤32p⁴U²`. Since `p≤d`, substitution of `U=11ds`,
`s=m+n−2`, gives `3872d⁶s²`. For `m,n≥2`, the existing dimension inequality
`3s+13≤d` gives the rounded allowance `431d⁸`.

| Claim | Lean statement | Hypotheses |
|---|---|---|
| Actual nonbalanced physical degree is at most `4p−3`. | `Math115.PhysicalDefectDegree.physical_nonbalanced_degree_le` | Actual positive physical state and its nonbalanced predicate; natural margins and finite ordered dimensions |
| The constructed trace has stationary law `w/Z_D` and is lazy. | `Math115.PhysicalDefectTrace.actualRationalTrace_pi`; `actualRationalTrace_lazy` | `p≥2`, nonempty positive defect support |
| Actual normalized rational trace coefficient is at most `32p⁴U²`. | `Math115.PhysicalDefectTrace.actualRationalTrace_poincare_square` | `U≥2`, `L≥7`, `p≥2`, nonempty positive defect support |
| At the preselected cutoff the coefficient is `3872d⁶s²`. | `Math115.PhysicalDefectTrace.actualRationalTrace_poincare_shape_square` | `m,n≥2`, `U=11ds`, `L=7`, `p≥2`, nonempty positive defect support at these parameters |
| The all-shape coefficient is `431d⁸`. | `Math115.PhysicalDefectTrace.actualRationalTrace_poincare_d8` | Same shape-theorem hypotheses; no supplied variance, capacity, acceptance or degree conclusion |

An empty defect support has no chain under this constructor. A singleton
positive defect support is allowed and has zero variance. The theorem keeps
`p≥2` explicit; it is not a total branch-selection wrapper for arbitrary
margins. No assumption that every margin is positive is required.

## Verification and implementation boundary

The [formal packet](../research/physical-defect-trace/) and
[source review](physical-defect-trace-review.md) bind the concrete definitions
and assumptions. Reproduce the additive scope using built pinned baseline
dependencies and a new output directory:

```sh
python3 research/repair-accept/verify.py --scope physical-defect-trace \
  --output .local/physical-defect-trace-fresh
```

This is an ordinary Lean build and selected-module/headline audit, with the
pinned compiler and reused baseline imports trusted. It is separate from
strict Comparator replay and the historical default-target audit.

The [saved receipt](../research/physical-defect-trace/results/verification.json)
records fresh compilation of 41 research-scope modules plus the genuine
`SmallPatternArithmetic` helper and `EnvironmentAudit`. Its audit enumerates
1,147 selected declarations, including 1,011 theorems, and checks nine
headline dependency closures. The actual d⁸ headline has 30,429 declarations
in its closure. All selected declarations and all headline closures use only
standard Lean axioms. The audit took 142.412 seconds; this is verification
time, not a sampler or mixing benchmark. These overlapping research-scope
counts must not be added to the historical default-target audit count.

Only the rational trace is constructed and proved in this packet. Rounding
`β` down to a dyadic value between `β/2` and `β` gives the reviewed factor-two
allowances `64p⁴U²`, `7744d⁶s²` and `862d⁸`; that trace constructor and theorem
are not compiled here. The exact completion counts and weighted-star choices
in the rational definition have no runtime implementation in this packet.
Neither the changed-chain bound nor its source cutoff automatically proves a
smaller complete sampler runtime degree or measures practical mixing.
