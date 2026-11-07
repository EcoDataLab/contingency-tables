# Lessons from the multiplication improvement sequence

This review follows the major mechanisms from OpenAI's original integer
multiplication manuscript through the community's later constructions, rather
than treating one recent PR as the whole story. It is a source review, not a
reproduction of every construction. The useful question is which changes survive
the probability-law and complete-cost requirements of contingency sampling.

Snapshot: 11 October 2026. The original manuscript states `κ=2^-182` for
`O(n(log n)^(1−κ))`; the community's `frozen-154` patch is a later checkpoint.
Reviewed community main at `12a4934d15006e8c10f9b2264f13f8f341be802b` selects
`κ=0.000723571590007464`. Draft PR #434 at
`4bc4b3850d735379f30e5d273c0b635c364b07b0` claims
`κ=0.001246073505487942`, with an additional idle-hosting operator assumption.
These exponent savings are not practical runtime measurements. Its published
local wrapper receipts cover the preceding `d21614a` head; CI was pending in the
reviewed snapshot. We did not independently run the complete multiplication
checks. [Original introduction](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026/build/sections/00-introduction.tex),
[reviewed main](https://github.com/CrocSwap/integer-mult-bounds/tree/12a4934d15006e8c10f9b2264f13f8f341be802b),
[pinned PR package](https://github.com/rohanarun/integer-mult-bounds/tree/4bc4b3850d735379f30e5d273c0b635c364b07b0/research/e8-rank138-idle-hosting).

## What changed across the sequence

| Mechanism family | Change in the multiplication work | Relevance here |
|---|---|---|
| Parameter inequalities and direct routing | Tune stopping/dimension parameters, then remove a layout overcharge by changing how streams move. | Optimize the actual composed expression; a bound tied to an old implementation can cease to apply after a justified redesign. |
| Incidence circuits and shared DAGs | Reuse intermediate sums and auxiliary storage across stages, substantially reducing physical roles. | Reuse deterministic DP preparation and cycle-line conditionals. Count memory and cold-start cost separately. |
| Compact controls and Gaussian analysis | Replace expensive controls and tighten width/guard requirements using more precise analysis. | Examine reservation, precision and codec overestimates, while retaining all-execution and error guarantees. |
| Complex, ternary and product-ring algebra | Change the local algebra and stop recursive calls at a better interface. | Alternative completion representations may help; linear identities alone say nothing about nonnegativity or the desired table law. |
| Cayley covers and Clifford frames | Organize multiple stages with compatible data frames and more general subspaces. | A reminder to consider block decompositions and symmetry, not a ready-made sampler construction. |
| Paired cubes and completed banks | Share restored workspace across orthogonal blocks. | Scratch reuse can reduce implementation cost, but fresh random draws cannot be identified merely because storage is reusable. |
| Register lifetimes and response kernels | Delay reads, remove dead accumulators, cancel responses and retime whole words. | Deterministic preprocessing can be amortized; random-bit dependence and complete draw semantics must remain explicit. |
| CP-SAT, annealing and flow | Search local recipes, donor assignments and gate schedules, then exactly reprice the resulting construction. | Small exact searches for block kernels, flow comparisons and rejection rules are plausible. A search objective must match the final quantity claimed. |
| E8/Hamming geometry | Use different code/root structures to build stronger transform units. | No direct transfer identified. Symmetry may guide a representation, but is not evidence of a spectral gap. |
| More stages and compressed windows | Extend bridge schedules and distribute residual blocks across replicas. | Decomposition may reduce a bottleneck while adding overhead elsewhere. Charge the full recursion, state size and random bits. |
| Mutable frames, split centres and idle hosting | Change interfaces, cancel source terms and place residuals in otherwise idle coordinates. | A promising interface change needs a new correctness argument. Finite placement checks do not prove an operator identity—or a probability law. |

The historical stages are documented in the
[result history](https://github.com/CrocSwap/integer-mult-bounds/blob/12a4934d15006e8c10f9b2264f13f8f341be802b/docs/research/result-history.md),
[compact-control review](https://github.com/CrocSwap/integer-mult-bounds/blob/12a4934d15006e8c10f9b2264f13f8f341be802b/docs/research/compact-control-review.md),
[ternary review](https://github.com/CrocSwap/integer-mult-bounds/blob/12a4934d15006e8c10f9b2264f13f8f341be802b/docs/research/ternary-review.md),
[three-stage cover](https://github.com/CrocSwap/integer-mult-bounds/blob/12a4934d15006e8c10f9b2264f13f8f341be802b/docs/three-stage-cover.md),
[paired-cube review](https://github.com/CrocSwap/integer-mult-bounds/blob/12a4934d15006e8c10f9b2264f13f8f341be802b/docs/research/community-round6-review.md), and
[entrance-bank review](https://github.com/CrocSwap/integer-mult-bounds/blob/12a4934d15006e8c10f9b2264f13f8f341be802b/docs/research/community-round8-review.md).
The later search and geometry stages have their own scopes in
[#296](https://github.com/CrocSwap/integer-mult-bounds/pull/296),
[#334](https://github.com/CrocSwap/integer-mult-bounds/pull/334),
[#370](https://github.com/CrocSwap/integer-mult-bounds/pull/370),
[#386](https://github.com/CrocSwap/integer-mult-bounds/pull/386),
[the split-centre argument](https://github.com/CrocSwap/integer-mult-bounds/blob/6d9244518175caf9e0089f92486959bc2c317273/research/split-centres-global/PROOF.md), and
[the final pinned hosting argument](https://github.com/rohanarun/integer-mult-bounds/blob/4bc4b3850d735379f30e5d273c0b635c364b07b0/research/e8-rank138-idle-hosting/PROOF.md).
Their contributors and inherited constructions remain credited by the
[community ledger](https://github.com/CrocSwap/integer-mult-bounds/blob/12a4934d15006e8c10f9b2264f13f8f341be802b/CONTRIBUTORS.md).

One especially transferable observation is that total rank or addition count
can mis-rank recursive algorithms: the distribution of child costs matters.
The reviewed [#279 integration](https://github.com/CrocSwap/integer-mult-bounds/blob/12a4934d15006e8c10f9b2264f13f8f341be802b/docs/research/community-pr279-review.md)
retimes child ranks while retaining total rank, improving its recursive moment.
The analogue here is to minimize mixing, output rejection and completion cost
together. Improving an isolated inverse gap is insufficient.

Negative results are equally useful. The community records failed physical
transfers, limited recipe-class optima, and cases where a proxy score disagrees
with the final exponent. Its
[paradigm-search obstruction](https://github.com/CrocSwap/integer-mult-bounds/blob/475a088b5862f75f0b10596cfd6842d19531a5ec/research/negative-results-paradigm-search/README.md)
and [campaign results](https://github.com/CrocSwap/integer-mult-bounds/blob/fa8ab946df57ebadae1a470b637c2a590a0a5317/research/campaign-100-results/README.md)
are model-specific, not impossibility claims about every multiplication algorithm.
Our existing padding and local-walk obstructions require the same care.

## Concrete directions for this repository

**Use more of each endpoint.** The [repair-output result](repair-output.md)
now has compiled actual-fiber and finite-bit retry proofs. In the positive
all-small regime it reduces a sufficient retry allowance to `min(m,n)` while
keeping the proved chain. An initially more elaborate auxiliary-law change did
not beat the simpler scaled-rejection comparison. The next step is connecting
the proved terminal law to the encoded walker; the new rule is not yet part
of the compiled machine.

**Eliminate a costly intermediate state exactly.** The [defect-only chain](defect-trace.md)
uses a Schur complement to remove balanced repair stars, then samples the
resulting within-fiber refresh directly. This changes the proposal normalization
from quadratic in the number of cells to linear in `m+n`. The reviewed
all-small allowance becomes `2500d^16` (`5000d^16` for dyadic proposals).
The generic energy/variance transfer is compiled, and a
[direct finite-bit reference](direct-defect-sampler.md) now implements the unit
branch. The [variable-capacity refinement](rectangular-defect.md) reaches
`d^(31/2)` for every both-small aspect ratio; the [weighted trace](general-defect-trace.md)
and [joint correction](general-defect-output.md) extend the mathematical route
to nonempty completion blocks at `d^16`. Physical Lean assembly and general
encoded integration remain open. These are concrete uses of network elimination
and block sampling; no multiplication theorem is assumed to transfer.

**Finish pricing the literal program.** The existing
[affine degree refinement](composed-complexity.md) already separates output size
from the cost of computing that output's length. This is closely aligned with
the multiplication sequence's successful removal of composition overcharges.
The [current cost table](composed-complexity.md#exact-draw-cost-certificates)
leaves the two packed-trial certificates open; branch selection, printing,
initialization, fallback and retry parsing now have numerical bounds. Faster
integer multiplication alone is unlikely to remove exponents created by coarse
loop/encoding/composition bounds; the actual realizers need to be inspected.

**Try block heat baths and local-to-global analysis.** Cryan, Dyer, Goldberg,
Jerrum and Martin analyze contingency-table chains with a fixed number of rows;
that restriction matters for any attempted transfer to growing dimensions.
[Their paper](https://homepages.inf.ed.ac.uk/mcryan/cdgjm.pdf) motivates looking
for a block conditional law that can be sampled cheaply and compared to the
full chain. The new binary-matrix preprint by Fu, Qin and Wang proposes a
two-row heat bath, a three-row reduction, and harmonic decomposition. We have
read its argument outline, not checked its Lean build. Its binary restriction
does not cover arbitrary nonnegative integer cells.
[Preprint, version 2](https://arxiv.org/html/2606.22636v2).

There is a concrete law mismatch to avoid: expanding margins `(2,2)/(2,2)` into
four labeled workers and four labeled slots gives `4,16,4` assignments to the
three aggregate tables. Its probabilities are `1/6,2/3,1/6`, rather than uniform
`1/3,1/3,1/3`. Thus a binary/labeled matching sampler does not automatically solve
the aggregate-table problem. A valid reduction needs to correct that multiplicity
and price the correction.

**Consider nonlocal or nonreversible moves where diffusion is the obstruction.**
Chen, Lovász and Pak show how lifting can accelerate suitable chains and explain
limits of reversible lifts. This supports testing directed momentum on a small
family, not assuming that adding labels always helps. Our `2×2` repaired-coordinate
lower bound shows why tuning reversible unit moves alone leaves a quadratic
obstruction in that graph. Full-line heat baths already bypass it in this easy
case. [Lifting Markov chains](https://www.math.ucla.edu/~pak/papers/stoc2.pdf).

**Check the structural hypotheses before importing log-concavity.** Lorentzian
polynomials provide powerful tools, but the ordinary cell-variable generating
polynomial is not automatically in that class. For `2×2` permutation margins it
is `x11·x22+x12·x21`: its Hessian has two positive eigenvalues, whereas the
quadratic Lorentzian condition allows at most one. The support also fails the
single-coordinate exchange property. A different representation or a theorem
tailored to contingency counts is needed.
[Lorentzian polynomials](https://annals.math.princeton.edu/wp-content/uploads/annals-v192-n3-p04-s.pdf),
[contingency-count applications](https://arxiv.org/abs/2008.05907).

Finally, the [implemented reference-tool improvements](implementation-benchmarks.md)
reuse exact weighted choices and cycle-line conditionals, and replace repeated
reachability by a linear graph traversal after reading the dense matrix. These
are measured implementation gains in small-instance tools. They preserve the
target laws and do not finish the general sampler's runtime proof.

The practical priority is now: integrate the proved endpoint correction; close
the physical and finite-bit obligations for the defect chain; finish literal
draw-cost certificates. Further block/nonlocal kernels need exact laws and
complete work accounting. E8 geometry and idle hosting currently provide
inspiration about representation and resource use, with no direct sampling
improvement established.
