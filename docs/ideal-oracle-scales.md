# A separate ideal-oracle scale frontier

Subsequent [physical repair integration](physical-repair-refinement.md) sharpens this module's valid `640,000d¹⁷` allowance to **`80,000d¹⁷`** for the same reference/selected chain, with `40,000d¹⁷` for its unit branch. The scale and interface results below are unchanged.

This note considers `L=3d`, `U=5d³`, where
`d=10+(m+1)(n+1)`, for the actual parameterized ideal completion chain.
It is separate from the existing dense-compatible choice
`L=32d³`, `U=47d⁵`. Its reference-chain inverse-gap allowance is

\[
 1024\cdot5^4d^{17}=640{,}000d^{17}.
\]

The formal source is [IdealOracleScales.lean](../formal/Math115/IdealOracleScales.lean).
The upstream definitions inspected for this deduction are pinned at
`openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
This is a Lean-verified actual auxiliary-chain theorem.
Its reference theorem has an explicit nonempty-state premise and chosen
large reference row and column. The `feasibleChain_poincare_d17` wrapper
uses the automatic reference/unit branch selector and discharges state
nonemptiness from equal ordinary total margins, including empty index
types. It is not a complete sampler or bit-complexity theorem.

The [new module receipt](../formal/results/ideal-oracle-scales/verification.json)
records successful serial compilation and independent printed-axiom audits
of all 22 named declarations. They use only `propext`, `Classical.choice`,
and `Quot.sound`, or subsets; no `sorryAx` occurs. The source SHA-256 is
`401963282dd1e404c76e6c78555d0fe0387aaf150256638ed1728f20253260bf`.
This local receipt does not extend the earlier Linux verification or
establish strict Comparator replay.

## The two independent scale requirements

The generic theorem `ReducedSmallChain.chain_poincare_polynomial` proves

\[
 \operatorname{Var}_{\pi}H
 \le1024d^5U^4\,\mathcal E(H)
\]

for `U≥2`, `L≥3d`, a nonempty positive-weight physical state space,
and large reference row and column. Its capacity, physical adjacency,
dyadic proposal, ordinary reference-completion counts, exact adjustment,
half acceptance, and stationary energy comparison are part of the chain
construction and proof. It has no dense-bin or finite-bit oracle premise.
The scales here satisfy these scalar conditions. Also, `U≥2L` for `d≥2`,
and the source dimension allowance is always at least 11, including empty
row or column index types.

Unpadding has a separate ordinary-table count requirement. Let `K` be the
marked cells, `g=|K|`, and `e=(m−1)(n−1)` with natural subtraction. The
sequential count theorem and its rational envelope give

\[
 |\Omega_{\mathrm{padded}}|\le2|\Omega_{\mathrm{original}}|
 \quad\hbox{if}\quad47(gL)e\le32(U+1).
\]

Both original incident margins of every marked cell must be at least
`U`. Because `g,e≤mn≤d`, the ideal scales give

\[
 47(gL)e\le141d^3\le160d^3+32=32(U+1).
\]

The formal theorem uses the actual `Table`, `largePadding`, `paddedRows`,
and `paddedColumns` definitions. It needs no equal-total or nonempty-fiber
premise, because it states a natural cardinality inequality; empty fibers
are included. Its specialization chooses `K` to be the actual large
rectangle selected by `firstPaperSmall r c U`. The scale is computed from
the full dimensions before choosing this rectangle, so this selection
has no circular dependence on its own cardinality.

The successful padded-table subtype has exactly the original-table
cardinality, through the actual padding bijection. Thus a uniform draw
from a nonempty enlarged ordinary fiber has unpadding success at least
one half. Conditional on success, subtracting the padding gives the
uniform original-table law.

This does **not** show that a stationary draw from the physical small
chain succeeds with probability one half. That chain contains additional
defect states and uses completion-count weights. The pinned source's
original stationary-success proof combines the padding ratio with a
separate defect-mass factor, yielding a lower bound
`1/[2(1+d²)]`. The subsequent
[stationary-output modules](physical-stationary-success.md) now transfer
those arguments to free scales and prove the sharper actual-cell bound
`1/[2(1+p²)]` at these ideal parameters. They identify the physical chain's
stationary law, prove uniform conditional output, and bound independent
stationary retries. A finite-walk output law and complete finite-bit sampler
remain separate integration work.

## Why the dense-compatible result remains separate

The retained sufficient interface `DenseScaleConditions d A B L`
requires, among other conditions,

\[
 Ad\le B,\qquad
 8d^2B+8d^3A\le AB,\qquad
 2B\le L,\qquad A>0.
\]

From `Ad≤B`, the first term in the normalizer budget satisfies
`8d²B≥8Ad³`. Therefore `16Ad³≤AB`; cancellation of `A>0` gives
`B≥16d³`, hence `L≥32d³`. The existing
`A=16d²`, `B=16d³`, `L=32d³` attains that lower bound.
The new module proves this implication and the incompatibility of
`L=3d` for every positive dimension, irrespective of how `A,B` are retuned.

This is a lower bound imposed by the retained **sufficient interface**.
It is not a lower bound for every dense discretization, completion oracle,
or contingency-table sampler. A different completion implementation or
a stronger geometry proof might avoid these requirements.

## What the exponent comparison means

| Path | Padding `L` | Threshold `U` | Actual reference-chain inverse-gap allowance | Dense interface |
|---|---:|---:|---:|---|
| Existing reduced scales | `32d³` | `47d⁵` | `1024·47⁴d²⁵` | Meets retained sufficient conditions |
| Ideal-only scales | `3d` | `5d³` | `1024·5⁴d¹⁷` | Incompatible for positive `d` |

Both paths use the source's physical-chain constructor with an exact
uniform reference-completion draw. Changing `U,L` changes the auxiliary
state space, its weights, and its completion fibers. The exponent 17 is
a mathematical improvement within this ideal-oracle framework: it is
not a substitution into an unchanged transition matrix, and it does not
require replacing the original uniform-table target law.

If exact completion draws are treated as abstract oracle operations,
the same type of oracle is used along both paths. What is missing at the
new scales is an implementation theorem giving an appropriate cost and
accuracy for those operations. Counting oracle calls alone would hide
that cost. The existing dense-compatible path has its own substantial
unfinished finite-bit integration; this note does not complete either
path.

No measured runtime, general optimality, practical competitiveness,
finite-bit exact-sampling guarantee, counting algorithm, or coverage of
weighted or constrained table models follows from this result. The
formal reference-chain theorem retains its explicit nonempty-state and
reference-row/column hypotheses. The separate automatic-selector wrapper
handles missing-reference branches, and the equal-total wrapper provides
an actual chain for all feasible ordinary margins. Neither wrapper is an
outer sampler output theorem.
