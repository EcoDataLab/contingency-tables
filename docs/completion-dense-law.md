# Dense completion on the physical reference fibres

The compiled dense-completion family now supplies the fine-table law used by
lattice decoding and bounded retries. Its accuracy follows from the pinned
analytic proofs and the actual physical residual margins. The resulting
completion error bound holds at every physical state and admissible choice
of reference row and column. A further theorem inserts these families into
the normalized outer walk law at the ideal scales.

This checkpoint verifies **66 declarations** across three modules. It closes
the supplied fine-law accuracy premise for this family. Identifying the
final concrete encoded walker and proving its public-machine runtime remain
separate work.

## From a Boolean word to a completion law

[DenseLatticeCompletion.lean](../formal/Math115/DenseLatticeCompletion.lean)
enlarges the reference margins by `d¹²`, draws a fine table from a fixed
Boolean word, and preserves the original finite cell order when reindexing
the dense draw. The fine draw agrees with the canonical dense draw's matrix
code.

For accuracy exponent `h≥0`, the inner retry schedule is

\[
 J=4(h+2),\qquad q=h+2+\operatorname{clog}_2J.
\]

`completionDraw` partitions one whole Boolean word into the fine-draw words
for these retries. `completionDraw_law` proves that a uniform whole word
induces exactly `completionLaw`, including the fallback mass when all
trials fail. The law is normalized; failed mass is neither discarded nor
conditioned away.

The reusable dense theorem retains explicit input conditions: `d≥14`,
equal residual totals, a feasible fallback, row and column dimension bounds,
`m*n≤d−1`, and the lower margins
`Rᵢ≥(n+1)·3d`, `Pⱼ≥(m+1)·3d`. In
[DenseLatticeCompletionProvedInputs.lean](../formal/Math115/DenseLatticeCompletionProvedInputs.lean),
the exact finite-box Prékopa–Leindler and finite-Cheeger propositions are
discharged by their unchanged pinned proofs. The resulting completion law
and its uniform-word pushforward have total-variation distance at most
`2⁻ʰ` from the uniform ordinary-table law. Fine-law accuracy and those
analytic propositions are no longer assumptions of these three wrappers.

## Every physical reference choice

[PhysicalLatticeCompletion.lean](../formal/Math115/PhysicalLatticeCompletion.lean)
uses `L=3d` and `U=5d³`, with the original dimension allowance
`d=10+(|I|+1)(|J|+1)`. It reindexes each actual reference completion block,
proves its totals, dimensions and residual-margin bounds, then maps the
completion law back through an exact table equivalence.

`finiteFallback` is `GreedyFeasibleTable.table` on those reindexed residual
margins, using their proved equal totals. It supplies an actual feasible
table inside the law. The surrounding representations are in a
`noncomputable section`; in particular, reference indexing uses
`Fintype.equivFin`. This law representation and the verified canonical
dense code identity do not yet provide an executable encoded outer walker
or its cost witness.

`denseOracle_accuracy` proves, uniformly over every state `z` and
admissible reference pair `i₀,j₀`,

\[
 \operatorname{TV}(\operatorname{denseOracle}(h;i_0,j_0,z),
                  \operatorname{Uniform}(\operatorname{ReferenceTable}(i_0,j_0,z)))
 \le 2^{-h}.
\]

The selected transition error is at most `γ·2⁻ʰ`, where `γ` is
`proposalAllowance d`; a fresh selected terminal completion has error at
most `2⁻ʰ`. Empty large-block branches retain the exact unit transition law
and unique terminal completion.
The common fine-row bound and reserved word widths are also independent of
state and reference choice. They bound reserved bits, without asserting a
machine runtime.

## The instantiated outer law

For balanced original margins, a supplied feasible outer fallback, and
natural `T,R,hStep,hTerminal`, `denseOuterLaw_variation` proves

\[
 \operatorname{TV}(\operatorname{denseOuterLaw},\operatorname{Uniform}(\operatorname{Table}(r,c)))
 \le e^{-R/S}+R B e^{-T/K}
       +R\bigl(T\gamma 2^{-h_{\rm step}}+2^{-h_{\rm terminal}}\bigr).
\]

Here `S=successAllowance`, `B=massAllowance`, and the ideal walk allowance
is **`K=80000d¹⁷`**. Both transition and fresh terminal positions use the
proved dense completion family. The formula accounts for outer retry
failure, walk mixing, transition approximation, and terminal approximation.
It is a theorem about the finite probability law; the compiled concrete
Boolean walker, parser/printer and public random machine still need their
own identification and composition proofs.

## Verification evidence

The frozen actual sources compiled with pinned Lean **4.34.1** on native
Windows. All **25+3+38=66 declarations** passed exact named standard-axiom
audits, with report-only output and only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` occurs. The
[verification receipt](../formal/results/completion-dense-law/verification.json)
preserves source, object, dependency, compiler, driver and log hashes, with
sanitized command and runtime provenance. The
[independent source review](../formal/results/completion-dense-law/source-review.json)
checks the contracts and frozen evidence.

The compile logs retain four linter warnings: two `letI` style suggestions
in the dense module, and an unused section-variable warning plus a `letI`
suggestion in the physical module. The proved-input module's compile log
is empty. Public warning logs replace only private source-location paths;
their raw native hashes and sanitized-copy hashes are both recorded. The
audit drivers and audit logs are byte-identical copies of executed evidence.

The pins remain OpenAI `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Dependency-aware compilation and
auditing used isolated native objects and the trusted official package
cache. These three successful module receipts do not certify every draft
in the surrounding build. No complete public-machine sampler theorem,
fresh full-closure replay, or practical runtime measurement is claimed.
