# The encoded completion program

The completion component now has a binary list program with exact finite-word
semantics. Native Lean compilation and strict named axiom checks passed for
**46 declarations across two modules**:
[`CompletionSamplerProgram.lean`](../formal/Math115/CompletionSamplerProgram.lean)
provides the program and its polynomial-cost realizers;
[`CompletionSamplerSemantics.lean`](../formal/Math115/CompletionSamplerSemantics.lean)
identifies its returned matrix with the analyzed table-valued experiment.
The [verification record](../formal/results/completion-program/verification.json)
collects the frozen sources and evidence for this checkpoint, including the
[independent source and native-evidence review](../formal/results/completion-program/source-review.json).


## What the program does

The input is a pair of coarse margin lists, a dimension allowance `d`, a requested
precision `h`, and a Boolean list:

```lean
Math115.CompletionSamplerProgram.draw (((rows, columns), (d, h)), bits)
```

The returned value is a list of matrix rows. The caller supplies neither a
feasible-table witness nor precomputed fine margins, initialization, or fallback.
The program computes

\[
 k=d^{12},\qquad J=4(h+2),\qquad
 h_{\rm fine}=h+2+\lceil\log_2 J\rceil.
\]

For an `a × b` coarse block with margins `R,P`, it enlarges the margins to
`k(R_i+2b)` and `k(P_j+2a)`. Each trial calls the unchanged upstream canonical
dense program at precision `h_fine`. That call computes its own initialization,
margin normalization, and fine-table fallback.

The integer decoder then floors rectangular prefix sums after division by `k`,
takes their mixed differences, and subtracts two from every cell. It checks
nonnegativity before natural subtraction, so a negative decoded cell produces
rejection rather than a truncated zero. For inputs satisfying the conditions below, an accepted matrix has exactly
the coarse margins `R,P`.

The program returns the first accepted trial result. For equal-total margins, if every parsed
trial rejects, it returns a feasible coarse table computed by the upstream
greedy constructor from `R,P`. The list retry realizer evaluates the trials over all
reserved complete words before selecting that first success; this checkpoint
claims no savings from stopping execution early.

## Exact word identification

Let `B` be the canonical dense word width computed from the enlarged margins
and `h_fine`. The program reserves `J B` bits. A full valid reserved source gives
`J` consecutive width-`B` words. Surplus bits add no trials. A short Boolean
list supplies fewer complete trials; the accuracy theorem requires the full
reserved source.

`wordWidth_code`, `bitCount_code`, and `reservedWords_code` identify those
computed widths and chunks with the typed Boolean experiment. `trial_code`
identifies each dense-call-and-decoder result. `draw_code` proves, for every
whole word, that the actual list program returns exactly the matrix encoding
of the analyzed table, including its all-failed fallback.

`draw_prefix_code` extends the identity to any longer word. For a uniform longer
word, taking the required prefix preserves its exact law; the
`padded_programTable_law` theorem consequently allows a common reservation
without adding distribution error.

## Accuracy and cost have different inputs

The accuracy contract uses `a=m+1`, `b=n+1`, nonnegative integer margins and
uniform fair bits. It requires

\[
 d\ge14,\quad a,b\le d,\quad (a-1)(b-1)\le d-1,\quad
 \sum_iR_i=\sum_jP_j,
\]

and the strong residual-margin bounds

\[
 R_i\ge3db,\qquad P_j\ge3da.
\]

Under these hypotheses and the computed word allowance, `draw_semantics`
combines the exact program-output identity with total variation at most
`2^{-h}` from the uniform law on coarse tables. The imported proofs discharge
the fine-law error, equal accepted-fibre counts, constant acceptance bound,
and published analytic inputs. The error includes both the dense program's
own fallback and the completion retry fallback. One-row or one-column blocks
are covered with the full dimension bounds retained; empty blocks are outside
this successor-index accuracy contract.

`polynomial_draw` gives a charged tree-machine execution-cost and encoded
output-weight bound in the **complete encoded input**, including the supplied
Boolean list. It is not a measured runtime or a final sampler exponent.
Generating the reserved fair-bit bank and composing the broader sampler's
cost remain separate work.

This checkpoint identifies completion for the coarse lists passed to the
program. The computed physical list-order bridge, profile walk, terminal
reconstruction, outer retries and schedules, and public sampling machine
remain separate from this two-module result.
