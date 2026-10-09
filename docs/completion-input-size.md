# Completion input size and reserved-bank bounds

Two compiled modules connect the completion reservation to encoded margin
lists and to the parameters in the public sampling statement. They also give
a generic composition rule for a supplied polynomial-time deterministic
realizer. Precision is measured by the **numeric value of `h`** throughout.
Degree **170** describes a reserved-bank bound after changing the size
measure; a sampler's runtime degree would require a separate cost theorem.

## Encoded margins and the supplied Boolean word

In [CompletionEncodingSize.lean](../formal/Math115/CompletionEncodingSize.lean),
the margins `a` are a pair of natural-number lists. Let

\[
 E=\operatorname{weight}(a),\qquad
 s=E+h+3,\qquad
 d=10+(\operatorname{length}(a_1)+1)(\operatorname{length}(a_2)+1),\qquad
 M=\operatorname{sum}(a_1).
\]

Here `weight` is the existing tree-encoding cost measure. The module proves
`E≥3`, `s≥6`, `d≥11`, `d≤10+E²`, and `clog₂(M+2)≤E`, including empty margin
lists and `h=0`. Thus the combined measure from the
[reservation arithmetic](completion-schedules.md) obeys

\[
 N=d+\operatorname{clog}_2(M+2)+h+3\le2s^2.
\]

Write `C=12672000000·37⁶²` for the reservation coefficient and `W` for the
entire reserved Boolean bank. With the explicit scalar premise `p≤d`,

\[
 W\le C\,2^{85}s^{170}.
\]

For a supplied Boolean list `bs` with `length(bs)≤W`, the complete
deterministic tree input satisfies

\[
 \operatorname{weight}(((a,h),bs))
 \le I(s),\qquad I(X)=4X+4C\,2^{85}X^{170}.
\]

This pays for the whole supplied word, even when execution would inspect
only part of it. The margin-size facts do not require equal totals or a
feasible table. Literal margin encoding gives the additional bridge
`E≤4·length(encodeMargins r c)` and hence
`s≤4·(length(encodeMargins r c)+h+3)`.

## The public parameter bound

For rows `r : Fin m → ℕ`, columns `c : Fin n → ℕ`, and `h≥1`, let

\[
 S=\operatorname{samplingSize}(n,r,h)
  =m+n+\operatorname{clog}_2(M+1)+h+1,\qquad M=\sum_i r_i.
\]

[CompletionPublicSize.lean](../formal/Math115/CompletionPublicSize.lean)
proves `N≤5S²` for the original dimensions. For supplied `p≤d`, this gives

\[
 W\le C\,5^{85}S^{170}.
\]

When the **row and column totals are equal**, the literal-input bound is

\[
 18\,\operatorname{length}(\operatorname{encodeSamplingInput}(r,c,h))+1+W
 \le (C\,5^{85}+91)S^{170}.
\]

The equal-total premise lets the row total also bound the column words.
The displayed quantity combines the literal-input allowance and reserved
bit count. It is separate from the preceding tree encoding of
`((a,h),bs)`, and does not instantiate a public parser, printer, or random
machine.

## Generic cost composition

`CompletionEncodingSize.reserved_program_work` assumes an arbitrary supplied
deterministic realizer `F` of a function `f`, together with a
`PolynomialTime F` witness. If that witness bounds cost plus encoded output
weight by `Q`, composition gives `P=Q∘I` and

\[
 F.\operatorname{cost}(((a,h),bs))+
 \operatorname{weight}(f(((a,h),bs)))\le P(s).
\]

The theorem applies to every supplied word within the reservation. It
preserves both the execution-cost and output-weight terms. It neither
supplies the realizer nor proves that a particular sampler has the needed
polynomial-time witness. Uniform randomness, coin generation, total
variation accuracy, and public-machine execution require separate
composition.

## Verification and reproduction

The actual source modules compiled locally with Lean **4.34.1**. All
**25+7=32 declarations** passed exact named standard-axiom checks: every
report appears once in driver order, the output contains no other compiler
text, and only `propext`, `Classical.choice`, and `Quot.sound` occur. Both
final compile logs are empty. The
[verification receipt](../formal/results/completion-input-size/verification.json)
preserves source, object, compiler, driver, and log hashes; the
[independent review](../formal/results/completion-input-size/source-review.json)
checks the frozen evidence and mathematical contracts.

The pins are OpenAI `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Direct local compilation reused
existing pinned dependency objects and the official package cache. The
encoding checkpoint restored `AlgorithmStatements` and `PublicInputLength`;
the public-size checkpoint needed no additional prerequisite restoration.
This was not a fresh dependency-closure build, cross-host reproduction, or
Comparator replay. Python tests and benchmark measurements remain separate
evidence.

With the [pinned environment](formal-verification.md) and dependencies
available, the sources can be compiled and audited from `formal/`:

```sh
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean \
  -j1 -DautoImplicit=false \
  -o .lake/build/lib/lean/Math115/CompletionEncodingSize.olean \
  Math115/CompletionEncodingSize.lean
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean \
  -j1 -DautoImplicit=false results/completion-input-size/EncodingSizeAxiomCheck.lean
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean \
  -j1 -DautoImplicit=false \
  -o .lake/build/lib/lean/Math115/CompletionPublicSize.olean \
  Math115/CompletionPublicSize.lean
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean \
  -j1 -DautoImplicit=false results/completion-input-size/PublicSizeAxiomCheck.lean
```

The compiled checkpoint covers encoding arithmetic, supplied-bank bounds,
and generic deterministic cost composition. It does not establish a
complete physical sampler cost theorem or `BoundedSamplingStatement`.
