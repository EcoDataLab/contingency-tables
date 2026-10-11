# Composed complexity: what is explicit and what remains symbolic

## Comparable result, in the same public size measure

`Math115.LatticeBoundedSampling.boundedSampling` has exactly the type
`Algorithms.BoundedSamplingStatement`, already proved by pinned upstream
`OAI.ContingencyTables.boundedSampling`. It is an alternative proof using a
different fixed machine and the d¹⁷ route. The existential theorem statement
is unchanged; it does not compare the chosen constants or degrees.

A concrete improvement survives the complete **reserved random-bit bank**
composition. Write `S=m+n+clog₂(M+1)+h+1`, including numeric precision `h≥1`,
and `C₀=12672000000·37^62`:

| Complete route | All reserved fair bits | Numerical machine-time degree |
|---|---|---|
| Pinned upstream | `W ≤ 344^644 S^1288` | `1288·natDegree(P_U)`, still symbolic |
| This repo's compiled d¹⁷ route | `W ≤ C₀·5^85 S^170` | `170·natDegree(P_L)`, still symbolic |
| Dense-compatible d²⁵ chain | No separate assembled bit-bank theorem | Unknown |
| Same compiled rational defect chain: d⁸ generally; d^6.5 at bounded aspect | Frozen older sampler supplies completion availability; new adapter/outer-program composition still open | Unknown |

The two bank bounds use the same `S` and include every reserved transition,
completion retry, terminal draw and unused bit. They are upper allowances,
not optimal exponents or a pointwise runtime comparison. The compiler
polynomials `P_U` and `P_L` belong to different complete programs. The detailed
[schedules and source map](#three-routes-with-the-cost-models-kept-separate)
below make this comparison reproducible without inferring it from gap powers.

For the changed defect chain, the [new actual aggregate theorem](aggregate-defect-trace.md)
has coefficient `34848d⁵s³`, compared with the preceding `3872d⁶s²`,
where `s=m+n−2`. Their old/new ratio is `d/(9s)`; use the minimum.
These are bounds for the same kernel and improve the bounded-aspect exponent
from 7 to 6.5. Both retain exponent 8 for thin shapes. They do not update
either complete bit-bank row above.

Two actual draw certificates remain open: the reference-completion and unit
packed trials. Initialization, fallback construction and retry-word parsing
now join branch selection and printing with exact compiled cost certificates;
the [current field table](#exact-draw-cost-certificates) links each proof and
its evidence. The checked complete count certificate is `e=1008`; the
conditional local runtime degree remains `340·max(1008,t)` until a complete
draw certificate `t` is supplied. These large degree allowances come from
conservative composition helpers. They do not establish optimal exponents,
practical speed or superiority to the unknown upstream degree.

## Compiled baseline and evidence

Original source review: October 9, 2026, Pacific time. Verification update: October 11, 2026, Pacific time.

The complete bounded-sampling research overlay now passes **ordinary Lean compilation**. The [compiler checkpoint](outer-sampler-compiler-checkpoint.md) and the [current verification record](../reports/composed-complexity.json) bind the round-10 result: all 13 research modules completed within a 685-module closure, with 684 authenticated object reuses and one fresh successful compilation. The recorded evidence review passed at `2026-10-11T00:09:15.207698+00:00` UTC. The **actual full compiled-environment audit passed**, with 25,448 selected declarations, including 18,054 theorem constants, and 22 exact transitive headline closures across 11,951 imported modules. These counts include pinned upstream and generated/private declarations; they are not counts of new results. Independent AI-agent artifact and semantic reviews also passed. The semantic readback confirms that the final theorem uses the same computed machine, schedule, both branches, and fallback/rejection mass, and reaches the refined \(d^{17}\) chain bound through `PhysicalFiniteWalk.idealOuterLaw_variation`. This is ordinary compilation and environment inspection with the recorded compiler/cache trust boundary. These checkpoint receipts supply no strict sampler acceptance or fresh Linux verification of the expanded default target. The byte-identical proved sources are now [promoted into the default root](default-target-integration.md). A separate [fresh hosted Linux receipt at `5b4af40`](../formal/results/linux-focused-5b4af40/README.md) verifies that expanded target; it does not supply a numerical complete runtime degree or strict sampler acceptance.

`PublicLatticeSampler.machineTime_public_bound` and `LatticeBoundedSampling.boundedSampling` have passing ordinary compiler bindings. Their statements provide one fixed public machine and one uniform polynomial execution bound for ordinary equal-total natural margins, all dimensions, and numeric precision \(h\ge1\), with feasible output on every tape and total variation at most \(2^{-h}\). This is a complete bounded-sampling statement, not a new exact expected-time sampler or bounded-table counting result.

The [archived pre-compilation appendix](composed-complexity-uncompiled-appendix.md) preserves the original proposed-source excerpts, warnings, and hashes. Its creation-time uncompiled status is historical. The original 20-file hash snapshot remains unchanged; current source and compiler bindings are recorded separately. The old draft comments are not current verification receipts.

The ordinary-compiled bound establishes uniform polynomial-time existence but does **not** extract a numeric complete runtime exponent. Its proof chooses

\[
 D_{\mathrm{time}}=170\,\operatorname{natDegree}(P_L),\qquad
 C_{\mathrm{time}}=P_L(A_L)+1,
\]

where

\[
 A_L=12672000000\cdot37^{62}\cdot5^{85}+91
\]

and \(P_L\) is the polynomial supplied by the physical-machine compiler for this particular sampler. The number 170 bounds the input allowance plus the reserved fair-bit bank. It is not the degree of that compiler polynomial. The ideal-chain powers 17 and 25 are also different quantities.

There is a useful further source-level calculation: if the **complete online realizer**, including fresh bits and final encoded output, has a work polynomial of degree \(e_L\), the pinned compiler gives a physical-time polynomial of degree at most \(2\max(1,e_L)\). Consequently one honest composed envelope is

\[
 \boxed{\quad T_L(r,c,h)\le (Q_L(A_L)+1)\,
 S^{340\max(1,e_L)}.\quad}
\]

Here \(Q_L\) is the compiler's constructed polynomial. This is a conditional algebraic degree transformation, with a named unknown \(e_L\); it supplies no numerical degree. The complete program's ordinary-compiled polynomial witnesses now support polynomial-time existence. The additional \(340\max(1,e_L)\) transformation remains a source-level calculation: it has not been compiled as a new degree theorem, and the [archived failed or uncompiled degree diagnostics](../research/runtime-degree/README.md) are preserved. Ordinary compilation of the sampler does not turn this transformation into a certified numerical exponent.

## Checked generic degree helpers

The [generic-helper checkpoint](../research/runtime-degree/checkpoints/generic-helpers-v1/) now records ordinary native compilation of seven quantitative helper modules and two separate standard-axiom named audits of 47 and 21 declarations. Recorded dependency objects and the official cache were reused. This scope is separate from the complete sampler's environment audit. The earlier failed and uncompiled [degree archive](../research/runtime-degree/README.md) remains unchanged.

The earlier checked `Math115.DegreeBounds.machineTime_degree` theorem follows the actual pinned finite-word compiler. Given degree certificates \(e\) for its complete word-count realizer and \(t\) for its complete supplied-word public draw, it bounds physical machine time by a polynomial of degree at most

\[
 2\max(1,t)\max(e,6)
\]

in `wordMeasure = weight(input) + numeric bit count`, including fresh-bit generation and final encoded output. The later [actual count/draw helper checkpoint](../research/runtime-degree/checkpoints/actual-count-draw-helpers-v1/) certifies the exact complete count realizer with \(e=1008\); the numerical draw certificate \(t\) remains missing. Substituting its checked public \(S^{170}\) allowance gives \(340\max(1,t)\max(e,6)\) in \(S\). This earlier multiplicative conversion has a separate [ordinary-compiled conditional public-degree theorem](../research/runtime-degree/checkpoints/public-sampler-degree-v1/), with its three-name audit and retained failed first attempt. The earlier \(340\max(1,e_L)\) expression uses a different hypothesis: a degree bound for the already complete online-work witness.

The earlier `PublicSamplerDegree.fixedMachineBoundedSampling_with_degree` theorem uses the existing `PublicLatticeSampler.machine` and `Algorithms` input/output definitions. Given certificates for the actual `wordCountRealizer` and `publicDrawRealizer`, one positive constant works uniformly over every pair of dimensions, equal-total natural margins and numeric precision \(h\ge1\). At time \(C S^{340\max(1,t)\max(e,6)}\), every tape produces a feasible table and the uniform-bit output law has total variation at most \(2^{-h}\). Here word count means the number of reserved random bits, not the number of feasible tables. The compilation reused authenticated native prerequisites; it is separate from the default-target Linux audit and strict Comparator checking. At that checkpoint, both numerical realizer certificates were left open. The later actual helper packet discharges the count premise with `e=1008`; the draw premise remains unresolved.

The checked `typed_actual_fixedPower` result gives degree at most six for `LatticeScheduleProgram.fixedPowerRealizer k` for **each fixed** \(k\). Its polynomial coefficient may depend on \(k\); it is not a uniform bound for a runtime-variable exponent. These helpers supply reusable degree transformations and scalar seeds. The later actual helper packet supplies the complete count certificate `e=1008`; the complete draw degree, measured performance, fresh Linux acceptance of this quantitative packet and strict sampler acceptance remain open.

## Sharper conditional degree from affine output

The newer [affine refinement](../research/runtime-degree/checkpoints/affine-public-sampler-degree-v1/) preserves the exact `PublicLatticeSampler.machine`, complete `wordCountRealizer` and `publicDrawRealizer`, and the `Algorithms` input/output codecs. Its `AffinePublicSamplerDegree.fixedMachineBoundedSampling_with_degree` theorem replaces the earlier multiplicative envelope by

\[
 \boxed{D=340\max(\max(e,6),t).}
\]

Here \(e\) certifies the actual complete reserved-bit-count routine and \(t\) the complete supplied-word public draw. The exact complete count certificate is now verified with \(e=1008\) in the [actual helper packet](../research/runtime-degree/checkpoints/actual-count-draw-helpers-v1/); \(t\) remains unresolved. The current conditional envelope is \(D=340\max(1008,t)\), not a complete numerical exponent. Given those certificates, one positive coefficient \(C\) works uniformly for all finite dimensions, equal-total natural margins, including zeros and empty dimensions, and numeric \(h\ge1\). At \(C S^D\), every tape halts with a feasible table; independent uniform fair bits give total variation at most \(2^{-h}\) from uniform ordinary fixed-margin tables. The companion `machineTime_public_degree` theorem bounds that same machine's execution time.

The improvement separates computation cost from output size. The fresh Boolean word has exactly the reserved number of bits, regardless of how expensive computing that number was. With \(w=\operatorname{weight}(input)+\text{numeric bit count}\), the preserved-input/word pair fed into the draw has weight at most \(4w+2\). The online degree is therefore \(\max(\max(e,6),t)\), rather than a product of the count and draw work degrees. The unchanged physical compiler doubles it; the existing public \(S^{170}\) conversion yields the factor 340. This sharper bound is proved no larger than the preserved earlier bound, but supplies neither a numerical exponent nor measured practical speed.

The two affine source modules passed ordinary native compilation, and their ordered six-name and four-name axiom checks passed. Independent AI saved-artifact review passed. This helper evidence is separate from the expanded default Linux receipt and strict Comparator acceptance; the earlier packets and failed attempts remain unchanged.

## Exact draw-cost certificates

The [historical seven-field handoff](../research/runtime-degree/checkpoints/actual-count-draw-helpers-v1/README.md#remaining-numerical-draw-certificates)
names the unchanged realizers required by `ActualDrawSeams`. Current results
bound charged work **plus encoded output** on every input in each realizer's
typed codec domain. They do not assume feasibility, successful acceptance or
the desired runtime bound.

| Field | Certified degree at most | Exact program and evidence |
| --- | ---: | --- |
| `branch` | 1008 | [Branch selection](../research/runtime-degree/checkpoints/actual-branch-degree-v1/); arbitrary natural margin lists; 20-name audit |
| `printer` | 4 | [Matrix printer](../research/runtime-degree/checkpoints/actual-printer-degree-v1/); arbitrary ragged or empty natural matrix lists; 25-name audit |
| `initial` | 4032 | [Initial configuration](../research/runtime-degree/checkpoints/actual-initial-degree-v1/); arbitrary natural margin lists and precision |
| `fallback` | 18 | [Named initial fallback](../research/runtime-degree/checkpoints/actual-initial-degree-v1/); the exact original greedy table program |
| `retryWords` | 42914304 | [Retry-word parser](../research/runtime-degree/checkpoints/actual-retry-degree-v1/); all `RetryData`, including zero widths and short/surplus words; 25-name audit |
| `referenceTrial` | **Open** | Exact `LatticeOuterProgram.packedTrialRealizer`, including the complete dense completion backend |
| `unitTrial` | 272019144737569436269241336269647035188617216 | [Exact unit packed trial](../research/runtime-degree/checkpoints/actual-unit-degree-v1/); original neighbor/filter/dedup, guarded walk, word parsing and output reconstruction on every literal input |

The initialization packet's compiled-environment audit checks five complete
headline closures; the retry packet has focused transitive type/axiom checks
and also supplies exact division/quotient degree 4. Separate AI source reviews
passed. The unit packet closes its exact named field with six final
transitive axiom/type readbacks and a separate AI source review. Its very
large degree comes from conservative proof composition; it does not describe
observed execution time or a best possible exponent. The newly owned sources
compiled locally with pinned Lean 4.34.1 and
authenticated reused imports. These packets do not expand the historical
default-target Linux or strict Comparator receipts. Prepared public
reproduction commands are distinguished from executions actually recorded.

The complete count certificate covers computing the reserved-bit number and
encoding it in binary for every literal input. It does not bound generating
the full numeric bank by degree 1008. After the remaining reference-trial
certificate is obtained, the exact complete draw must be assembled and
its degree inserted into the public-machine theorem.

## A common public size measure

Use the original sampling statement's parameters:

\[
 M=\sum_i r_i=\sum_j c_j,\qquad
 d=10+(m+1)(n+1),\qquad
 S=m+n+\operatorname{clog}_2(M+1)+h+1,
 \quad h\ge1.
\]

\(\operatorname{clog}_2\) is the natural-number ceiling binary logarithm. The public input is the binary encoding of both margin lists and \(h\). Nevertheless the complexity measure contains the **numeric value of \(h\)**, as required for error at most \(2^{-h}\). A polynomial in \(S\) is therefore not a polynomial in the literal input length alone when \(h\) varies. Equal totals are needed to control the column encoding using the row total. These definitions and premises are in the pinned [AlgorithmStatements](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/AlgorithmStatements.lean) and [PublicInputLength](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Machines/PublicInputLength.lean).

The local reservation uses another measure,

\[
 b_0=\operatorname{clog}_2(M+2),\qquad N=d+b_0+h+3.
\]

The existing [CompletionPublicSize](../formal/Math115/CompletionPublicSize.lean) module proves \(N\le5S^2\); the [input-size verification note](completion-input-size.md) records its checked scope alongside [CompletionEncodingSize](../formal/Math115/CompletionEncodingSize.lean). These scalar size bounds alone do not verify the assembled sampler; the complete-program result has its separate round-10 ordinary compiler evidence. A power in \(N\) and a power in \(S\) cannot be compared without this conversion. Likewise, a chain bound in \(d\) is not already a runtime bound in \(S\).

## Preserve the mixing, retry, and inner-work factors

For the current \(d^{17}\) route set \(U=5d^3\), \(L=3d\), and let \(p\le d\) be its actual number of small cells. The compiled program's scalar schedule is

\[
 \begin{aligned}
 K&=80000d^{17},& B&=M+dL+U+3=M+3d^2+5d^3+3,\\
 R&=2(1+p^2)(h+3),\\
 \ell&=h+3+\operatorname{clog}_2R+2d\operatorname{clog}_2B,&T&=K\ell,\\
 t_s&=h+3+\operatorname{clog}_2R+\operatorname{clog}_2T,\\
 t_t&=h+3+\operatorname{clog}_2R.
 \end{aligned}
\]

The factor \(2d\operatorname{clog}_2B\) pays for the logarithm of the mass allowance \(B^{2d}\). Omitting it changes the mixing schedule. A single inverse-gap bound supplies \(K\); it does not supply \(T\), \(R\), the precision of each approximate completion, or the work of a transition. See [CompletionScheduleArithmetic](../formal/Math115/CompletionScheduleArithmetic.lean) and [CompletionOuterSchedule](../formal/Math115/CompletionOuterSchedule.lean).

One completion reserves

\[
 \begin{aligned}
 C_f&=d^{12}(M+3d^2+2d),&b_f&=\operatorname{clog}_2(C_f+2),\\
 J(t)&=4(t+2),&q(t)&=t+2+\operatorname{clog}_2J(t),\\
 F(t)&=J(t)\,25(d+b_f+q(t)+1)^{62}.
 \end{aligned}
\]

This includes the lattice-completion rejection bank and the pinned dense sampler's full supplied word. The proposal reservation is \(s_d=\operatorname{clog}_2(32d^2)\). The full outer bank is

\[
 W=R\bigl[T(s_d+F(t_s))+F(t_t)\bigr].
\]

It reserves words for every transition and every trial, including holdings, rejected trials, and unused words. It measures reserved bits, not expected bits inspected. The formulas are in the existing [CompletionRandomBudgetArithmetic](../formal/Math115/CompletionRandomBudgetArithmetic.lean) and [CompletionRetryBudget](../formal/Math115/CompletionRetryBudget.lean) modules. The ordinary-compiled public interface obtains the bank through `LatticeScheduleProgram.totalBits` after parsing the margin lists and identifies it with these scalar formulas. The [archived appendix](composed-complexity-uncompiled-appendix.md) records the earlier source presentation; the current result has passed the full compiled-environment audit and actual semantic readback.

The arithmetic bounds retain all these factors:

\[
 \begin{aligned}
 R&\le4d^2(h+3),&T&\le480000d^{18}N,\\
 t_s&\le21N,&t_t&\le2N,\\
 F(t_s),F(t_t)&\le2200\,37^{62}N^{63},\\
 W&\le C_0d^{20}(h+3)N^{64}\le C_0N^{85},\\
 C_0&=3\cdot4\cdot480000\cdot2200\cdot37^{62}
       =12672000000\cdot37^{62}.
 \end{aligned}
\]

The power calculation is \(2+18=20\), followed by one \(N\) from \(T\) and 63 from the inner bank, then \(20+1+64=85\). Applying \(N\le5S^2\) yields the retained public bank bound

\[
 \boxed{W\le12672000000\cdot37^{62}\cdot5^{85}\,S^{170}.}
\]

The literal-symbol allowance adds

\[
 \operatorname{wordMeasure}
 =18\,\operatorname{length}(\operatorname{encodeSamplingInput})+1+W
 \le A_LS^{170}.
\]

The 91 is \(18\cdot5+1\), using the original bound on literal input length. These are conservative upper allowances; no matching lower bound or optimal exponent follows. The [input-size note](completion-input-size.md) separately records the supplied-word tree input envelope
\(I(X)=4X+4C_0\,2^{85}X^{170}\).

## Three routes, with the cost models kept separate

| Quantity | Pinned upstream sampler | Local dense-compatible \(d^{25}\) chain | Local \(d^{17}\) lattice route |
| --- | --- | --- | --- |
| Auxiliary scales | \(U=d^{20}, L=d^{12}\) | \(U=47d^5, L=32d^3\) | \(U=5d^3, L=3d\) |
| Ideal inverse-gap allowance | \(98560d^{126}\), weakened to \(d^{160}\) for the source schedule | Refined selected/reference bound \(128\cdot47^4d^{25}\) | Refined selected/reference bound \(80000d^{17}\) |
| Outer walk and retries | \(T=d^{200}(h+b)^2\), \(R=d^4(h+1)\), inner precision \(d^4(h+b)^2\) | No separate complete literal sampler/schedule theorem at these scales is identified here | \(T=80000d^{17}\ell\), \(R=2(1+p^2)(h+3)\), distinct \(t_s,t_t\) as above |
| Total reserved fair-bit bank | \(W_U\le(d+b+h+100)^{644}\) | No instantiated full-bank bound for this route is identified here | \(W_L\le C_0N^{85}\) |
| Public input conversion | \(d+b+h+100\le344S^2\), hence \(W_U\le344^{644}S^{1288}\) | \(d=10+(m+1)(n+1)\); a dimension conversion alone supplies no completion cost | \(N\le5S^2\), hence \(W_L\le C_0 5^{85}S^{170}\) |
| Per transition / dense draw | Polynomial finite-bit program; complete numeric work degree is not exposed by the cited public theorem | Exact completion draws in the chain are oracle operations; retained sufficient dense-interface conditions are compatible | Supplied-word completion draw, decoder, proposal, translation, capped fold, and retry realizers have ordinary-compiled polynomial witnesses; numerical degree composition is not extracted |
| Complete bounded physical-machine time | \((P_U(A_U)+1)S^{1288\operatorname{natDegree}(P_U)}\), \(A_U=344^{644}+91\); degree symbolic | No complete machine-time theorem for a newly instantiated route | Ordinary-compiled \((P_L(A_L)+1)S^{170\operatorname{natDegree}(P_L)}\); degree symbolic; actual full environment audit and semantic readback passed |
| Exact expected-time sampling | Source has a separate exact correction construction and expected-polynomial statement | No new exact sampler derived here | No new exact sampler or counting extension in this bounded-sampling result |

The upstream \(b\) is its `smallBinaryLength`, not \(b_0\):
\(b=d+\operatorname{clog}_2(M+d^{13}+d^{20}+4)\), with a proved bound \(b\le21d+\operatorname{clog}_2(M+1)+2\). The upstream bank and conversion are from pinned [FirstPaperWordBudget](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/FirstPaperWordBudget.lean), [FirstPaperBinaryParameters](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/FirstPaperBinaryParameters.lean), and [FirstPaperInputWordBudget](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/FirstPaperInputWordBudget.lean). Its public degree is in pinned [AllSamplingMachine](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/AllSamplingMachine.lean).

The gap comparison uses the sampling manuscript's [algorithms section](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/algorithms.tex) and local [repair refinement](physical-repair-refinement.md). The smaller-scale route uses dilation and rejection to obtain a completion implementation; replacing \(L\) by \(3d\) in the old sufficient dense interface alone would fail. Compatibility of the \(d^{25}\) chain with that interface does not establish an assembled sampler's time bound.

**The two symbolic degrees belong to different complete programs.** The bound \(170\operatorname{natDegree}(P_L)\) cannot be declared smaller than \(1288\operatorname{natDegree}(P_U)\) without controlling both polynomials. Likewise, oracle inverse gaps, reserved random bits, charged typed work, physical-machine steps, and measured latency are not interchangeable. This note makes no measured runtime comparison.

## The compiler degree can be traced, but the program degree is still needed

The pinned [FiniteWordExecution](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Machines/FiniteWordExecution.lean) establishes a work bound for the complete online experiment, including declared-word generation and the deterministic draw. Let a particular witness be

\[
 G.\operatorname{cost}(a)
 +\operatorname{worst}_{G(a)}\operatorname{weight}(\text{output})
 \le p(\operatorname{wordMeasure}(a)),\qquad e=\operatorname{natDegree}(p).
\]

The source's [FiniteWordMachine](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Machines/FiniteWordMachine.lean) constructs

\[
 Q=p_{\mathrm{pack}}+p\,f_{\mathrm{stack}}+p_{\mathrm{out}}.
\]

The fixed program's stack-access count, stack overhead, packing width, and transition-table costs are constants in this polynomial. The elementary block-map polynomial in pinned [LiteralProgram](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Machines/LiteralProgram.lean) is

\[
 \operatorname{budget}_{w,H}(u,v)
 =(u+1)\bigl[3+w+H+2(v+u(H+w))\bigr].
\]

Consequently \(p_{\mathrm{pack}}\) has degree at most 2, \(f_{\mathrm{stack}}\) at most \(\max(1,e)\), and \(p_{\mathrm{out}}\) at most \(2e\). Thus

\[
 \operatorname{natDegree}(Q)
 \le\max\bigl(2,e+\max(1,e),2e\bigr)
 =2\max(1,e).
\]

No physical compiler primitive is omitted from this degree calculation: it covers packing, the online realizer, the stack execution factor, tape erasure, and unpacking/printing. Applying the public word-measure envelope then gives the displayed \(340\max(1,e_L)\) bound. Applying the same reasoning to upstream instead gives \(2576\max(1,e_U)\), with its **separate** online-work witness. Neither is a numeric runtime claim.

The ordinary-compiled `LatticeSamplerCost.reserved_draw_work` theorem addresses a different seam. Its repaired proof first specializes the existing `CompletionEncodingSize.reserved_program_work` theorem through `reserved_work_of_polynomial`, then applies it to the actual sampler realizer. If \(Q_d\) bounds deterministic supplied-word tree work, the generic theorem composes \(Q_d\) with \(I\). This gives an analytical degree bound of at most \(170\operatorname{natDegree}(Q_d)\) in encoded margin weight plus numeric precision. It pays for the supplied bank but does not itself acquire random bits, parse and print the literal public interface, or perform the physical-machine conversion. The ordinary-compiled `reserved_draw_work_literal` uses an affine change to literal margin length plus numeric \(h\); that does not multiply the degree again. The [appendix](composed-complexity-uncompiled-appendix.md) retains the earlier uncompiled proof attempt; current source hashes and ordinary compiler bindings are separate in the [report](../reports/composed-complexity.json).

## What a numerical complete degree would require

The existential `PolynomialTime` API is not itself an error: it states that one fixed polynomial controls every relevant input, not a polynomial chosen separately for each input. But obtaining a numeric degree from its existence alone is invalid. The missing quantitative artifact is a **named complete work polynomial with a proved numerical degree bound**, or a degree-tracked composition theorem producing one.

The remaining numerical degree accounting must include:

1. Greedy initialization, the actual branch selector, and both branches of `LatticeSampler.draw`, retaining the accepted parser/catalogue/schedule certificates and complete word-count certificate `e=1008` wherever their exact composition signatures apply.
2. The complete canonical dense draw, including fine-margin construction, normalization, exact integer/rational arithmetic, bin walk and offsets, feasibility tests, and its internal fallback; the signed lattice decoder; and every bounded rejection trial.
3. The outer proposal and translated-completion test, capped profile fold and empty-block fold, separate terminal draw, output reconstruction/unpadding, chunking and copying, outer retries, and fallback.
4. Numeric-degree bounds for the reusable composition, pairing, map, fold, capped intermediate-weight, and first-success combinators used to assemble those programs, plus public printing and fresh-word generation.
5. A numerical certificate for the exact complete public-draw realizer `t`. The exact complete count premise now has certificate `e=1008`; the compiler/fresh-bit helpers, affine public-size conversion and actual branch test are already checked. The remaining draw certificate must cover the same assembled source, actual codec and output weight, including all six unresolved seams.

The complete program already has ordinary-compiled polynomial witnesses. The count, parser and selected schedule/helper degrees now have numeric certificates; the complete supplied-word draw still needs a numerical degree in the same cost model. In particular, the pinned [FirstSuccessProgram](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Machines/FirstSuccessProgram.lean) constructs **all** trial results with `List.map` before selecting `firstSome`. Its charged realizer therefore cannot be costed as stopping all later computations at the first successful trial. Full supplied words and intermediate list/tree weights also matter. Schoolbook arithmetic in a separate random-access implementation would require its own cost derivation and would not certify this realizer's physical-machine degree.

The pinned manuscript's [dense implementation discussion](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/dense.tex) accounts qualitatively for polynomial arithmetic and loop counts. This does not supply a degree for the assembled local realizer. This review does not substitute an untracked primitive estimate for that missing degree, and does not derive an exact expected-time sampler or a bounded-table counting theorem from the local bounded-sampling result.

## Upstream revision check

At **2026-10-10 04:50 UTC**, the GitHub primary [main-commit API](https://api.github.com/repos/openai/math/commits/main) reported
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, committed at
`2026-10-08T05:20:00Z`, with the merge message “Update manuscripts and Lean formalizations.”
This is exactly the repository's preserved source pin. Therefore the observed latest `main` has **no revision difference** affecting #115, its manuscripts, or its theorems. The [current #115 scope page](https://github.com/openai/math/blob/main/lean/docs/115.md) still states the bounded-time approximate sampler, exact expected-polynomial sampler for ordinary tables, and companion bounded-table FPRAS. No source pin was updated. This is a dated observation, not a claim about later upstream changes.
