# Composed complexity: what is explicit and what remains symbolic

Original source review: October 9, 2026, Pacific time. Verification update: October 10, 2026, Pacific time.

The complete bounded-sampling research overlay now passes **ordinary Lean compilation**. The [compiler checkpoint](outer-sampler-compiler-checkpoint.md) and the [current verification record](../reports/composed-complexity.json) bind the round-10 result: all 13 research modules completed within a 685-module closure, with 684 authenticated object reuses and one fresh successful compilation. The recorded evidence review passed at `2026-10-11T00:09:15.207698+00:00` UTC. The **actual full compiled-environment audit passed**, with 25,448 selected declarations, including 18,054 theorem constants, and 22 exact transitive headline closures across 11,951 imported modules. These counts include pinned upstream and generated/private declarations; they are not counts of new results. Independent AI-agent artifact and semantic reviews also passed. The semantic readback confirms that the final theorem uses the same computed machine, schedule, both branches, and fallback/rejection mass, and reaches the refined \(d^{17}\) chain bound through `PhysicalFiniteWalk.idealOuterLaw_variation`. This is ordinary compilation and environment inspection with the recorded compiler/cache trust boundary. It supplies no strict sampler acceptance, fresh Linux reproduction of the overlay, or promotion into the default aggregate.

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

1. The public binary parser, computed dimension/catalogue and reference selector, complete schedule/word-count program, greedy initialization, and both branches of `LatticeSampler.draw`.
2. The complete canonical dense draw, including fine-margin construction, normalization, exact integer/rational arithmetic, bin walk and offsets, feasibility tests, and its internal fallback; the signed lattice decoder; and every bounded rejection trial.
3. The outer proposal and translated-completion test, capped profile fold and empty-block fold, separate terminal draw, output reconstruction/unpadding, chunking and copying, outer retries, and fallback.
4. Numeric-degree bounds for the reusable composition, pairing, map, fold, capped intermediate-weight, and first-success combinators used to assemble those programs, plus public printing and fresh-word generation.
5. An explicit numerical degree bound on the complete online-work witness, a checked degree transformation for the physical compiler, and the public size conversion. These quantitative bounds must cover the same assembled sources whose polynomial-time existence ordinary-compiles; the additional degree diagnostics have not acquired a compiler pass.

The complete program already has ordinary-compiled polynomial witnesses for these operations; their numerical degrees have not been extracted. The remaining task is to quantify them in one complete cost model. In particular, the pinned [FirstSuccessProgram](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Machines/FirstSuccessProgram.lean) constructs **all** trial results with `List.map` before selecting `firstSome`. Its charged realizer therefore cannot be costed as stopping all later computations at the first successful trial. Full supplied words and intermediate list/tree weights also matter. Schoolbook arithmetic in a separate random-access implementation would require its own cost derivation and would not certify this realizer's physical-machine degree.

The pinned manuscript's [dense implementation discussion](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/dense.tex) accounts qualitatively for polynomial arithmetic and loop counts. This does not supply a degree for the assembled local realizer. This review does not substitute an untracked primitive estimate for that missing degree, and does not derive an exact expected-time sampler or a bounded-table counting theorem from the local bounded-sampling result.

## Upstream revision check

At **2026-10-10 04:50 UTC**, the GitHub primary [main-commit API](https://api.github.com/repos/openai/math/commits/main) reported
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, committed at
`2026-10-08T05:20:00Z`, with the merge message “Update manuscripts and Lean formalizations.”
This is exactly the repository's preserved source pin. Therefore the observed latest `main` has **no revision difference** affecting #115, its manuscripts, or its theorems. The [current #115 scope page](https://github.com/openai/math/blob/main/lean/docs/115.md) still states the bounded-time approximate sampler, exact expected-polynomial sampler for ordinary tables, and companion bounded-table FPRAS. No source pin was updated. This is a dated observation, not a claim about later upstream changes.
