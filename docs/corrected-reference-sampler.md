# Corrected reference-branch table sampler

The reference branch connects the stronger trace to ordinary-table output:
ordered positive-margin lists, the recomputed cutoff and branch guards,
the scheduled joint draw, actual repair and padding test, a literal inverse
counter and bounded coin, fresh independent retries, and zero restoration.
A reduced actual defect start and feasible reduced fallback remain inputs.

Let m,n be the filtered dimensions, d=10+(m+1)(n+1),
U=11d(m+n-2), L=7, p the number of small cells, and a,b the small-row and
small-column counts. Define c0=max[a(na-1),b(mb-1)] and
s=c0/[2p(p-1)]. The reference tag implies m,n>=2 and p>=2.
Positive filtering implies positive reduced margins. Thus s>0.

The ordered list counter equals the actual number ell(X) of successful
preimages of the completion-retaining repair, for every ordinary target X.
It uses ordinary support at a small crossing and both ordinary residual
slacks at a large crossing. It preserves the existing catalog order and
ordered-label multiplicity. No supplied inverse-count premise remains in
the actual correction theorem.

A separate k-bit suffix implements the threshold floor(2^k*c0/ell).
Clipping by min(c0,ell) makes the generic rule total; the geometric lower
bound removes the clip on valid ordinary targets. Padding failures remain
none and ignore their reserved suffix. The whole option-valued one-trial
law is within 2^-h+2^-k of the ideal corrected law. The proof charges this
error before rejection and never divides by the implemented success rate.

R fresh independent trials followed by the supplied feasible fallback have
ordinary-table total variation at most

```
(1-s)^R + R*(2^-h + 2^-k).
```

Exact zero restoration preserves this error relative to uniform tables on
the original margin lists. Repeated positive margins keep their original
positions. Physical states or kernels on the two shapes are not identified;
the cutoff, catalogs and schedule are rebuilt on the filtered lists.

The counter and bit test are computational functions. The composition is a
typed finite-word one-trial map plus the existing independent retry law.
It does not identify a literal encoded outer program or a flat retry-word
realizer. Initialization, automatic outer accuracy choices, the deterministic,
no-small and unit branches, and encoded costs remain separate obligations.
The old complete sampler and its runtime theorem are unchanged.

All six modules passed ordinary Lean compilation and full assumption audits.
Every module declaration and every complete headline closure uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. Separate AI
source reviews examine semantics and reconcile the receipts. The pinned
compiler and reused imports remain trusted. This is an additive research
scope, separate from historical Linux builds and strict Comparator replay.
Exact failed candidates and diagnostics are retained.

| English claim | Lean headline | Main hypotheses |
|---|---|---|
| Literal count equals the actual successful fibre | `listedInverseCount_eq_terminalInverseCount` | Valid ordinary table code, L>=1 |
| Actual bounded correction adds at most 2^-k | `terminalFiniteCorrectionRow_variation` | Actual joint input, L>=1; count equality is derived |
| Fresh corrected trial error is at most 2^-h+2^-k | `terminalCorrectedWord_accuracy` | Equal totals, U>=2, L>=7, p>=2, both large lists, actual defect start |
| Retries give the displayed table bound | `actualShape_terminalCorrectedRetry_accuracy` | Shape cutoff, L=7, positive margins, m,n>=2, p>=2, both large lists, start and feasible fallback |
| Success allowance after filtering is positive | `positiveTraceCorrectionSuccess_positive` | Computed reduced reference tag |
| Original ordered table error has the same bound | `positiveTraceCorrectedRetry_accuracy` | Equal original totals, reduced reference tag, reduced start and feasible fallback |

Each headline is in namespace `Math115.PhysicalTraceJoin`.

| Packet | Exact receipt |
|---|---|
| [Literal ordered-list count](../research/physical-trace-general-listed-count/) | [attempt-02](../research/physical-trace-general-listed-count/attempt-02/verification.json) |
| [Partial bounded coin](../research/physical-trace-general-bounded-coin/) | [attempt-03](../research/physical-trace-general-bounded-coin/attempt-03/verification.json) |
| [Actual correction row](../research/physical-trace-general-finite-correction/) | [attempt-01](../research/physical-trace-general-finite-correction/attempt-01/verification.json) |
| [Scheduled corrected trial](../research/physical-trace-general-corrected-word/) | [attempt-09](../research/physical-trace-general-corrected-word/attempt-09/verification.json) |
| [Fresh independent retries](../research/physical-trace-general-corrected-retry/) | [attempt-01](../research/physical-trace-general-corrected-retry/attempt-01/verification.json) |
| [Ordered original-table restoration](../research/physical-trace-zero-margin-corrected/) | [attempt-03](../research/physical-trace-zero-margin-corrected/attempt-03/verification.json) |
