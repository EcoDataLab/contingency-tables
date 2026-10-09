# Explicit completion schedules and reserved fair bits

The outer error budget now has a computable natural-number schedule, with
all four scalar error terms bounded by `2^(-(h+3))`. Their sum is at most
`2^(-(h+1))`, leaving a factor-two margin below the requested `2^(-h)`.
A second theorem bounds the entire reserved fair-bit bank by an explicit
polynomial in dimension, binary margin length, and requested precision.

These are verified arithmetic components. The physical-law wrappers,
complete outer program, and composed machine cost have separate validation
obligations. Degree **85** below describes reserved bits; it is not a
sampler runtime exponent.

## The natural schedule

Let `M` be the original total margin, `d` the dimension allowance, `p` the
number of threshold-selected small cells, and `h≥0` the accuracy exponent.
At the ideal scales `L=3d` and `U=5d³`, put

\[
 A=M+3d^2+5d^3+3,\qquad S=2(1+p^2),\qquad K=80000d^{17}.
\]

Write `clog₂` for the **ceiling** binary logarithm, implemented by
`Nat.clog 2`. The choices are

\[
\begin{aligned}
 R&=2(1+p^2)(h+3),\\
 T&=80000d^{17}\bigl(h+3+\operatorname{clog}_2R
                  +2d\operatorname{clog}_2A\bigr),\\
 h_{\rm terminal}&=h+3+\operatorname{clog}_2R,\\
 h_{\rm step}&=h+3+\operatorname{clog}_2R+\operatorname{clog}_2T.
\end{aligned}
\]

The scalar theorem needs `d≥1` and a proposal allowance `γ≤1`. For the
intended nonnegative error terms, with `B=A^(2d)`, it gives:

| Error term | Bound |
| --- | --- |
| Outer retries: `exp(-R/S)` | `2^(-(h+3))` |
| Walk mixing: `R B exp(-T/K)` | `2^(-(h+3))` |
| Transition approximation: `R T γ 2^(-hStep)` | `2^(-(h+3))` |
| Terminal approximation: `R 2^(-hTerminal)` | `2^(-(h+3))` |

Ceiling-log precision pays for the full factors `R` and `R*T`. The walk
length retains the **`2d` log-mass factor**. The proof uses
`exp(-n)≤2^(-n)` and `x≤2^(clog₂ x)`. It introduces no real-log ceiling or
unbounded search into the schedule functions. `R` is always positive and
`T` is positive when `d≥1`; `p=0` and `h=0` are included.

The declarations are in
[CompletionScheduleArithmetic.lean](../formal/Math115/CompletionScheduleArithmetic.lean),
under the preserved `Math115.CompletionOuterSchedule` namespace.
`arithmetic_schedule_half` proves the half-target bound;
`arithmetic_schedule` gives the requested target.

## The whole reserved bit bank

Fine margins are enlarged by `d¹²`. The common row and binary-length bounds
are

\[
 C=d^{12}(M+3d^2+2d),\qquad c=\operatorname{clog}_2(C+2).
\]

For a completion call requesting exponent `t`, the reserved inner retries,
fine-draw precision, and whole completion word are

\[
\begin{aligned}
 J(t)&=4(t+2),\\
 q(t)&=t+2+\operatorname{clog}_2J(t),\\
 F(t)&=25J(t)\bigl(d+c+q(t)+1\bigr)^{62}.
\end{aligned}
\]

The source proposal word has `s=clog₂(32d²)` bits. The entire reservation is

\[
 W=R\bigl[T\bigl(s+F(h_{\rm step})\bigr)+F(h_{\rm terminal})\bigr].
\]

This includes a proposal and completion word on every transition and a
fresh terminal completion word on each attempt. Holds, rejection, and early
success can leave reserved words unused. `W` counts the fixed reservation,
not expected bits inspected.

Set `b=clog₂(M+2)` and `N=d+b+h+3`. For natural `M,h`, `d≥11`, and `p≤d`,
[CompletionRandomBudgetArithmetic.lean](../formal/Math115/CompletionRandomBudgetArithmetic.lean)
proves

\[
\begin{aligned}
 W&\le 12672000000\,37^{62}\,d^{20}(h+3)N^{64}\\
  &\le 12672000000\,37^{62}\,N^{85}.
\end{aligned}
\]

The namespace is `Math115.CompletionRandomBudget`; the two final theorems
are `totalReservedBits_separated` and `totalReservedBits_combined`.
The proof retains the dilation's contribution to binary length:

\[
 C+2\le4d^{14}(M+2),\qquad
 c\le b+14\operatorname{clog}_2d+2.
\]

Useful intermediate bounds are `R≤4d²(h+3)`, `T≤480000d¹⁸N`,
`hStep≤21N`, and `F(t)≤2200·37⁶²N⁶³` for either used precision. The extra
dimension factor in the walk allowance comes from the retained log-mass
term. These universal allowances are very large; polynomial dependence is
not evidence of practical sampling speed.

## Verification and reproduction

The two frozen arithmetic modules compiled locally with Lean **4.34.1**.
All **24+32=56 declarations** passed the strict named standard-axiom audit:
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
Both final compile logs are empty. The
[verification receipt](../formal/results/completion-schedules/verification.json)
records exact source, object, driver, and log hashes; the
[independent review](../formal/results/completion-schedules/source-review.json)
checks those receipts and the arithmetic contracts. Its 2,240 independent
integer checks supplement the universal Lean proofs.

The pins are OpenAI `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Validation reused existing
pinned dependency objects and the official package cache. It restored no
upstream modules for this checkpoint; it was not a fresh dependency-closure
build, Linux reproduction, or strict Comparator replay. The unchanged
237-test Python record remains separate historical evidence.

With the [pinned environment](formal-verification.md) and dependencies
available, compile and audit the actual source modules from `formal/`:

```sh
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean \
  -j1 -DautoImplicit=false \
  -o .lake/build/lib/lean/Math115/CompletionScheduleArithmetic.olean \
  Math115/CompletionScheduleArithmetic.lean
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean \
  -j1 -DautoImplicit=false results/completion-schedules/CompletionScheduleArithmetic-AxiomAudit.lean
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean \
  -j1 -DautoImplicit=false \
  -o .lake/build/lib/lean/Math115/CompletionRandomBudgetArithmetic.olean \
  Math115/CompletionRandomBudgetArithmetic.lean
ELAN_HOME="$PWD/../.tools/elan" ../.tools/elan/bin/lake env lean \
  -j1 -DautoImplicit=false results/completion-schedules/CompletionRandomBudgetArithmetic-AxiomAudit.lean
```

The separate two dense-law wrappers and six physical reservation wrappers
are uncompiled and outside this checkpoint. These 56 arithmetic declarations
do not establish new dense integration, an already compiled physical outer
program, or a complete finite-bit sampler runtime theorem.
