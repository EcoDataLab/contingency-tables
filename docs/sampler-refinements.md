# Refinements beyond the assembled list program

The [complete ordinary sampler](executable-sampler.md) uses the linear outer
schedule, correction numerator `c0`, and the previous uniform completion-bit
allowance. The results below are checked alternatives. Each targets a different
source of wasted work; none changes the spectral-gap exponent.

## More guaranteed repair labels

Let `p` count the cells in the union of small rows and small columns, and let
`N(X)` count the valid ordered inverse-repair labels for an ordinary table `X`.
With positive row and column margins, the new theorem proves

```text
N(X) >= p - 1
N(X) >= C = max(c0, p - 1)
c0 = max(a*(n*a - 1), b*(m*b - 1)).
```

The proof constructs distinct valid labels by connecting the small-cell set
through positive small donors. It first covers the small-row cells and then
attaches the remaining small-column cells. It does not assume that a large
residual donor has positive slack. A stronger earlier count conjecture failed
precisely at that boundary; the [packet](../research/physical-trace-general-augmented-lower/)
retains its counterexample and independent exact checks.

This is a universal count theorem for actual feasible tables with positive
margins, including degenerate cases through natural subtraction. It does not
depend on a completion oracle's accuracy. Installing `C` in the acceptance
coin now has a [checked law-level refinement](../research/physical-trace-general-numerator-correction/).
At the actual reference scales with p>=2, it gives ideal success at least
`1/(2p)` and retry error at most
`(1-1/(2p))^R + R*(2^-h+2^-k)`. The original start/fallback and h,k,R remain
explicit in this theorem. The assembled raw program and automatic schedule
still use `c0`; their changed-numerator code adapter remains separate.

## Use the known numerator in the retry schedule

Even without changing `c0`, the current schedule can use its value more closely.
Write `D=2*p*(p-1)` and `s=c0/D`. The
[shape-aware schedule](../research/physical-trace-general-shape-schedule/) chooses

```text
K = ceil(D/c0)
R = K*(t+1)
h = k = t+2+clog2(R).
```

On the computed reference branch, `c0>0`, `K*s>=1`, and `K` is the least natural
number satisfying `D<=K*c0`. The failure term and two accumulated draw errors
then fit the same `2^-t` target. Attempts and both precisions are no larger
than in the current linear schedule. Minimality concerns that integer
certificate; it does not assert an optimal retry count.

Kernel-checked fixtures illustrate the reduction. At `t=10`, equal axis lists
of nine ones followed by 30,000 reduce attempts from 4,356 to 275 and precision
from 25 to 21. Nineteen ones followed by 200,000 reduce attempts from 17,556
to 495 and precision from 27 to 21. These are evaluated schedule formulas,
not sampler timing measurements.

## Bound completion words at their actual residual dimension

The residual block has fixed row and column counts `lr,lc`. Its dimension is
`Dr=10+(lr+1)*(lc+1)`, and its mass is at most
`sum(rows)+L*lr*lc`. The
[tighter completion bound](../research/physical-trace-general-completion-tight-budget/)
substitutes these bounds into the existing frozen sampler's scalar reservation
and takes the minimum with the previous uniform allowance. Every actual
source request fits this new allowance, and the allowance is no larger than
the previous one.

The [shorter-word adapter](../research/physical-trace-general-tight-width/)
carries that bound through a step, repeated walk and independent terminal
completion, proving exactly the same joined and terminal laws. The new and
old word spaces have different lengths; the theorem equates their output
distributions under uniform fair bits. The actual source completion still
determines the incoming split, with unused uniform padding at the final suffix.

The [complete tight typed sampler](../research/physical-trace-general-tight-sampler/)
now composes correction, retries, initialization and zero restoration as well.
It preserves the entire hybrid output law and has total width no larger than
the current hybrid, for every equal-total input and natural t. Its unchanged
deterministic and legacy branches retain their original widths. Installation
in the ordinary raw program remains separate. The [complete reservation comparison](reservation-comparison.md)
keeps the unchanged program's costs visible, including its unfavorable
comparison with the legacy sampler.

## Exact zero-bit singleton completions

When both residual row and column lists are nonempty and one has length at
most one, the fixed margins determine a unique table. The
[singleton replacement](../research/physical-trace-general-singleton-completion/)
returns that greedy table from a zero-bit word. It equals every complete
inherited draw and has exactly the same distribution. Its raw-code equation
retains a sufficient-word-length guard. Empty residual lists use a different
branch, and arbitrary short inputs are outside this equivalence theorem.
The default raw sampler has not yet installed this shortcut.

## Evidence and remaining interfaces

| Result | Main Lean statements | Hypotheses |
|---|---|---|
| Spanning repair-label bound | `inverseSupportCount_spanning_lower`, `augmentedInverseSupportAllowance_le_count` | An actual feasible table; all row and column margins positive |
| Augmented correction/retry law | `actualShape_terminalAugmented_success_lower`, `actualShape_terminalAugmentedRetry_accuracy` | Positive margins at actual reference scales; p>=2, both large-line lists and supplied actual start/fallback, h,k,R |
| Shape-aware retry budget | `positiveTraceShapeBlock_success`, `positiveTraceShapeScheduled_accuracy` | Computed positive-list reference branch; equal totals and actual start/fallback for sampling |
| Tighter source reservation | `completionBits_le_rawTight`, `rawTightCompletionBits_le_old` | Actual positive physical source; nonempty computed large-row and large-column lists; arbitrary natural scales and precision |
| Same-law shorter terminal bank | `tightTerminalJoinedWord_law` and associated width bounds | Equal totals, actual defect start and nonempty computed large-line lists, with stated schedule parameters |

The singleton result is `singletonCompletionDraw_same_law`; its exact
nonempty/singleton hypotheses are retained in the public statement.

Names are in `Math115.PhysicalTraceJoin`; the packets give the exact Lean types.
All linked proof families and adapters passed ordinary
compilation and full assumption audits, followed by separate AI source and
receipt review. Only standard Lean axioms occur. The compiler and reused
imports remain trusted. These receipts do not establish a revised encoded
machine, charged runtime degree, practical speedup, human review or strict
Comparator acceptance.
