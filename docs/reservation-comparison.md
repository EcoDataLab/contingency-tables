# Complete reserved-word comparison

The smaller chain-gap bound has not yet produced a smaller complete reserved random-bit bank. On the four examples below, the linear outer retry schedule improves the stronger construction, but repeated inner completion reservations still make its complete bank vastly larger than the legacy sampler's.

This compares the same quantity—complete reserved word length—on the same margins and target error `2^-20`. It is not a timing test or an expected-bit estimate. The two algorithms use their respective proved scales. [Exact integer artifacts and a reproducing script](../research/physical-trace-reservation-comparison/) retain every input and intermediate value; a separate AI reviewer independently recalculated them from the Lean formulas.

Each axis has one margin equal to 1 and all remaining margins equal to the displayed large value. Both algorithms classify each fixture as reference.

| Shape; large margins | Small cells p | Stronger linear retries; precision | Stronger complete reserved bits | Previous stronger bank / linear bank | Stronger linear bank / legacy bank |
|---|---:|---:|---:|---:|---:|
| 2 × 2; 100,000 | 3 | 252; 30 | 1.45014 × 10^309 | 3.76654 | 2.84537 × 10^126 |
| 3 × 3; 1,000,000 | 5 | 420; 31 | 2.20768 × 10^316 | 6.44062 | 3.81304 × 10^127 |
| 8 × 8; 1,000,000,000 | 15 | 1260; 33 | 4.21402 × 10^340 | 29.1282 | 3.82997 × 10^129 |
| 16 × 16; 1,000,000,000,000 | 31 | 2604; 34 | 2.18179 × 10^369 | 39.3074 | 8.73584 × 10^133 |

The first ratio changes only the stronger outer schedule, recomputing the shared inner bank at the resulting precision. The earlier schedule used `R=2p(p-1)(t+2)` and `h=k=t+3+clog₂ R`; the linear schedule uses `R=min(2p(p-1),4p)(t+1)` and `h=k=t+2+clog₂ R`. The formal comparison establishes no more retries; the complete-bank ratios above are exact arithmetic checks for these fixtures.

The new trace calls the frozen complete sampler for conditional completions. Its current uniform allowance raises a combined size to power 85 and includes a large global coefficient. That allowance is reserved repeatedly inside the balanced-state exit and then across the entire walk. The legacy program's actual scalar completion reservation instead uses its power-62 expression. These layers explain why the improved gap and outer retry bounds do not by themselves give an improved full reservation.

The raw outer program reuses `FirstSuccessProgram.retry`, which maps the trial over the supplied block list before selecting the first successful result. Its output agrees with recursive first-success selection, but that equation does not establish early return or fewer inspected bits for this implementation. The full reservation accommodates all attempts.

Two checked follow-ups address this bottleneck. The [shape-aware schedule](../research/physical-trace-general-shape-schedule/) retains the current numerator `c0` and uses the exact reciprocal block `ceil(2p(p-1)/c0)`. The [tighter completion bound](../research/physical-trace-general-completion-tight-budget/) substitutes actual residual dimensions and count/mass bounds into the existing scalar reservation, then takes the minimum with the old allowance. These are separate checked alternatives; this table continues to report the unchanged linear schedule and old uniform allowance. The [complete tight typed sampler](../research/physical-trace-general-tight-sampler/) now proves that law-preserving composition and total-width nonincrease for every equal-total input. The ordinary raw program still uses the larger bank. No new machine-time exponent or practical speedup follows from these numbers.


The checked typed alternative gives the following complete reservations on the
same fixtures, retaining current T/J/R and both precisions. The
[second exact calculator](../research/physical-trace-reservation-comparison/tight_reserved_bits.py)
and its [integer artifact](../research/physical-trace-reservation-comparison/tight-reserved-bits.json)
were reconciled with the full typed width formulas.

| Shape | Tight typed reserved bits | Current / tight typed bank | Tight typed / legacy bank |
|---|---:|---:|---:|
| 2 × 2 | 1.09603 × 10^210 | 1.32308 × 10^99 | 2.15056 × 10^27 |
| 3 × 3 | 6.65610 × 10^217 | 3.31677 × 10^98 | 1.14962 × 10^29 |
| 8 × 8 | 2.49035 × 10^246 | 1.69214 × 10^94 | 2.26339 × 10^35 |
| 16 × 16 | 3.28860 × 10^274 | 6.63440 × 10^94 | 1.31675 × 10^39 |

These enormous reductions remove a loose repeated envelope, yet the tight
banks still exceed the legacy bank on every fixture. The separate shape
schedule, augmented correction numerator and zero-bit singleton replacement
are not included in this table. No sampler was executed on these bit banks.
