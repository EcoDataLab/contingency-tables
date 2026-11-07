# Explicit outer accuracy settings

6 November 2026.

For the corrected reference law, let p be the filtered small-cell count, `A=2p(p-1)`, `R=A*(t+2)`, and `q=t+3+clog₂ R`. Using q for both one-trial precision settings gives original-table total variation at most `2^-t`. The success interval and reciprocal-block bound are derived from the actual correction law and positive integer numerator.

These are explicit natural law-level settings. This packet does not construct the defect start or fallback, flatten the retries into a Boolean word, supply an encoded program, or prove running time.

## Inputs and hypotheses

The scheduled accuracy theorem takes equal original totals, the computed filtered `.reference` tag, an actual reduced defect start, a feasible reduced fallback, and target t. No desired-error inequality or externally supplied success bound is assumed.

## Checked evidence

[Exact source](formal/ResearchPhysicalTraceJoin/GeneralOuterSchedule.lean) and
[verification receipt](attempt-02/verification.json) identify successful
attempt 02. All 14 module declarations and every complete
headline dependency closure were audited; only `propext`, `Classical.choice`
and `Quot.sound` occur. The receipt also binds the pinned compiler, source,
compiled object and accepted imported-object inventory.

| Headline | Declarations in dependency closure |
|---|---:|
| `positiveTraceCorrectionSuccess_bounds` | 13108 |
| `positiveTraceOuter_budget` | 13181 |
| `positiveTraceOuterScheduled_accuracy` | 45592 |

Attempt 01 failed an arithmetic goal and exhausted the deterministic heartbeat limit while reducing a large expression. Its exact candidate and diagnostics are retained. Attempt 02 passed compilation and audit without changing the declaration headers.

## Replay and evidence boundary

Use `LEAN_PATH=<prepared pinned dependency object paths> bash REPRODUCE.sh NEW_OUTPUT_DIRECTORY`
from this packet, or invoke the script by its path. Set `LEAN_BIN` to override
the default pinned Lean 4.34.1 binary. The output directory must be new;
replay compiles this additive module and reruns the environment audit.
Dependencies must already be prepared; the script does not rebuild them.

The recorded result is ordinary additive compilation and a compiled-environment
assumption audit. The compiler and reused imports remain trusted. This is
separate from a default-target Linux rebuild, strict Comparator acceptance,
independent source review, and a new encoded sampler/runtime result.
