# Linear outer retry settings

6 November 2026.

Let p be the filtered small-cell count, `A=min(2p(p-1),4p)`, `R=A*(t+1)`, and `q=t+2+clog₂ R`. The existing corrected reference law with both precision settings q has original-table total variation at most `2^-t`. The block satisfies A≤4p and the retry count never exceeds the earlier outer schedule.

This combines the incidence success allowance with the existing correction-law bound. It is a law-level improvement to the outer settings, without an encoded program, initializer, revised spectral bound, or complete running-time exponent.

## Inputs and hypotheses

The accuracy theorem takes equal original totals, the computed filtered `.reference` tag, an actual reduced defect start, a feasible reduced fallback and target t. The success lower bound and budget inequality are derived, rather than supplied as desired-result premises.

## Checked evidence

[Exact source](formal/ResearchPhysicalTraceJoin/GeneralLinearSchedule.lean) and
[verification receipt](attempt-01/verification.json) identify successful
attempt 01. All 13 module declarations and every complete
headline dependency closure were audited; only `propext`, `Classical.choice`
and `Quot.sound` occur. The receipt also binds the pinned compiler, source,
compiled object and accepted imported-object inventory.

| Headline | Declarations in dependency closure |
|---|---:|
| `positiveTraceLinearBlock_le_linear` | 2392 |
| `positiveTraceLinearAttempts_le_old` | 2404 |
| `positiveTraceLinear_budget` | 13231 |
| `positiveTraceLinearScheduled_accuracy` | 45611 |

Attempt 01 passed ordinary compilation and the full audit. No failed candidate precedes it in this packet.

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
