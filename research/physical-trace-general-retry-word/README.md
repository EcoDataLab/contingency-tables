# A flat word for fresh corrected retries

6 November 2026.

One finite Boolean word is split bijectively into R disjoint complete corrected-trial words, including each trial's reserved correction suffix. First-success recursion advances only on `none`; a successful table equal to the fallback is accepted. With R=0 the width is zero and the output is the fallback.

The map's uniform-word law equals the existing independent retry law exactly. Under the stated geometric conditions and a supplied ideal success lower bound s, its table error is at most `(1-s)^R + R*(2^-h + 2^-k)`. This is typed finite-word semantics, with no encoded retry realizer or charged running-time theorem.

## Inputs and hypotheses

The map takes margins, cutoff/padding, both computed large-list guards, an actual defect start, one-trial precision settings, a feasible fallback and R. The generic accuracy theorem additionally requires equal totals, U≥2, L≥7, p≥2, positive margins and `s ≤ 1 - idealFailureMass`. It does not itself derive the last bound or choose R/h/k.

## Checked evidence

[Exact source](formal/ResearchPhysicalTraceJoin/GeneralRetryWord.lean) and
[verification receipt](attempt-01/verification.json) identify successful
attempt 01. All 9 module declarations and every complete
headline dependency closure were audited; only `propext`, `Classical.choice`
and `Quot.sound` occur. The receipt also binds the pinned compiler, source,
compiled object and accepted imported-object inventory.

| Headline | Declarations in dependency closure |
|---|---:|
| `terminalCorrectedRetryWordLaw_eq` | 43966 |
| `terminalCorrectedRetryWord_accuracy_of_success` | 45284 |

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
