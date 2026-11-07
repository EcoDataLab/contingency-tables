# Reference-branch initialization

6 November 2026.

For ordered positive-margin reference inputs, equal original totals now supply both a feasible greedy fallback and an actual positive-weight defect start. A finite row-major search finds distinct small-cell labels satisfying the existing ordinary support and residual-slack test. The initialized retry law keeps the bound `(1-s)^R + R*(2^-h + 2^-k)`.

The explicit fallback and label search are computational definitions. The inherited map from valid inverse labels to a defect state remains a noncomputable semantic construction. This packet does not establish an encoded initializer, initializer cost, automatic retry/precision settings, or all-branch dispatch.

## Inputs and hypotheses

The caller supplies equal original totals, the computed filtered `.reference` tag, and retry/precision settings R, h and k. The initialized theorem requires no caller-supplied defect start or fallback. Positive filtering, the branch dimensions/catalog and the inverse-support lower bound discharge existence.

## Checked evidence

[Exact source](formal/ResearchPhysicalTraceJoin/GeneralInitialization.lean) and
[verification receipt](attempt-02/verification.json) identify successful
attempt 02. All 27 module declarations and every complete
headline dependency closure were audited; only `propext`, `Classical.choice`
and `Quot.sound` occur. The receipt also binds the pinned compiler, source,
compiled object and accepted imported-object inventory.

| Headline | Declarations in dependency closure |
|---|---:|
| `initialization_inverseSupport_nonempty` | 6562 |
| `initializationLabelSearch_isSome` | 6649 |
| `positiveTraceDefect_nonempty` | 10978 |
| `positiveTraceInitializedRetry_accuracy` | 45609 |

Attempt 01 failed ordinary compilation with unresolved names, noncomputable dependencies in the initial label test, and a support-specification mismatch. The exact candidate and diagnostics are retained. Attempt 02 uses the existing literal listed-label test and passed compilation and audit.

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
