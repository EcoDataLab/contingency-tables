# A linear reciprocal success allowance

6 November 2026.

The small-cell mask is a union of small rows and small columns. Its incidence identity gives `p-1 ≤ 2*c0`, where c0 is the existing inverse-support allowance. On a filtered reference input, the correction success allowance `s=c0/[2p(p-1)]` therefore satisfies `1/(4p) ≤ s`.

This sharpens the outer retry allowance. It does not change the transition kernel, spectral gap or completion accuracy, and supplies no new encoded/runtime theorem. The lower bound concerns the derived allowance; the earlier correction-law theorem connects that allowance to ideal successful mass.

## Inputs and hypotheses

The incidence and numerator inequalities are generic finite-margin statements. The final rational inequality requires only the computed filtered `.reference` tag, which supplies p≥2. It does not assume the desired lower bound, require a supplied start, or assert an implemented finite-word success rate.

## Checked evidence

[Exact source](formal/ResearchPhysicalTraceJoin/GeneralLinearSuccess.lean) and
[verification receipt](attempt-02/verification.json) identify successful
attempt 02. All 15 module declarations and every complete
headline dependency closure were audited; only `propext`, `Classical.choice`
and `Quot.sound` occur. The receipt also binds the pinned compiler, source,
compiled object and accepted imported-object inventory.

| Headline | Declarations in dependency closure |
|---|---:|
| `smallCell_card_incidence` | 4022 |
| `inverseSupportAllowance_twice` | 4154 |
| `positiveTraceCorrectionSuccess_linear` | 7843 |

Attempt 01 failed ordinary compilation because the `Cells` namespace was not opened, with consequent type/cast errors. Its exact candidate and diagnostics are retained. Attempt 02 opens the existing coordinate namespace and passed compilation and audit.

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
