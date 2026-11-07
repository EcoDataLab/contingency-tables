# A complete legacy fallback after filtering

6 November 2026.

The existing complete finite-word sampler is rebuilt on the ordered positive margins, with its own cutoff `U=5d³`, padding `L=3d`, initializer and schedule. Ordered zero restoration gives a typed original-table map with total variation at most `2^-h` for every equal-total input pair, including empty lists and zero margins. A separate zero-width constant greedy map has exact uniform law on the computed deterministic branch.

This backend does not preserve the sharper classifier or identify states across scales: its cutoff differs from `11d(m+n-2)` and its padding differs from 7. This packet supplies typed maps and laws for later hybrid dispatch; it does not itself implement the complete hybrid, encoded preprocessing/restoration, or a new runtime theorem.

## Inputs and hypotheses

The legacy accuracy theorem takes only original lists, equal original totals and target h. It requires no supplied start, fallback, branch-preservation assertion or desired-error premise. The deterministic exact-law theorem additionally takes the computed filtered `.deterministic` tag.

## Checked evidence

[Exact source](formal/ResearchPhysicalTraceJoin/GeneralLegacyFallback.lean) and
[verification receipt](attempt-03/verification.json) identify successful
attempt 03. All 9 module declarations and every complete
headline dependency closure were audited; only `propext`, `Classical.choice`
and `Quot.sound` occur. The receipt also binds the pinned compiler, source,
compiled object and accepted imported-object inventory.

| Headline | Declarations in dependency closure |
|---|---:|
| `positiveLegacyWord_law` | 15866 |
| `positiveLegacyWord_accuracy` | 43118 |
| `positiveDeterministicWord_law` | 7628 |

Attempts 01 and 02 failed ordinary compilation on the deterministic proof's unqualified constant-map lemma. Their exact candidates and diagnostics are retained. Attempt 03 opens the lemma's existing namespace and passed compilation and audit.

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
