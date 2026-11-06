# Complete ordinary sampler contract

`executableSampler_contract` ties the actual ordinary `rawHybridSamplerCode` to its computed reserved width, a feasible table on every full word, and total variation at most `2^-t` under uniform fair bits. The only input condition is equal natural margin totals; zero margins, empty lists and every natural t are included.

The [source](formal/ResearchPhysicalTraceJoin/GeneralExecutableSampler.lean) composes the exact whole-program correspondence and existing typed accuracy theorem. It does not assume a starting state, acceptance probability, branch, law or supplied schedule. It uses the stronger trace on the recomputed reference branch and retains the checked deterministic and legacy branches elsewhere.

[Attempt-02](attempt-02/verification.json) passed ordinary Lean compilation and the full assumption audit of its headline dependency closure. The [history](attempts.json) retains the initial missing-namespace compiler error. Only standard axioms occur; the compiler and reused imports remain trusted. The [separate AI review](AI-SOURCE-REVIEW.md) checks source and receipts. No revised encoded Realizer, charged runtime degree or strict Comparator acceptance is claimed.

See the [program guide](../../docs/executable-sampler.md), [reservation comparison](../../docs/reservation-comparison.md), and [fresh source replay](../repair-accept/INTEGRATION-REPLAY.md). `REPRODUCE.sh` checks this module when the stated dependencies are available.
