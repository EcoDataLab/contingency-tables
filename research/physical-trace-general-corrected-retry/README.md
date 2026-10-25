# Fresh retries of the corrected reference law

24 October 2026. At U=11d(m+n-2), L=7, the actual inverse and padding counts supply s=c0/[2p(p-1)]. R independent complete trials and a supplied feasible fallback have ordinary-table error at most (1-s)^R+R*(2^-h+2^-k). Positive margins, m,n>=2, p>=2, both computed large-line lists and an actual defect start remain explicit. No success or desired-error bound is assumed in the actual-shape theorem.

[Source](formal/ResearchPhysicalTraceJoin/GeneralCorrectedRetry.lean) and
[verification receipt](attempt-01/verification.json) identify the exact checked result.
Ordinary compilation and the environment audit passed. Every module declaration
and every complete headline dependency closure uses only standard axioms.

| Headline | Declarations in its dependency closure |
|---|---:|
| `terminalCorrectedRetry_accuracy_of_success` | 45278 |
| `actualShape_terminalCorrectedRetry_accuracy` | 45459 |

Run `REPRODUCE.sh` with prepared pinned imports in `LEAN_PATH` and a new output
directory. The compiler and reused dependencies remain trusted. This is an
additive research check, separate from default-target Linux and Comparator
verification. The earlier failed candidates and diagnostics are preserved.
The profiling attempt has its large diagnostic stream stored as a compressed,
path-projected file; it is a failed diagnostic run, not proof evidence.

[The bridge note](../../docs/corrected-reference-sampler.md) states the complete
hypotheses and remaining work. These typed-law results do not construct an
initializer, choose outer accuracy parameters, realize an encoded retry
program, handle every branch, or give a new complete runtime exponent.
