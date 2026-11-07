# Independent source and local validation review

6 November 2026. A separate AI agent performed this source and evidence review.
Verdict: pass for the published source repair and source-only
assembly. This review used no remote resources, Lean compilation, VM, or strict
replay. The repaired Linux preparation and full strict verification remain unrun.

Both helpers add only `walk = None` at the start of the existing outer finalizer,
before the unchanged descriptor-closing loop. Independent AST comparison removes
that one assignment and recovers each original helper exactly. Recursive calls
have returned or unwound before the assignment executes. It breaks the closure's
self-reference without removing or reordering filesystem observations, identity
checks, rejection checks, returned metadata, or descriptor cleanup. Paths that
fail before the nested function is defined remain safe. No production GC setting
or explicit collection is introduced.

I independently ran all 15 normal-discovery regressions. They passed both lifetime
checks and the success/rejection/FD-cleanup comparisons, including symlinks,
missing entries, metadata mismatch, path escape, and directory-open failure.
The local default-enabled-GC diagnostic was rerun without changing its thresholds:
100 files and 80 snapshots retained 80 original expected maps versus zero fixed
maps, with approximately 8.47 MB versus 24.8 kB of retained traced allocations.
This verifies the bounded retention defect and its repair; it does not establish
production RSS, full-run memory bounds, or that this was the sole guest OOM cause.

The repaired helper hashes are
`55a3cef696f463fa4e9f54510498d61d99855275a95716431615299bc9b4cbde`
and
`2e23b335d43cad6a637d1ff9b0b1e5ee4e5ee45b4cc1458c53f2ac8b96f8fa56`.
I checked packet/reference/test-bridge hashes and independently applied each
unique replacement recipe. The resulting runner is
`b893f9af52bbe33c70eb883514a0e91ab50f7f1ed755c79202ef25625ee21e5f`;
the preparation helper is
`0e0b4e57db7973209048655edcebb5f7171c3800aecbcfb5ee2be795abdfe078`.
Their function/class bodies match the pinned predecessors. Only the documented
header/version labels and exact helper/candidate pins change.

I also assembled all 15 source/support files into a temporary destination and
loaded the candidate's fixed metadata, observer and planner, plus the original
runner's runtime assets, through their own hash-checking loaders. Assembly checks
and copies the same byte buffers, rejects drift before creating the destination,
and runs no preparation or checking process. Original source/runtime assets and
the failure evidence remain preserved; no validation or sandbox check is removed.

The packet correctly separates the Python helper OOM from mathematical/compiler
failure, states the sanitized terminal evidence boundary, and keeps the repaired
native/full-run status pending. Its target remains the historical 679-module
sampler. The source-only assembly supplies no VM/media/lease profile: future
execution must separately bind the intended longer invocation and enclosing
budgets, fresh runtime authentication, cache provenance, cleanup, and actual
export/default-kernel/Comparator acceptance.
