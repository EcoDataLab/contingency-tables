# Uniform completion bit bound at arbitrary physical scales

23 October 2026. The [Lean module](formal/ResearchPhysicalCompletionWidth/Bound.lean), `ResearchPhysicalCompletionWidth.Bound`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

For original dimension allowance D, total M and selected large-line counts R,C, every actual physical state's coarse request has total at most M+LRC and dimension at most D. The frozen complete sampler's existing reservation theorem therefore supplies

```
q_z(h) ≤ C0 · [D + clog2(M+LRC+2) + h+3]^85.
```

`coarseRows_total` proves the computed request reindexes all nonzero physical residual rows. `coarseDimension_le` bounds the request's actual dimensions. `completionBits_le_uniform` then applies `LatticeSampler.reservedBits_combined` and monotonicity to obtain the state-independent bound. C0 is the existing `CompletionRandomBudget.budgetCoefficient`; no maximum over states is computed.

Both computed large-line lists must be nonempty and an actual physical state is supplied. U,L,h are arbitrary natural numbers, including zero; original zero margins and singleton selected blocks are permitted. The bit bound itself requires neither equal original totals nor padding seven. At L=7 the padded total is M+7RC.

This is an independent backend reservation lemma. The exponent85 is inherited from the frozen sampler and describes reserved bits, not machine time. A new trace-step realization, repeated walk, output correction and full encoded machine require their own proofs.

## Evidence and replay

Ordinary Lean compilation passed in 48.48 seconds;
the compiled-environment audit passed in 101.16 seconds. The
[receipt](attempt-03/verification.json) binds the source, compiled object,
all module declarations and 3 complete headline dependency closures.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The dependency
objects match the recorded accepted or newly compiled input hashes.

The pinned compiler and reused baseline objects remain trusted. This is
separate from the historical default-target Linux build and strict Comparator
task. [AI source review](AI-SOURCE-REVIEW.md) is not human review or independent
kernel verification. Failed compiler attempts are retained when present;
the [scope check](attempt-03/scope-check.json) and [proof diff](attempt-03/proof-only.diff)
record proof repairs. Source and compressed audit bytes are unchanged;
public diagnostic paths and trailing whitespace are projected.

Prepare the pinned Lean compiler and the dependency objects named by this
module's imports, including `ResearchAudit.EnvironmentAudit`, then run:

```sh
LEAN_PATH=<prepared-object-roots> bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

The script compiles this additive module and audits its loaded environment.
It downloads or rebuilds no dependencies. The script is syntax-checked; the
saved run used the same source and compiler options. The claims-ledger
validator checks the saved source, statements, closures and object inventory.
