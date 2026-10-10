# Outer-sampler compiler checkpoint — first repair round

The first repair round, completed on 10 October 2026 at 14:52 UTC, produced successful fresh, full-module ordinary Lean compiler receipts for two research modules: the revised `LatticeSamplerPreparation` and unchanged `LatticeEmptyOutput`. The first native round still failed overall: 673 modules were reused, two failed, and eight were dependency-blocked. This checkpoint does not establish a complete encoded outer sampler, a new named-axiom audit result, or a machine-runtime bound.

| Module | Recorded round-one outcome | What can be claimed |
| --- | --- | --- |
| `LatticeSamplerPreparation` | Revised source `e5d33b3c…` compiled in 224.38 seconds; source unchanged during compilation; one deprecation warning retained | Successful ordinary compilation of that exact full source and recorded imported objects |
| `LatticeEmptyOutput` | Archived source `5af2b648…` compiled in 58.33 seconds; empty compiler log | Successful ordinary compilation of the unchanged archived source |
| `LatticeProfileWalk` | Compilation failed on a type/universe mismatch; reviewed round-two candidate awaits actual compilation | A recorded blocker and a reviewed candidate, without a compiler-success claim |
| `LatticeUnitStep` | Compilation failed at the deterministic heartbeat limit; reviewed round-two candidate awaits actual compilation | A recorded blocker and a reviewed candidate, without a compiler-success claim |
| `LatticeUnitWalk` | Dependency-blocked in round one; reviewed round-two candidate awaits actual compilation | No successful full-module compilation from this round |

The [source and evidence package](../formal/results/native-round1-evidence/README.md) preserves this historical round, including the failed attempts. It is not a report of later compiler rounds.

The original [outer-sampler archive](../research/outer-sampler/) is unchanged. Candidate overlays and subsequent receipts must be retained as additive evidence, with their own source hashes and imported-object bindings. The second-round descriptions above record their status when this first-round checkpoint was prepared; no second-round compiler result is asserted here.

A separate AI agent replayed the downloaded artifacts and saved metadata, including source bindings, dependency-map consistency, and the two successful delivered objects. It found no evidence-consistency blocker. This was local artifact review, without a fresh compiler or kernel run or live reauthentication of every dependency object and executable. The operator's recorded rechecks and that narrower AI-agent review are separate evidence. No outside human review or reproduction is claimed.

Ordinary Lean compilation is also separate from a no-admissions/allowed-axioms audit, an environment inventory, and Comparator acceptance. This round ran no new named-axiom audits. No strict Comparator success is claimed by this checkpoint. Comparator results require their own completed, scope-bound receipt.

## Reproduction

Use the [exact source overlay, manifest, and replay recipe](../formal/results/native-round1-evidence/README.md#reproducing-the-source-attempts) in an isolated checkout. The package records object hashes but does not distribute compiled objects. Preserve the archived sources. The original source and dependencies remain pinned, including Lean `leanprover/lean4:v4.34.1` and OpenAI source `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

Bootstrap the repository's pinned dependencies and reproduce the checked base using its existing workflow:

```sh
bash scripts/bootstrap_lean.sh
bash scripts/verify_lean.sh focused --serial
```

That command verifies the default checked base; it does not compile the archived outer sampler. Restore only the manifest-selected research overlay into the isolated project, confirm its source hashes, and build its imported modules in recorded dependency order. After the required predecessor modules are present, the two round-one successes can be tested explicitly from `formal/`:

```sh
../.tools/elan/bin/lake --no-ansi build +Math115.LatticeSamplerPreparation
../.tools/elan/bin/lake --no-ansi build +Math115.LatticeEmptyOutput
```

A new receipt should preserve the actual source/object hashes, compiler and dependency pins, complete logs, exit codes, warnings, and whether an object was rebuilt or reused. The recorded durations describe this native Windows verification run, not application sampling speed or a cross-platform timing guarantee. The [Windows guide](windows-verification.md) describes the pinned native workflow.

Before promoting a repaired module into the checked target, obtain successful exact-source compilation, its explicit named-axiom audits, and review of the stated interface. The next unresolved evidence is actual compilation of the three reviewed round-two candidates and any newly reachable downstream modules. The [handoff](handoff.md) retains the later whole-program, runtime, strict-checking, and application-validation obligations.
