# Explicit runtime degree for the original fixed public machine

Published source-bound checkpoint after separate AI source review and full headline-closure audit. This is ordinary Lean verification with trusted imports; it does not claim default/strict target acceptance, a new Comparator run, or a fresh-platform replay.

The exact existing `Math115.PublicLatticeSampler.machine` now has an unconditional explicit-degree theorem. `source/CompleteDraw/FixedMachineTheorem.lean` contains:

- `machineTime_public_explicit_degree`: one positive coefficient uniformly bounds the same machine's running time for every dimension, equal-total natural margin pair and precision `h≥1`.
- `fixedMachineBoundedSampling_explicit_degree`: at that polynomial time every tape yields a feasible `Table r c`, and total variation from the uniform table law is at most `2^-h`.

Neither theorem assumes a runtime degree or reference-field certificate. The existing d17 machine, Algorithms input/output codecs, empty-dimension behavior and distributional conclusion remain unchanged. This is finite runtime-degree closure for that machine; it is not an upstream numerical speedup, a practical runtime benchmark or the separate newer ideal-chain sampler.

The fixed exponent is the following literal-natural expression:

```
k = max(unitTrialDegree, referenceTrialDegree)
t = 8 * (1 + k * (k + 1)) * k^5
D = 340 * max(1008, t)
```

The unit constant is `272019144737569436269241336269647035188617216`; the exact 591-digit reference constant is defined in `FinalBinding.lean`. Its owner-confirmed source/object identities are retained in `degree-values.json` and `dependency-bindings.json`. The exact draw exponent has 4,134 decimal digits; the public-machine exponent has 4,137. Their full exact decimal values are machine-readable in `degree-values.json`, and Lean independently checked the decimal public value against the factored expression by `decide` in `Audit.lean`.

`FinalBinding.lean` also closes `Typed publicDrawRealizer explicitDrawDegree` and its expanded charged-work-plus-complete-encoded-output statement for every literal word/bank pair. `Seams.lean` instantiates all nine original fields; `field-closure.json` independently checks that each degree lies below `k`. `PublicBridge.lean` reuses the existing affine degree-1008 count bridge. Generic conditional helper statements are retained as reusable proof code, but the final public headlines are fully closed. The old conditional readback is confined to `history`.

All five own final modules compiled with cached imports in ordinary local Lean 4.34.1, two threads and an 8192 MiB cap. The five selected closed headline axiom closures contain only `propext`, `Classical.choice` and `Quot.sound`; exact type readback is in `evidence/final-readback.stdout.txt`. Compiler elapsed times are proof-verification times, not sampler runtime. `verification.json` and `compilation.json` bind source/object bytes, while `owner-bindings.json` preserves the original private receipt identities.

The packet intentionally references accepted count/draw-control/assembly, branch, printer, initializer, retry, unit, reference and affine public-bridge packets instead of copying their broad dependency trees or binary caches. `dependency-bindings.json` records the exact direct source and reused object identities. Independent source review and full compiled-environment headline attribution both passed and are retained under `reviews`. The existing environment audit selected 19 declarations, including 12 theorems in the four defining modules; the full fixed-machine theorem closure has 48,401 declarations and only standard axioms. The existing ledger validator passed. Full raw closure records/dependencies and the imported-object roster remain in their compressed evidence files; they were not truncated. Only compilation source paths were projected to the agreed public copies, with original receipt digests preserved.

For a contributor replay, first obtain an authenticated merged object prefix for the referenced accepted helper/original modules. Then use the pinned Lean toolchain:

```sh
python3 REPRODUCE.py --repo /path/to/repository \
  --base-objects /path/to/authenticated/helper-objects \
  --output /path/to/a/new/complete-degree-replay
```

This compiles only the five included modules in dependency order into the new output directory, leaving the provided baseline unchanged. `PACKET_VERIFY.py` checks packet bytes and arithmetic without compiling. These are prepared commands; no fresh/public-path replay was performed during staging. The original sampler sources and strict source freeze remain unchanged. Failed-attempt stdout copies redact only the local workspace prefix; `publication-redactions.json` records their original and published digests.
