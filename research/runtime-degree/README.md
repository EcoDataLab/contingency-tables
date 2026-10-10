# Runtime-degree research handoff

This package preserves four frozen Lean sources and their diagnostic evidence. **No numerical complete sampler runtime exponent is established.** The only successful compilation here is a direct diagnostic of the generic tree cost layer, using existing imported objects. There was no full normal rebuild or independent audit, and no missing upstream dependency builds were launched.

| Source | Current status |
| --- | --- |
| [TreeDegreeBounds.lean](ResearchBounds/TreeDegreeBounds.lean) | Diagnostic compilation succeeded with pinned Lean, `-j2` and `autoImplicit=false`. |
| [FreshBitDegreeBounds.lean](ResearchBounds/FreshBitDegreeBounds.lean) | Uncompiled candidate. Diagnostic stopped at missing `OnlineWordCost.olean`, before checking theorem bodies. |
| [FiniteWordDegreeBounds.lean](ResearchBounds/FiniteWordDegreeBounds.lean) | Uncompiled candidate. No diagnostic was launched. |
| [PolynomialCompilerDegree.lean](ResearchBounds/PolynomialCompilerDegree.lean) | Diagnostic failed; frozen without repair. |

The tree layer fixes the actual realizer and codec. It reconstructs degree certificates for identity, projections, constants, composition, pairing, congruence, measure conversion and list folds. A fold with callback degree `e` and a proved intermediate-state polynomial of degree `s` has allowance `1+e*s`, assuming `1≤e` and `1≤s`. The sampler's cubic state cap therefore gives `3e+1`; the callback certificate and state-size premise still have to be supplied for the actual program.

The fresh-bit candidate proposes numeric range degree 3, coin-list degree 2, and composed fresh-word degree 6 in the measure `n+weight n`. Those are **uncompiled candidates**. The finite-word candidate proposes

```
E_online = max(1,E_draw) * max(E_count,6)
E_physical = 2 * E_online
```

where `E_count` and `E_draw` must certify the actual complete public word-count and public-draw realizers. Applying the existing public word-measure envelope once would give `340*E_online`. These formulas do not supply numerical values for the missing certificates. The candidate compiler witness retains packing, stack execution, tape erasure and output unpacking/printing.

The separate polynomial-expression diagnostic failed because its definitions need noncomputable declarations and three degree steps failed to simplify variable natural-number coefficients as constants. It asserts no physical-machine runtime theorem. Its [exact failed log](diagnostics/PolynomialCompilerDegree-attempt-1.log) is retained.

## Evidence and reproduction

[Diagnostic results](diagnostics/results.json) record every attempt's return code, compiler hash, source hashes before and after, and direct import-object hashes. Three earlier tree diagnostic failures and the final successful attempt are retained. Earlier failing source versions are identified by hash but are not included; their logs are historical repair evidence, not reproduction targets for the final source.

The [source manifest](source-manifest.json) records the frozen drafts and inspected dependency snapshots. The [redaction manifest](redaction-manifest.json) records original and published log hashes and path substitutions. All four Lean sources retain their exact original bytes. No binary objects, account paths or host paths are included.

Pins:

- [OpenAI Math](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb): `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
- [mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612): `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Lean toolchain: `leanprover/lean4:v4.34.1`. Recorded compiler SHA-256: `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`. This is the binary used for these diagnostics; compiler hashes can differ across platforms.

Use a fresh clone of [EcoDataLab/contingency-tables](https://github.com/EcoDataLab/contingency-tables). The repository's [bootstrap script](../../scripts/bootstrap_lean.sh) installs Elan and the pinned Lean toolchain inside the checkout, populates the pinned upstream and mathlib checkouts, and retrieves the dependency cache using the committed manifest. Do not run `lake update`. From the repository root, the following uses the same environment settings as [verify_lean.sh](../../scripts/verify_lean.sh) and reproduces the tree diagnostic into a separate object directory; no globally installed Elan, Lake or Lean is required:

```sh
bash scripts/bootstrap_lean.sh
export ELAN_HOME="$PWD/.tools/elan"
export ELAN_TOOLCHAIN="$(cat formal/lean-toolchain)"
export MATHLIB_CACHE_DIR="$PWD/.tools/mathlib-cache"
cd formal
../.tools/elan/bin/lake build OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure
mkdir -p ../research/runtime-degree/diagnostic-objects/ResearchBounds
../.tools/elan/bin/lake env bash -c 'export LEAN_PATH="../research/runtime-degree/diagnostic-objects:$LEAN_PATH"; lean --root=../research/runtime-degree -j2 -DautoImplicit=false -o ../research/runtime-degree/diagnostic-objects/ResearchBounds/TreeDegreeBounds.olean ../research/runtime-degree/ResearchBounds/TreeDegreeBounds.lean'
```

The [missing dependency manifest](missing-upstream-closure.json) records 43 pinned upstream sources in topological order with SHA-256 hashes: 24 through `OnlineWordCost`, then 19 additional modules through `FiniteWordMachine`. Building the corresponding targets enables the remaining diagnostic attempts:

```sh
../.tools/elan/bin/lake build OAI.Combinatorics.MatchingCount.Complexity.OnlineWordCost OAI.Combinatorics.ContingencyTables.Machines.FiniteWordMachine
../.tools/elan/bin/lake env bash -c 'export LEAN_PATH="../research/runtime-degree/diagnostic-objects:$LEAN_PATH"; lean --root=../research/runtime-degree -j2 -DautoImplicit=false -o ../research/runtime-degree/diagnostic-objects/ResearchBounds/FreshBitDegreeBounds.olean ../research/runtime-degree/ResearchBounds/FreshBitDegreeBounds.lean'
../.tools/elan/bin/lake env bash -c 'export LEAN_PATH="../research/runtime-degree/diagnostic-objects:$LEAN_PATH"; lean --root=../research/runtime-degree -j2 -DautoImplicit=false -o ../research/runtime-degree/diagnostic-objects/ResearchBounds/FiniteWordDegreeBounds.olean ../research/runtime-degree/ResearchBounds/FiniteWordDegreeBounds.lean'
```

Run the final command only after the fresh-bit module succeeds. These commands are next-round instructions, not builds performed in this stage. Failures must be recorded and any repairs saved as new candidate versions before normal verification and independent review.

## Remaining numerical obligations

Supply degree certificates for the actual parser, schedule and word-count DAG, and the complete public-draw DAG. The latter includes both sampler branches, initialization/fallback, canonical dense draws and their fallback, lattice decoding, every inner and outer trial, capped folds, chunking/copying, and final printing. The pinned first-success implementation maps all supplied trials before selection, so its certificate must charge every trial.

An existential `PolynomialTime` result alone cannot supply either missing numerical degree. A certificate for an ideal completion oracle or replacement implementation also cannot fill the premise for these fixed realizers. None of these draft sources uses `sorry`, `admit`, a new axiom or `native_decide`.
