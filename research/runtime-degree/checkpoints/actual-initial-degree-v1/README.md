# Actual initialization and fallback degree certificates

The exact frozen initial-configuration realizer has a polynomial bound of degree at most **4032** on charged work plus binary encoded output weight, for every literal pair of natural-margin lists and natural precision parameter. The exact greedy fallback realizer has degree at most **18**. Both named endpoints compiled locally with pinned Lean 4.34.1; a compiled-environment audit checked 63 owned declarations, 61 theorem constants including generated declarations, and five complete headline dependency closures. All use only standard Lean axioms. [Verification](verification.json) saves their exact types and source/object/compiler hashes.

The endpoints are `Math115.InitialRuntimeNext.typed_actual_initialConfiguration`, `actual_initialConfiguration_polynomial`, and `typed_actual_initialFallback` in [InitialDegree.lean](InitialRuntime/InitialDegree.lean). The fallback is definitionally the original `GreedyFeasibleTable.tableRealizer`, certified by `typed_actual_greedyTable` in [GreedyDegree.lean](InitialRuntime/GreedyDegree.lean).

No feasibility, equal-total, successful-parse, nonempty-dimension or desired-cost premise is supplied. The typed input domain is arbitrary natural lists and precision values; this includes empty lists, unequal totals and other values not satisfying the sampler's mathematical input conditions. It does not claim a bound for arbitrary malformed tree encodings outside the realizer's codec domain.

The programs and codecs are unchanged. The greedy proof derives a linear `12X+10` intermediate row-accumulator envelope and a quadratic `12(X+1)^2` table-accumulator envelope, retaining arbitrary preexisting accumulator contents. Its degree18 includes every row/table fold, projection, tuple copy, final reversal and encoded matrix output.

The initial proof uses the [actual catalogue1008 certificate](../actual-count-draw-helpers-v1/README.md), exact dimension/cutoff circuits from the [branch packet](../actual-branch-degree-v1/README.md), greedy18, and the original matrix-entry reads, maps and complement calculations. Independent cubic/quartic output-size estimates keep initial views at degree1008 and initial-check data preparation at4032. The final tuple also charges padding, dimension, precision and repeated views. The initializer prepares the original profile-check data; it does not assert that arbitrary input margins are feasible.

These certificates address the `initial` and `fallback` fields of the historical `ActualDrawSeams` interface. They supply no complete public-draw degree, packed-trial or retry certificate, physical machine-runtime degree, measured sampler speed, default-target rebuild or strict challenge acceptance. Compilation timings are compiler timings.

## Reused prerequisites and verification scope

The owned source modules were freshly compiled on the local arm64 compiler. The audit used those exact newly compiled objects. Prior authenticated native Windows sampler/helper objects were copied into a new read-only local import prefix and successfully imported by the local compiler; they were **reused**, not rebuilt. The source/object hashes for those overlays are recorded in [reused import bindings](evidence/reused-native-bindings.json), with the [portability probes](evidence/object-portability.json). The full imported-object inventory and complete audit are compressed under `evidence/`. Binary objects and private cache trees are not distributed.

The public verification receipt projects private source paths to the byte-identical source files in this packet, preserving exact theorem types, hashes, timings and outcomes. It records the original receipt hash and the substitution. Earlier failed native initial-source diagnostics remain preserved separately; they are not described as successful executions.

[Independent AI source/evidence review passed](SOURCE_REVIEW.md), including the exact initializer/fallback endpoints and all reused import bindings. No human review or public-platform replay is claimed.

## Prepared source reproduction

Use the repository's existing pinned bootstrap and baseline source workflow, then build the prerequisite sources from the generic-helper, actual-count/draw-helper, branch and printer packets into one shared object namespace. The relevant helper packet is [actual printer degree4](../actual-printer-degree-v1/README.md). Do not run `lake update` or substitute a different compiler/cache revision.

With those exact prerequisites available in `LEAN_PATH`, compile these two files in order into a new object prefix, using pinned Lean4.34.1 and `-DautoImplicit=false`:

    lean --root=research/runtime-degree/checkpoints/actual-initial-degree-v1 -j2 -M8192 \
      -DautoImplicit=false -o "$INITIAL_OBJECTS/InitialRuntime/GreedyDegree.olean" \
      research/runtime-degree/checkpoints/actual-initial-degree-v1/InitialRuntime/GreedyDegree.lean
    lean --root=research/runtime-degree/checkpoints/actual-initial-degree-v1 -j2 -M8192 \
      -DautoImplicit=false -o "$INITIAL_OBJECTS/InitialRuntime/InitialDegree.olean" \
      research/runtime-degree/checkpoints/actual-initial-degree-v1/InitialRuntime/InitialDegree.lean

`INITIAL_OBJECTS` must be a fresh output prefix included first in `LEAN_PATH`, with its `InitialRuntime` directory created. These are prepared commands; a fresh checkout reproduction of the prerequisites has not been executed for this publication. Preserve exits, both diagnostic streams and exact source/object/import bindings when replaying.
