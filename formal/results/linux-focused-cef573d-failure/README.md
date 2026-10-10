# Linux focused failure at cef573d

The [focused workflow](https://github.com/EcoDataLab/contingency-tables/actions/runs/38028745299) **failed** at source commit `cef573d3c8e6ea6ada9a6e869439f974c28a69f4`. Its normal Lean build and all **1,236 ordered selected axiom reports passed** before the environment-audit runner rejected a missing Lake inventory directory, `formal/.lake/packages/Cli/.lake/build/lib`. The original [outcome](outcome.json) remains failed.

The complete raw [verification log](verification.log) records successful Lake builds ending at 8,948 and 9,507 jobs, then the exact named audit and the runner failure. Those job counts include trusted dependency-cache work; they are not new-theorem counts. The focused run did not perform the separate six-name standalone audit, strict Comparator replay, or an environment-derived theorem inventory. No helper compilation or environment-audit success is recorded; the failure occurred during initial input inventory collection.

## Preserved evidence

All **nine downloaded artifact members** retain their exact bytes. `manifest.json` records original archive names, public paths, byte sizes and SHA-256 hashes; environment-attempt files are placed under a visible folder rather than the artifact's hidden `.local` hierarchy. Public hosted-runner paths in the raw files are intentionally preserved. No signed download metadata or URL is copied.

Artifact `11662082123`, `math115-linux-focused-38028745299-1`, has 192,881 archive bytes and SHA-256 `5ff6e700199c74399dec913b8612f1d833c8b8c10cf08bc975efb3a334a1aa5b`. The downloaded bytes match that authenticated artifact digest. Run `38028745299`, job `114145052080`, and the failed conclusion were matched to authenticated metadata. This packaging step ran no Lean/compiler, workflow or remote job.

`AxiomAudit.lean` is the exact audit driver at the source commit. `axiom-audit.log` extracts the contiguous report block from the raw verification log; it was strictly checked for every requested name in order, no duplicate/extra output, and only `propext`, `Classical.choice`, and `Quot.sound`, or subsets. `source-validation.json` records 153 environment source hashes matched to committed Git blobs and the prepared source/configuration pins matched to this commit or the pinned upstream revision. Those inventories include evidence/audit files; they do not assert that every recorded file was compiled.

To reparse the saved named audit without compiling:

```sh
python3 scripts/check_lean_axioms.py formal/results/linux-focused-cef573d-failure/AxiomAudit.lean < formal/results/linux-focused-cef573d-failure/axiom-audit.log
```

## Scope and resumption

The OpenAI source pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and Mathlib is `d13f23b723b8a846827a245b89c10fc7d3f11612`; the log records Lean 4.34.1 for Linux x86_64. The official toolchain/cache and hosted operating environment remain trusted. Normal compiler/selected-axiom success is partial evidence, **not an overall workflow pass**, exhaustive environment audit, built-in-kernel comparison, literal outer-sampler verification, or complete runtime claim.

Preserve this failure receipt and original files. A runner change or rerun is a new source-bound attempt requiring its own logs and final outcome; it cannot upgrade this attempt retroactively. This bundle deliberately supplies no successful environment inventory, Comparator result, or revised-runner proof.
