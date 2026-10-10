# Compiled environment audit of the integrated aggregate

This records a successful fresh native Windows environment audit after the
normal integrated aggregate build. Its explicit prefix and defining-module
filters enumerated **22,710 declarations**, including **16,549 theorem
constants**, and checked **six headline dependency closures**. The imported
Lean environment contains **11,849 modules**. These counts include pinned
upstream code and generated/private constants; they are not counts of new
project theorems or of every declaration in all external packages.

The source-bound project/upstream graph contains 583 normal modules. That
normal build freshly compiled one aggregate root and validated/reused 582
existing objects. The audit helper and environment audit then ran fresh.
The [receipt](verification.json) records their successful exits and actual
compiler identity. The normal source binding is the recorded checkout base
plus frozen source/object hashes, rather than a fresh current-HEAD or Linux
claim.

## Complete report and exact headline types

[environment-audit.stdout.json.gz](environment-audit.stdout.json.gz) contains
**all 149,192,527 original stdout bytes**, without truncation, redaction or
statement replacement. Its decompressed SHA-256 is
`bf0fa0e2dc770358b783ff5526e35f0c14da2adb866677bab25d57f62f5a62b6`.
The deterministic gzip is about 14.37 MB, below Git's single-file size limit.
The gzip filename is empty, its timestamp is zero, and compression level is
nine; [compression.json](compression.json) records compressed and uncompressed
hashes, sizes and replay parameters. Only text is compressed; no `.olean`,
`.ilean`, executable or library binary is included.

[headlines.json](headlines.json) preserves each exact compiled headline type,
including its quantifiers/hypotheses as printed by the frozen helper, defining module, kind, direct dependencies
and axiom set. English claim text, hypotheses and limitations were copied from
the hash-qualified `claims.json` snapshot. They were not strengthened during
projection. Complete closure declarations remain in the raw report:

| Exact headline | Reachable declarations |
| --- | ---: |
| `Math115.CompletionSamplerProgram.polynomial_draw` | 9,795 |
| `Math115.CompletionSamplerSemantics.draw_semantics` | 40,568 |
| `Math115.IdealRepairRefinement.feasibleChain_poincare_d17_refined` | 22,070 |
| `Math115.LatticeScheduleProgram.polynomial_schedule` | 9,244 |
| `Math115.PhysicalBooleanSampler.draw` | 15,711 |
| `Math115.PhysicalBooleanSampler.draw_explicit_accuracy` | 43,025 |

These closures overlap, so their counts must not be added. The finite-word draw
is a typed noncomputable construction; the completion and schedule costs are
component costs. The report supplies no full encoded outer walker, public
random-machine implementation, or complete sampler runtime exponent.

## Reproduction sources and input binding

`run_environment_audit.py` is the **exact runner that executed**, SHA-256
`fc5dee3ccb4469a976f39ef6acf39db36208892faa3f9978265d69a8245e1db9`.
`EnvironmentAudit.lean` is the exact compiled helper source, and `Audit.lean`
is the exact executed import/filter/headline driver. Their hashes and the
helper-object hash are recorded. The current optimized runner was not
substituted for the executed runner in this bundle.

`config.json` is a public-safe projection of the frozen configuration. It
retains every expected declaration/module, pin and digest, while physical paths
use the roles in [redactions.json](redactions.json). To reexecute, restore those
roles to a pinned native workspace with the recorded source/object/compiler
identities, place `EnvironmentAudit.lean` under `ResearchAudit/`, and invoke:

```text
python run_environment_audit.py --config <resolved-config.json> --output <new-empty-attempt-directory>
```

This template is not a new execution receipt. Another platform or source state
requires a new audit and its own hashes. The original runner's large-closure
validation is slower than the later optimization, but its original bytes are
preserved.

The compile before/after snapshots were byte-identical; the audit before/after
snapshots were byte-identical. [input-inventories.json.gz](input-inventories.json.gz)
therefore stores the two unique complete snapshots once each, with both original
before/after hashes. The helper-compilation snapshot binds 1,268 files and
69,189 inventory artifacts. The environment-audit snapshot binds **1,269
files and 69,190 artifacts**, adding the compiled helper object. All paths and
hashes remain represented in the projected snapshots. No inventory is sampled.

[imported-object-closure.json.gz](imported-object-closure.json.gz) retains every
resolved imported module/object hash under public-safe path roles. The
original configuration, receipt, report, snapshot and downloaded archive
hashes remain in `verification.json`. The original archive SHA-256 is
`688599b44eaf52ff88257e5b1d58576de42ba8f0c860b5af547ac0ad472db7c7`.
The frozen compiler is Lean 4.34.1, with source and object pins tied to OpenAI
revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Trust and scope

The audit inspected compiled declarations, defining modules, exact types,
direct type/value dependencies and transitive axiom dependencies. The helper
rejects nonstandard axioms in selected declarations and headline roots; the
runner additionally checks every headline closure record. All permitted
axioms are among `propext`, `Classical.choice` and `Quot.sound`.

The filters select `Math115`, `OAI.ContingencyTables`, and
`OAI.Combinatorics.ContingencyTables`, plus the complete 583-module defining
scope. Private declarations in selected defining modules are included.
The audit helper itself is excluded. External Lean/Mathlib declarations can
appear in headline dependency closures without becoming new project results.

Known compiler/loader override variables were cleared and the process PATH
was limited to the pinned compiler directory. The official external cache,
compiler/toolchain, operating system loader and libraries, Python interpreter
and standard library, and platform services remain trusted. This is a
compiler/import input audit, **not an OS sandbox or strict Comparator replay**.

No theorem statement, mathematical exponent, empirical performance claim,
new HEAD/Linux result, full original three-export replay, or pending encoded
Boolean-walker/public-machine result is inferred from these counts. Earlier
named audits and historical receipts retain their own separate scope.
The candidate awaits independent readback before publication.
