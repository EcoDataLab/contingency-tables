# Integrated native aggregate: 1,236 focused and six standalone audits

This bundle records one successful normal native Windows aggregate build and
four successful strict named audits. The focused driver requested **1,236
names**; three standalone drivers requested two names each. The **1,242 names
are distinct**. They are selected definitions, statements and proofs, rather
than an enumeration of every declaration in the imported Lean environment.

The normal project closure contains 583 internal modules. **One root was
freshly compiled and 582 existing objects were validated and reused** against
the frozen source graph, closure identities and object hashes. The three
standalone objects were also validated reused objects; their short compile
logs are reuse records, not fresh compiler runs. All four axiom audits were
fresh executions. The fresh root compiler log is empty.

The exact root source SHA-256 is
`bc1b3e1148d5a84da433ac71518620035d5ef581ee7f2f09050db5b250746057`.
The root object SHA-256 is
`14f4039699aff30f6561e9ce8072d905c283ab7ecd687be9cc3f424679e492fe`.
The repository focused reproduction roster SHA-256 is
`75523df89d2df8d7c8fd9a664b47b6c07a979ba1e9318a07ebed354379375c0e`.
The generated executed driver has SHA-256
`8373f81481f4084192c554ab7c26730eab60532b4d34f0d482c8f4b81b4d1fae`.
Their ordered requests agree; comments account for their different bytes.

The recorded source checkout base is
`b021f227a21c7e9252eae78c55ab09c404cc66cd`. The proof binding is that base
**plus the explicit frozen source hashes**, including the later root/roster
state. This is not an assertion that the new frozen root was committed at the
base SHA or freshly verified at the current repository HEAD.

## Evidence files

- `verification.json` supplies the compatible named-audit receipt, exact
  counts, module source/object hashes, runtime identity and build/reuse scope.
- `*-Source.lean` files are exact selected source snapshots. The executed
  `*-AxiomCheck.lean` drivers and `*-axiom-audit.log` files are byte-exact.
  The reproduction rosters preserve the repository's commented focused and
  standalone lists; the TSV and plain list retain all requested names.
- `source-closure.json` records all 583 internal source/object bindings and
  direct imports. The exporter authenticated native source/object files;
  packaging rehashed all 583 available source files and four delivered object
  binaries. The complete transitive object binaries were not delivered locally.
- `runtime-provenance.json` retains the pinned compiler/package objects,
  compiler/import-significant environment, complete before/expected/after audit
  input maps and their original canonical hashes. It does not claim complete
  process-environment byte identity or exhaustive declaration enumeration.
- `redaction-mapping.json` documents logical path roles and each projected log
  transformation. `artifact-manifest.json` lists nonreceipt assets. The
  receipt binds that manifest; its own final digest is supplied by the frozen
  package/readback record, avoiding a circular self-hash.
- `source-review.json` records a fresh **AI-agent independent source and
  evidence review** of this candidate. No prior aggregate review was renamed
  or reused; final publication readback remains separate.

The original export archive SHA-256 is
`d4a044a841d7351f8a8f1269393467063285960feabd657f1193881001cc00b9`.
All 45 archive entries, 44 manifested assets and extracted bytes matched.
Before, expected and after input maps were equal; the root audit binds 1,261
inputs. Every report was checked in exact driver order with only `propext`,
`Classical.choice` and `Quot.sound`, or subsets, and no extra audit output.

## Privacy and trust boundaries

Source, axiom and module spellings were preserved. Logs without private paths
are byte-exact. Only the three reuse JSON logs needed redaction: their
`reused_from` native build root becomes `<build>`, while the relative suffix,
other JSON values and line-ending convention remain unchanged. Original and
projected hashes are both recorded. Structured runtime paths use documented
logical tokens. No private account path or internal host nickname is published.

The compiler is Lean 4.34.1 for native Windows; the recorded compiler binary,
Lake binary and package objects have explicit hashes. The OpenAI source pin is
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, and Mathlib is
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The official toolchain and external
package cache remain trusted. This normal build is not a fresh reconstruction
of every imported dependency or an independent kernel replay.

## Scope

The new root imports the previously published completion components and
rechecks their selected names together with the existing focused scope.
The thirteen prospective encoded Boolean step, walker and public-machine
modules listed in `verification.json` are outside this closure and receipt.
The mathematical finite-word output law and numeric schedule components do
not, by themselves, supply the pending literal public random-machine proof.

This bundle supplies no fresh Linux result for the new source state, full
original three-export theorem audit, strict Comparator replay, exhaustive
Lean-environment enumeration, or new practical/runtime benchmark. Earlier
Linux, original-theorem and isolated component receipts retain their exact
historical scope and remain unchanged.

For replay, use the recorded source/configuration freeze and pinned imports,
then run the four executed drivers under the recorded compiler/import settings.
`scripts/check_lean_axioms.py` rechecks the preserved reports without compiling;
its SHA-256 is
`f8a9de8baf9ce2d3d03877f827c72455bdfa60281da7f6e75f54b26a5786035e`.
A later fresh build is a new result and needs its own logs, source identities
and successful receipt.
