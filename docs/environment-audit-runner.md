# Reproducing the compiled environment audit

The environment runner enumerates declarations through the reviewed Lean
helper after importing the built aggregate. A source import graph determines
which compiled project modules must be present; it never supplies a theorem
roster. The Lean environment supplies every selected theorem, its complete
type, axiom dependencies, and each headline's exact proof/type dependency
closure. Previously audited declaration names are additional inclusion checks.

After the normal project build, run preparation under Lake's environment so
it resolves the pinned compiler and existing object search paths:

```sh
mkdir -p .local/environment-audits
AUDIT_WORK=$(mktemp -d "$PWD/.local/environment-audits/focused-XXXXXXXX")
(cd formal && ../.tools/elan/bin/lake env python3 ../scripts/prepare_environment_audit.py \
  --output "$AUDIT_WORK/config.json" --driver-output "$AUDIT_WORK/Audit.lean")
python3 scripts/run_environment_audit.py \
  --config "$AUDIT_WORK/config.json" --output "$AUDIT_WORK/attempt"
```

The attempt directory must not exist. Each failure is retained with its raw
stdout/stderr, process exit code, before/after snapshots, and receipt. Preparing
a config invokes the compiler only for its version and installed-prefix
queries; it does not build project modules or download dependency objects.
The runner compiles the audit helper in a separate library whose only package
prefix is `ResearchAudit`. This prevents a partial `Math115` directory from
shadowing the authenticated project library.

The runner hashes the source/configuration pins, normal module objects, and
all import-significant artifacts across the selected object and native-library
search directories before and after helper compilation and the audit. These
inventories include `.olean`, `.olean.private`, `.olean.server`, `.ir`,
`.ir.sig`, `.ilean`, and native shared libraries. After compilation, the helper
library is inventoried too. The actual compiler prefix must agree with the
configured builtin library. Source-bound imported module names must exactly
match the frozen project graph; extra cached Lean/Mathlib modules remain
within the stated dependency-cache boundary.

A successful compiler exit is necessary. Nonempty stderr, invalid JSON
framing, duplicate JSON keys, scope discrepancies, omitted modules/headlines,
inconsistent theorem counts, nonstandard axioms, or a dependency closure with
missing or unrelated declarations fail validation. The helper, driver,
runner, Python executable, compiler, input inventories, and output hashes are
bound in the private receipt. Known native-loader override variables are
removed and the compiler directory is the only PATH entry. The operating
system, system loader/libraries, and Python standard library remain trusted;
this is an input-integrity audit, not an operating-system sandbox.

For saved native normal builds, `prepare_environment_audit.py` also accepts
`--normal-evidence` and an explicit `--native-helper-source`. It binds the
complete delivered source/object graph, reused normal dependencies, frozen
runtime/configuration metadata, and authenticated external boundary objects.
Its exact native config is private because it contains execution paths.

The private full-project audit must pass before its exhaustive declaration or
theorem totals are promoted into public claims. Publishing a receipt requires
separate projection/review of private paths and runtime provenance. A small
fixture success establishes runner behavior, not a full project audit.

## Default verification integration

`scripts/verify_lean.sh focused` runs this after the focused build and selected
axiom audit, using a unique attempt directory:

```sh
mkdir -p "$TASK_ROOT/.local/environment-audits"
AUDIT_WORK=$(mktemp -d "$TASK_ROOT/.local/environment-audits/focused-XXXXXXXX")
"$ELAN_HOME/bin/lake" env python3 "$TASK_ROOT/scripts/prepare_environment_audit.py" \
  --root "$TASK_ROOT" --output "$AUDIT_WORK/config.json"
python3 "$TASK_ROOT/scripts/run_environment_audit.py" \
  --config "$AUDIT_WORK/config.json" --output "$AUDIT_WORK/attempt"
```

The wrapper's `set -e` and `pipefail` make a failed environment
audit fail the fresh Linux verification target. Preserve the selected audit
for historical comparability while the compiled environment becomes the
coverage authority. CI retains the attempt on success or failure. Public hosted
runner paths appear in its raw CI artifacts; receipts committed to the repository
receive a separate provenance and path review.
