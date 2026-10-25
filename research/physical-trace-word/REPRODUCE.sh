#!/usr/bin/env bash
set -euo pipefail
# Reuse prepared imports; compile only this additive bridge module and inspect its environment.
PACKET=$(cd -- "$(dirname -- "$0")" && pwd -P)
TASK_REPO=$(cd -- "$PACKET/../.." && pwd -P)
if [[ $# -ne 1 || -z "${LEAN_PATH:-}" ]]; then
  echo 'Usage: LEAN_PATH=<prepared dependency object paths> bash REPRODUCE.sh NEW_OUTPUT_DIRECTORY' >&2
  exit 2
fi
case "$1" in /*) RUN_OUT=$1 ;; *) RUN_OUT="$PWD/$1" ;; esac
LEAN_BIN=${LEAN_BIN:-"$TASK_REPO/.tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"}
mkdir "$RUN_OUT" # Existing evidence is never overwritten.
mkdir -p "$RUN_OUT/objects/ResearchPhysicalTraceJoin"
# Merge reused namespace roots, including this module's namespace; an earlier partial root must not hide
# an accepted module in a later root. Earlier LEAN_PATH entries keep priority.
python3 - "$RUN_OUT/objects" "$LEAN_PATH" <<'PYMERGE'
from pathlib import Path
import os, sys
output = Path(sys.argv[1])
for namespace in ['Math115', 'OAI', 'ResearchComparison', 'ResearchPhysicalTraceJoin']:
    for root in reversed([Path(p) for p in sys.argv[2].split(os.pathsep) if p]):
        for source in (root / namespace).rglob('*.olean'):
            if namespace == 'ResearchPhysicalTraceJoin' and source.relative_to(root / namespace) == Path('Word.olean'):
                continue  # Never overwrite a supplied copy of the module being rebuilt.
            target = output / namespace / source.relative_to(root / namespace)
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.is_symlink():
                target.unlink()
            target.symlink_to(source.resolve())
PYMERGE
export LEAN_PATH="$RUN_OUT/objects:$LEAN_PATH"
export LEAN_NUM_THREADS=2
"$LEAN_BIN" --version > "$RUN_OUT/compiler-version.txt"
"$LEAN_BIN" -j2 -M8192 -DautoImplicit=false --root="$PACKET/formal" \
  -o "$RUN_OUT/objects/ResearchPhysicalTraceJoin/Word.olean" \
  "$PACKET/formal/ResearchPhysicalTraceJoin/Word.lean" \
  > "$RUN_OUT/compilation.stdout.txt" 2> "$RUN_OUT/compilation.stderr.txt"
"$LEAN_BIN" -j2 -M8192 -DautoImplicit=false "$PACKET/attempt-01/ResearchScopeAudit.lean" \
  > "$RUN_OUT/audit.json" 2> "$RUN_OUT/audit.stderr.txt"
python3 - "$RUN_OUT/audit.json" <<'PY'
import json, sys
audit = json.load(open(sys.argv[1]))
for declaration in audit['declarations']:
    assert not declaration['nonstandard_axioms'], declaration['name']
for headline in audit['headlines']:
    names = set(headline['closure'])
    assert names == {d['name'] for d in headline['declarations']}
    for declaration in headline['declarations']:
        assert set(declaration['dependencies']) <= names, declaration['name']
        assert not declaration['nonstandard_axioms'], declaration['name']
print('Additive bridge module compiled; all enumerated declarations and headline closures use standard axioms.')
PY
