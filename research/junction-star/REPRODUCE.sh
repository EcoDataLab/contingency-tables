#!/usr/bin/env bash
set -euo pipefail
# Target only this helper against an already authenticated import root.
PACKET=$(cd -- "$(dirname -- "$0")" && pwd -P)
TASK_REPO=${TASK_REPO:-$(git -C "$PACKET" rev-parse --show-toplevel)}
if [[ $# -ne 2 ]]; then
  echo 'Usage: REPRODUCE.sh AUTHENTICATED_IMPORT_ROOT NEW_OUTPUT_DIRECTORY' >&2
  exit 2
fi
IMPORT_ROOT=$(cd -- "$1" && pwd -P)
case "$2" in /*) RUN_OUT=$2 ;; *) RUN_OUT="$PWD/$2" ;; esac
LEAN_BIN=${LEAN_BIN:-"$TASK_REPO/.tools/elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"}
case "$LEAN_BIN" in /*) ;; *) LEAN_BIN="$PWD/$LEAN_BIN" ;; esac
python3 - "$PACKET" "$IMPORT_ROOT" "$RUN_OUT" "$TASK_REPO" "$LEAN_BIN" <<'PY'
import hashlib, json, pathlib, sys
packet, base, out, repo, lean = map(pathlib.Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
binding = json.loads((packet/'source-bindings.json').read_text())
assert sha(packet/binding['source']) == binding['sha256'], 'Helper source pin mismatch'
required = json.loads((packet/'required-imports.json').read_text())
assert sha(lean) == required['compiler_sha256'], 'Captured compiler pin mismatch'
for row in required['imports']:
    assert sha(repo/row['source']) == row['source_sha256'], 'Prior source pin mismatch'
    p = base/pathlib.Path(row['module'].replace('.','/')+'.olean')
    assert sha(p) == row['olean_sha256'], 'Prior object pin mismatch'
out.mkdir()  # Existing output directories are rejected; prior evidence is preserved.
(out/'objects/Research').mkdir(parents=True)
for p in base.iterdir():
    if p.name == 'Research':
        for q in p.iterdir():
            if q.name.startswith('JunctionStarBridge.'):
                continue
            (out/'objects/Research'/q.name).symlink_to(q, target_is_directory=q.is_dir())
    else:
        (out/'objects'/p.name).symlink_to(p, target_is_directory=p.is_dir())
PY
# The caller supplies the established upstream/mathlib import paths in LEAN_PATH.
export LEAN_PATH="$RUN_OUT/objects:$IMPORT_ROOT${LEAN_PATH:+:$LEAN_PATH}"
export LEAN_NUM_THREADS=2
"$LEAN_BIN" --version > "$RUN_OUT/compiler-version.txt"
"$LEAN_BIN" -j2 -M8192 -DautoImplicit=false --root="$PACKET/formal" \
  -o "$RUN_OUT/objects/Research/JunctionStarBridge.olean" \
  "$PACKET/formal/Research/JunctionStarBridge.lean" \
  > "$RUN_OUT/compilation.stdout.txt" 2> "$RUN_OUT/compilation.stderr.txt"
"$LEAN_BIN" -j2 -M8192 -DautoImplicit=false "$PACKET/Audit.lean" \
  > "$RUN_OUT/audit.json" 2> "$RUN_OUT/audit.stderr.txt"
python3 "$PACKET/check_audit.py" "$RUN_OUT/audit.json"
