#!/usr/bin/env bash
# Prepared commands, not an executed public-path replay.
set -euo pipefail
TASK_REPO="$PWD"
TASK_PACKET="$TASK_REPO/research/runtime-degree/checkpoints/actual-printer-degree-v1"
TASK_HELPERS="${1:?Pass the existing generic degree helper object root}"
TASK_OUTPUT="${2:?Pass a new private output directory}"
case "$TASK_HELPERS" in /*) ;; *) TASK_HELPERS="$TASK_REPO/$TASK_HELPERS" ;; esac
case "$TASK_OUTPUT" in /*) ;; *) TASK_OUTPUT="$TASK_REPO/$TASK_OUTPUT" ;; esac
test ! -e "$TASK_OUTPUT"
mkdir -p "$TASK_OUTPUT/PrinterRuntime" "$TASK_OUTPUT/logs"
cd formal
for TASK_MODULE in LinearCollections PrinterDegree; do
  ../.tools/elan/bin/lake env bash -c '
    export LEAN_PATH="$1:$2${LEAN_PATH:+:$LEAN_PATH}"
    lean --root="$3" -j2 -M8192 -DautoImplicit=false \
      -o "$1/PrinterRuntime/$4.olean" "$3/PrinterRuntime/$4.lean"
  ' _ "$TASK_OUTPUT" "$TASK_HELPERS" "$TASK_PACKET" "$TASK_MODULE" \
    >"$TASK_OUTPUT/logs/$TASK_MODULE.stdout.txt" \
    2>"$TASK_OUTPUT/logs/$TASK_MODULE.stderr.txt"
done
../.tools/elan/bin/lake env bash -c '
  export LEAN_PATH="$1:$2${LEAN_PATH:+:$LEAN_PATH}"
  lean -j2 -M8192 -DautoImplicit=false "$3/PrinterAudit.lean"
' _ "$TASK_OUTPUT" "$TASK_HELPERS" "$TASK_PACKET" \
  >"$TASK_OUTPUT/logs/audit.stdout.txt" 2>"$TASK_OUTPUT/logs/audit.stderr.txt"
python3 -B "$TASK_PACKET/check_audit.py" <"$TASK_OUTPUT/logs/audit.stdout.txt"
