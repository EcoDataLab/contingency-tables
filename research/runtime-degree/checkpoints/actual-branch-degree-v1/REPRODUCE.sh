#!/usr/bin/env bash
# Prepared public-path reproduction instructions; not a recorded execution.
set -euo pipefail
TASK_REPO="$PWD"
TASK_PACKET="$TASK_REPO/research/runtime-degree/checkpoints/actual-branch-degree-v1"
TASK_HELPER_OBJECTS="${1:?Pass the existing actual helper packet object root}"
TASK_OUTPUT="${2:?Pass a NEW private output directory}"
case "$TASK_HELPER_OBJECTS" in
  /*) ;;
  *) TASK_HELPER_OBJECTS="$TASK_REPO/$TASK_HELPER_OBJECTS" ;;
esac
case "$TASK_OUTPUT" in
  /*) ;;
  *) TASK_OUTPUT="$TASK_REPO/$TASK_OUTPUT" ;;
esac
test ! -e "$TASK_OUTPUT"
mkdir -p "$TASK_OUTPUT/DrawRuntime" "$TASK_OUTPUT/logs"
cd formal
for TASK_MODULE in RangeSeed BranchDegree; do
  ../.tools/elan/bin/lake env bash -c '
    export LEAN_PATH="$1:$2${LEAN_PATH:+:$LEAN_PATH}"
    lean --root="$3" -j2 -M6144 -DautoImplicit=false \
      -o "$1/DrawRuntime/$4.olean" "$3/DrawRuntime/$4.lean"
  ' _ "$TASK_OUTPUT" "$TASK_HELPER_OBJECTS" "$TASK_PACKET" "$TASK_MODULE" \
    >"$TASK_OUTPUT/logs/$TASK_MODULE.stdout.txt" \
    2>"$TASK_OUTPUT/logs/$TASK_MODULE.stderr.txt"
done
../.tools/elan/bin/lake env bash -c '
  export LEAN_PATH="$1:$2${LEAN_PATH:+:$LEAN_PATH}"
  lean -j2 -M6144 -DautoImplicit=false "$3/BranchAudit.lean"
' _ "$TASK_OUTPUT" "$TASK_HELPER_OBJECTS" "$TASK_PACKET" \
  >"$TASK_OUTPUT/logs/audit.stdout.txt" 2>"$TASK_OUTPUT/logs/audit.stderr.txt"
python3 "$TASK_PACKET/check_audit.py" <"$TASK_OUTPUT/logs/audit.stdout.txt"
