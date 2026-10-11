#!/usr/bin/env bash
# Prepared source reproduction instructions; not run during packet preparation.
# This does not change or certify the repository's default Linux target.
set -euo pipefail
bash scripts/bootstrap_lean.sh
export ELAN_HOME="$PWD/.tools/elan"
export ELAN_TOOLCHAIN="$(cat formal/lean-toolchain)"
export MATHLIB_CACHE_DIR="$PWD/.tools/mathlib-cache"
TASK_REPO="$PWD"
TASK_HELPERS="$TASK_REPO/research/runtime-degree/checkpoints/generic-helpers-v1"
TASK_PACKET="$TASK_REPO/research/runtime-degree/checkpoints/actual-count-draw-helpers-v1"
TASK_OBJECTS="$TASK_REPO/.local/actual-count-draw-helper-replay-v1"
test ! -e "$TASK_OBJECTS"
mkdir -p "$TASK_OBJECTS/ResearchBounds" "$TASK_OBJECTS/CountBounds" "$TASK_OBJECTS/logs"
cd formal
../.tools/elan/bin/lake build \
  OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure \
  OAI.Combinatorics.MatchingCount.Complexity.OnlineWordCost \
  OAI.Combinatorics.ContingencyTables.Machines.FiniteWordMachine \
  OAI.Combinatorics.MatchingCount.Tapes.Codec \
  Math115.PublicLatticeSampler Math115.LatticeUnitWalk

compile_source() {
  local TASK_SOURCE_ROOT="$1" TASK_MODULE="$2"
  local TASK_RELATIVE="${TASK_MODULE//.//}"
  ../.tools/elan/bin/lake env bash -c '
    export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
    lean --root="$2" -j2 -M8192 -DautoImplicit=false \
      -o "$1/$3.olean" -i "$1/$3.ilean" "$2/$3.lean"
  ' _ "$TASK_OBJECTS" "$TASK_SOURCE_ROOT" "$TASK_RELATIVE" \
    >"$TASK_OBJECTS/logs/$TASK_MODULE.stdout.log" \
    2>"$TASK_OBJECTS/logs/$TASK_MODULE.stderr.log"
}
for TASK_SHORT in TreeDegreeBounds PolynomialCompilerDegree FreshBitDegreeBounds FiniteWordDegreeBounds TreeArithmeticDegree ScalarOutputSizeDegree WordCountSeedDegrees; do
  compile_source "$TASK_HELPERS" "ResearchBounds.$TASK_SHORT"
done
for TASK_MODULE in CountBounds.ListRepeatDegree ResearchBounds.DrawControlDegree CountBounds.ParserDegree ResearchBounds.CatalogueLeafDegrees ResearchBounds.SmallCellCatalogueDegree CountBounds.ScalarCircuitDegreeV2 CountBounds.TightWordCountDegreeV2 ResearchBounds.DrawWalkDegree ResearchBounds.DrawAssemblyDegree; do
  compile_source "$TASK_PACKET" "$TASK_MODULE"
  TASK_DRIVER="${TASK_MODULE//./_}"
  ../.tools/elan/bin/lake env bash -c '
    export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
    lean --root="$2/audit-source" -j2 -M8192 -DautoImplicit=false \
      "$2/audit-source/Checkpoint12Audits/$3.lean"
  ' _ "$TASK_OBJECTS" "$TASK_PACKET" "$TASK_DRIVER" \
    >"$TASK_OBJECTS/logs/$TASK_DRIVER.audit.stdout.log" \
    2>"$TASK_OBJECTS/logs/$TASK_DRIVER.audit.stderr.log"
  python3 "$TASK_PACKET/audit/check_lean_axioms.py" \
    "$TASK_PACKET/audit-source/Checkpoint12Audits/$TASK_DRIVER.lean" \
    <"$TASK_OBJECTS/logs/$TASK_DRIVER.audit.stdout.log"
done
