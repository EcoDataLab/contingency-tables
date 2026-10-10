#!/usr/bin/env bash
set -euo pipefail

TASK_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export ELAN_HOME="$TASK_ROOT/.tools/elan"
export MATHLIB_CACHE_DIR="$TASK_ROOT/.tools/mathlib-cache"
VERIFY_SCOPE="${1:-focused}"
VERIFY_MODE="${2:-parallel}"
if [[ $# -gt 2 || ! "$VERIFY_SCOPE" =~ ^(standalone|focused|full|comparator)$ || \
      ! "$VERIFY_MODE" =~ ^(parallel|--serial)$ ]]; then
  echo "Usage: $0 [standalone|focused|full|comparator] [--serial]" >&2
  exit 2
fi
if [[ "$VERIFY_SCOPE" == comparator && "$VERIFY_MODE" == --serial ]]; then
  echo "Serial compilation is not Comparator replay; use a fresh Comparator environment." >&2
  exit 2
fi
VERIFY_LOG="$TASK_ROOT/formal/results/$VERIFY_SCOPE.log"
[[ "$VERIFY_MODE" != --serial ]] || VERIFY_LOG="$TASK_ROOT/formal/results/$VERIFY_SCOPE-serial.log"
mkdir -p "$TASK_ROOT/formal/results"

audit_axioms() {
  local audit_file="$1" audit_output
  audit_output="$("$ELAN_HOME/bin/lake" env lean "$audit_file")"
  printf '%s\n' "$audit_output"
  printf '%s\n' "$audit_output" | python3 "$TASK_ROOT/scripts/check_lean_axioms.py" "$audit_file"
}

[[ "$(git -C "$TASK_ROOT/.upstream/openai-math" rev-parse HEAD)" == \
  fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb ]]
git -C "$TASK_ROOT/.upstream/openai-math" diff --quiet
git -C "$TASK_ROOT/.upstream/openai-math" diff --cached --quiet
cmp "$TASK_ROOT/formal/lean-toolchain" "$TASK_ROOT/.upstream/openai-math/lean/lean-toolchain"
export ELAN_TOOLCHAIN="$(cat "$TASK_ROOT/formal/lean-toolchain")"

serial_build() {
  python3 "$TASK_ROOT/scripts/build_lean_serial.py" "$VERIFY_SCOPE"
}

verify() {
  cd "$TASK_ROOT/formal"
  date -u '+Verification started: %Y-%m-%dT%H:%M:%SZ'
  printf 'Verification scope: %s; build mode: %s\n' "$VERIFY_SCOPE" "$VERIFY_MODE"
  "$ELAN_HOME/bin/lake" env lean --version
  case "$VERIFY_SCOPE" in
    standalone)
      if [[ "$VERIFY_MODE" == --serial ]]; then
        serial_build
      else
        "$ELAN_HOME/bin/lake" build Math115.QuadraticCoefficient Math115.GlobalDisplayOwnership \
          Math115.RepairCoefficient
      fi
      audit_axioms Math115/StandaloneAxiomAudit.lean
      ;;
    focused)
      if [[ "$VERIFY_MODE" == --serial ]]; then
        serial_build
      else
        "$ELAN_HOME/bin/lake" build \
          OAI.Combinatorics.ContingencyTables.Transport.IntegerLeafEnergy \
          OAI.Combinatorics.ContingencyTables.Transport.IntegerRootTransport
        "$ELAN_HOME/bin/lake" build Math115
      fi
      audit_axioms Math115/AxiomAudit.lean
      mkdir -p "$TASK_ROOT/.local/environment-audits"
      AUDIT_WORK=$(mktemp -d "$TASK_ROOT/.local/environment-audits/focused-XXXXXXXX")
      "$ELAN_HOME/bin/lake" env python3 "$TASK_ROOT/scripts/prepare_environment_audit.py" \
        --root "$TASK_ROOT" --output "$AUDIT_WORK/config.json"
      python3 "$TASK_ROOT/scripts/run_environment_audit.py" \
        --config "$AUDIT_WORK/config.json" --output "$AUDIT_WORK/attempt"
      ;;
    full)
      if [[ "$VERIFY_MODE" == --serial ]]; then
        serial_build
      else
        "$ELAN_HOME/bin/lake" build \
          OAI.Combinatorics.ContingencyTables.UnconditionalMain \
          ComparatorChallenges.ContingencyTables
      fi
      audit_axioms Math115/UpstreamAxiomAudit.lean
      ;;
    comparator)
      [[ "$(uname -s)" == Linux ]] || {
        echo "Comparator's real Landrun sandbox requires Linux; no Comparator pass claimed." >&2
        return 2
      }
      command -v comparator >/dev/null
      command -v landrun >/dev/null
      command -v lean4export >/dev/null
      command -v systemd-run >/dev/null
      systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --wait --pipe \
        -E "PATH=$PATH" -E "ELAN_HOME=$ELAN_HOME" -E "MATHLIB_CACHE_DIR=$MATHLIB_CACHE_DIR" \
        --working-directory "$TASK_ROOT/formal" -- \
        "$ELAN_HOME/bin/lake" env comparator \
          ../.upstream/openai-math/lean/ComparatorChallenges/ContingencyTables.json
      ;;
  esac
  date -u '+Verification completed: %Y-%m-%dT%H:%M:%SZ'
}

# Logs are safe to publish: no machine-specific absolute workspace paths.
verify 2>&1 | python3 -u -c \
  'import sys; [sys.stdout.write(line.replace(sys.argv[1], "<workspace>")) for line in sys.stdin]' \
  "$TASK_ROOT" | tee "$VERIFY_LOG"
