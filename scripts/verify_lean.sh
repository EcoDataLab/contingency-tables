#!/usr/bin/env bash
set -euo pipefail

TASK_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export ELAN_HOME="$TASK_ROOT/.tools/elan"
export MATHLIB_CACHE_DIR="$TASK_ROOT/.tools/mathlib-cache"
VERIFY_SCOPE="${1:-focused}"
VERIFY_LOG="$TASK_ROOT/formal/results/$VERIFY_SCOPE.log"
mkdir -p "$TASK_ROOT/formal/results"

audit_axioms() {
  local audit_file="$1" audit_output
  audit_output="$("$ELAN_HOME/bin/lake" env lean "$audit_file")"
  printf '%s\n' "$audit_output"
  python3 - "$audit_output" <<'PY'
import re, sys
output = sys.argv[1]
matches = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
assert matches, "No axiom reports found"
allowed = {"propext", "Classical.choice", "Quot.sound"}
for report in matches:
    actual = {name.strip() for name in report.split(",") if name.strip()}
    assert actual <= allowed, f"Unexpected axioms: {actual - allowed}"
print(f"Axiom allowlist passed for {len(matches)} declarations.")
PY
}

[[ "$(git -C "$TASK_ROOT/.upstream/openai-math" rev-parse HEAD)" == \
  fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb ]]
git -C "$TASK_ROOT/.upstream/openai-math" diff --quiet
git -C "$TASK_ROOT/.upstream/openai-math" diff --cached --quiet
cmp "$TASK_ROOT/formal/lean-toolchain" "$TASK_ROOT/.upstream/openai-math/lean/lean-toolchain"

verify() {
  cd "$TASK_ROOT/formal"
  date -u '+Verification started: %Y-%m-%dT%H:%M:%SZ'
  "$ELAN_HOME/bin/lake" env lean --version
  case "$VERIFY_SCOPE" in
    standalone)
      "$ELAN_HOME/bin/lake" build Math115.QuadraticCoefficient Math115.GlobalDisplayOwnership \
        Math115.RepairCoefficient
      audit_axioms Math115/StandaloneAxiomAudit.lean
      ;;
    focused)
      "$ELAN_HOME/bin/lake" build \
        OAI.Combinatorics.ContingencyTables.Transport.IntegerLeafEnergy \
        OAI.Combinatorics.ContingencyTables.Transport.IntegerRootTransport
      "$ELAN_HOME/bin/lake" build Math115
      audit_axioms Math115/AxiomAudit.lean
      ;;
    full)
      "$ELAN_HOME/bin/lake" build \
        OAI.Combinatorics.ContingencyTables.UnconditionalMain \
        ComparatorChallenges.ContingencyTables
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
    *) echo "Usage: $0 [standalone|focused|full|comparator]" >&2; return 2 ;;
  esac
  date -u '+Verification completed: %Y-%m-%dT%H:%M:%SZ'
}

# Logs are safe to publish: no machine-specific absolute workspace paths.
verify 2>&1 | python3 -u -c \
  'import sys; [sys.stdout.write(line.replace(sys.argv[1], "<workspace>")) for line in sys.stdin]' \
  "$TASK_ROOT" | tee "$VERIFY_LOG"
