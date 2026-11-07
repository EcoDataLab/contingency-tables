#!/usr/bin/env bash
# Main ordinary verification: the preserved baseline and current public research.
# Bare Lake Math115 remains the baseline library; Comparator has a separate flow.
set -euo pipefail

TASK_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TASK_MODE="${1:---serial}"
if [[ $# -gt 2 || ! "$TASK_MODE" =~ ^(--serial|parallel)$ ]]; then
  echo "Usage: $0 [--serial|parallel] [NEW_OUTPUT_DIRECTORY]" >&2
  exit 2
fi
if [[ $# -eq 2 ]]; then
  case "$2" in /*) TASK_RUN_ROOT=$2 ;; *) TASK_RUN_ROOT="$PWD/$2" ;; esac
  mkdir -p "$(dirname "$TASK_RUN_ROOT")"
  mkdir "$TASK_RUN_ROOT" # Existing evidence is never overwritten.
else
  mkdir -p "$TASK_ROOT/.local/main-lean"
  TASK_RUN_ROOT=$(mktemp -d "$TASK_ROOT/.local/main-lean/attempt-XXXXXXXX")
fi

TASK_STAGE=source-plan
TASK_BASELINE_STATUS=not_run
TASK_INTEGRATION_STATUS=not_run
record_outcome() {
  TASK_EXIT_CODE=$?
  trap - EXIT
  python3 - "$TASK_RUN_ROOT" "$TASK_EXIT_CODE" "$TASK_STAGE" \
    "$TASK_BASELINE_STATUS" "$TASK_INTEGRATION_STATUS" <<'PY' || TASK_EXIT_CODE=$?
from pathlib import Path
import json, sys
output, code, stage, baseline, integration = sys.argv[1:]
output, code = Path(output), int(code)
passed = code == 0 and baseline == integration == 'passed'
if passed:
    try:
        receipt = json.loads((output/'integration/verification.json').read_text())
        required = {
            'Math115.PhysicalDefectTrace.actualRationalTrace_poincare_d8',
            'Math115.AggregateDefectTrace.actualRationalTrace_poincare_aggregate_aspect_sq',
            'Math115.PhysicalTraceJoin.executableSampler_contract',
        }
        if receipt['status'] != 'passed' or not required <= {h['name'] for h in receipt['headlines']}:
            raise ValueError('main integration receipt omits a required chain/program headline')
    except (OSError, ValueError, KeyError) as error:
        print(error, file=sys.stderr)
        passed, code, stage, integration = False, 1, 'integration-receipt', 'failed'
if not passed:
    code = code or 1
    baseline = 'failed' if baseline == 'running' else baseline
    integration = 'failed' if integration == 'running' else integration
record = {
    'schema_version': 1, 'status': 'passed' if passed else 'failed', 'exit_code': code,
    'failed_stage': None if passed else stage,
    'baseline': {'scope': 'focused', 'status': baseline, 'log': 'baseline.log'},
    'integration': {'scope': 'integration-sampler', 'status': integration,
                    'log': 'integration.log', 'receipt': 'integration/verification.json'},
    'source_plan': 'source-plan.json',
    'scope': 'Ordinary focused baseline plus current public research sources and selected chain/program audits in one invocation; trusted bootstrap/imports, no Comparator or new runtime claim.',
}
(output/'main-verification.json').write_text(json.dumps(record, indent=2)+'\n')
print('Main ordinary verification: '+record['status']+'; evidence: '+str(output))
raise SystemExit(code)
PY
  exit "$TASK_EXIT_CODE"
}
trap record_outcome EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

echo "Main verification evidence: $TASK_RUN_ROOT"
cd "$TASK_ROOT"
python3 research/repair-accept/verify.py --scope integration-sampler --plan \
  > "$TASK_RUN_ROOT/source-plan.json"
TASK_STAGE=baseline
TASK_BASELINE_STATUS=running
bash scripts/verify_lean.sh focused "$TASK_MODE" 2>&1 | tee "$TASK_RUN_ROOT/baseline.log"
TASK_BASELINE_STATUS=passed
TASK_STAGE=integration
TASK_INTEGRATION_STATUS=running
python3 research/repair-accept/verify.py --scope integration-sampler \
  --output "$TASK_RUN_ROOT/integration" 2>&1 | tee "$TASK_RUN_ROOT/integration.log"
TASK_INTEGRATION_STATUS=passed
TASK_STAGE=complete
