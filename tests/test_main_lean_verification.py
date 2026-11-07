"""Exercise the real main shell entrypoint with source-aware checker fixtures."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
REQUIRED_HEADLINES = {
    'Math115.PhysicalDefectTrace.actualRationalTrace_poincare_d8',
    'Math115.AggregateDefectTrace.actualRationalTrace_poincare_aggregate_aspect_sq',
    'Math115.PhysicalTraceJoin.executableSampler_contract',
}


class MainLeanVerificationTests(unittest.TestCase):
    def test_main_scope_and_failure_evidence_with_spaced_paths(self):
        manifest = json.loads((ROOT / 'research/repair-accept/integration-sampler.json').read_text())
        self.assertLessEqual(REQUIRED_HEADLINES, set(manifest['headlines']))
        for failure, expected in [('', 0), ('baseline', 23), ('integration', 124), ('missing-aspect', 1)]:
            with self.subTest(failure=failure), tempfile.TemporaryDirectory(prefix='main verification ') as temporary:
                root = Path(temporary) / 'checkout with spaces'
                scripts = root / 'scripts'
                scripts.mkdir(parents=True)
                shutil.copyfile(ROOT / 'scripts/verify_main.sh', scripts / 'verify_main.sh')
                (scripts / 'verify_lean.sh').write_text('''#!/usr/bin/env bash
set -euo pipefail
test "$1" = focused
test "$2" = --serial
if [[ "${FAKE_MAIN_FAILURE:-}" == baseline ]]; then
  echo 'baseline failed' >&2
  exit 23
fi
touch .baseline-passed
echo 'baseline passed'
''')
                packet = root / 'research/repair-accept'
                packet.mkdir(parents=True)
                (packet / 'integration-sampler.json').write_text(json.dumps(manifest))
                (packet / 'verify.py').write_text('''import argparse, json, os, sys
from pathlib import Path
root = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser()
parser.add_argument('--scope', required=True)
parser.add_argument('--plan', action='store_true')
parser.add_argument('--output', type=Path)
args = parser.parse_args()
assert args.scope == 'integration-sampler'
manifest = json.loads((Path(__file__).parent/'integration-sampler.json').read_text())
assert 'Math115.PhysicalTraceJoin.executableSampler_contract' in manifest['headlines']
if args.plan:
    print(json.dumps(manifest))
    raise SystemExit(0)
assert (root/'.baseline-passed').is_file(), 'integration ran before baseline passed'
if os.environ.get('FAKE_MAIN_FAILURE') == 'integration':
    print('integration timed out; partial output retained', file=sys.stderr)
    raise SystemExit(124)
args.output.mkdir()
headlines = manifest['headlines']
if os.environ.get('FAKE_MAIN_FAILURE') == 'missing-aspect':
    headlines = [h for h in headlines if not h.endswith('_aggregate_aspect_sq')]
(args.output/'verification.json').write_text(json.dumps({
    'status': 'passed', 'headlines': [{'name': h} for h in headlines]}))
print('integration passed')
''')
                output = Path(temporary) / 'output with spaces'
                result = subprocess.run(
                    ['bash', str(scripts / 'verify_main.sh'), '--serial', str(output)],
                    cwd=Path(temporary), env={**os.environ, 'FAKE_MAIN_FAILURE': failure},
                    capture_output=True, text=True, timeout=15)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
                record = json.loads((output / 'main-verification.json').read_text())
                self.assertEqual(record['exit_code'], expected)
                self.assertEqual(record['status'], 'passed' if expected == 0 else 'failed')
                self.assertTrue((output / 'source-plan.json').is_file())
                if failure == 'baseline':
                    self.assertEqual(record['failed_stage'], 'baseline')
                    self.assertEqual(record['integration']['status'], 'not_run')
                    self.assertFalse((output / 'integration.log').exists())
                elif failure == 'integration':
                    self.assertEqual(record['failed_stage'], 'integration')
                    self.assertIn('timed out', (output / 'integration.log').read_text())
                    self.assertEqual(record['baseline']['status'], 'passed')
                elif failure == 'missing-aspect':
                    self.assertEqual(record['failed_stage'], 'integration-receipt')
                else:
                    self.assertIsNone(record['failed_stage'])
                    self.assertEqual(record['baseline']['status'], 'passed')
                    self.assertEqual(record['integration']['status'], 'passed')


if __name__ == '__main__':
    unittest.main()
