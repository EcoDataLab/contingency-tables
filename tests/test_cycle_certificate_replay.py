"""Historical producer identity is separate from exact certificate validity."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('cycle_certificate_replay', ROOT / 'experiments/cycle_mixtures.py')
experiment = importlib.util.module_from_spec(spec)
spec.loader.exec_module(experiment)


class CertificateReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report_path = ROOT / 'reports/cycle-mixtures.json'
        cls.saved_bytes = cls.report_path.read_bytes()
        cls.saved = json.loads(cls.saved_bytes)
        cls.current_sources = {path: experiment.sha256(ROOT / path) for path in experiment.SOURCE_PATHS}

    def test_historical_witnesses_recheck_and_report_producer_drift(self):
        result = experiment.replay_report(self.saved, experiment.DEFAULT_FIXTURE)
        self.assertEqual((result['verified_gap_intervals'], result['verified_family_upper_bounds'],
                          result['verified_strict_improvements']), (8, 4, 6))
        drift = sorted(path for path in experiment.SOURCE_PATHS
                       if self.saved['source_sha256'][path] != self.current_sources[path])
        self.assertEqual(result['producer_sources_match'], not drift)
        self.assertEqual(result['producer_source_mismatches'], drift)
        self.assertEqual(result['verification_source_sha256'], self.current_sources)
        self.assertEqual(self.report_path.read_bytes(), self.saved_bytes)

    def test_strict_producer_identity_rejects_valid_historical_witnesses(self):
        changed = copy.deepcopy(self.saved)
        changed['source_sha256'] = dict(self.current_sources)
        source = experiment.SOURCE_PATHS[0]
        changed['source_sha256'][source] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'producer sources have changed'):
            experiment.replay_report(changed, experiment.DEFAULT_FIXTURE, check_source_hashes=True)

    def test_strict_identity_still_rechecks_the_certificate(self):
        changed = copy.deepcopy(self.saved)
        changed['source_sha256'] = dict(self.current_sources)
        first_case = next(iter(next(iter(changed['laws'].values()))['cases'].values()))
        first_case['gap_lower']['bound'] = '2'
        with self.assertRaisesRegex(ValueError, 'invalid lower certificate'):
            experiment.replay_report(changed, experiment.DEFAULT_FIXTURE, check_source_hashes=True)

    def test_mathematical_and_provenance_mismatches_remain_errors(self):
        for field, error in [('fixture_sha256', 'fixture provenance'),
                             ('state_order_sha256', 'state order')]:
            changed = copy.deepcopy(self.saved)
            changed[field] = '0' * 64
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, error):
                experiment.replay_report(changed, experiment.DEFAULT_FIXTURE)
        changed = copy.deepcopy(self.saved)
        next(iter(changed['laws'].values()))['stationary'][0] = '0'
        with self.assertRaisesRegex(ValueError, 'stationary law'):
            experiment.replay_report(changed, experiment.DEFAULT_FIXTURE)
        changed = copy.deepcopy(self.saved)
        del changed['source_sha256'][experiment.SOURCE_PATHS[0]]
        with self.assertRaisesRegex(ValueError, 'invalid producer source provenance'):
            experiment.replay_report(changed, experiment.DEFAULT_FIXTURE)


if __name__ == '__main__':
    unittest.main()
