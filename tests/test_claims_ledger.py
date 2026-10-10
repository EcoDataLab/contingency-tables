import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('claims_ledger', ROOT / 'scripts/claims_ledger.py')
ledger = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ledger)


class ClaimsLedgerTests(unittest.TestCase):
    def setUp(self):
        self.document = json.loads((ROOT / 'claims.json').read_text(encoding='utf-8'))

    def test_delivered_scopes_replay_and_linux_overlap_is_not_added(self):
        result = ledger.validate_ledger(ROOT, self.document)
        self.assertEqual({k: v['count'] for k, v in result['scopes'].items()},
                         {'integrated-aggregate': 1242, 'aggregate': 869, 'encoded-completion': 46,
                          'physical-bridges': 193, 'boolean-schedule': 134, 'linux-focused': 863})
        self.assertEqual(result['disjoint_count'], 1242)
        self.assertTrue(set(result['scopes']['linux-focused']['names']) <=
                        set(result['scopes']['integrated-aggregate']['names']))
        historic_union = set().union(*(set(result['scopes'][i]['names']) for i in ['aggregate','encoded-completion','physical-bridges','boolean-schedule']))
        self.assertEqual(set(result['scopes']['integrated-aggregate']['names']), historic_union)
        self.assertEqual(result['current_receipt'], 'integrated-aggregate')
        self.assertEqual(result['scopes']['integrated-aggregate']['module_counts']['Math115'], 1236)

    def test_changed_receipt_digest_and_unknown_status_fail(self):
        changed = copy.deepcopy(self.document)
        changed['receipts'][0]['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'digest mismatch'):
            ledger.validate_ledger(ROOT, changed)
        changed = copy.deepcopy(self.document)
        changed['receipts'][0]['status'] = 'failed'
        with self.assertRaisesRegex(ValueError, 'not passed'):
            ledger.validate_ledger(ROOT, changed)

    def test_an_omitted_headline_is_not_verified_by_a_large_count(self):
        changed = copy.deepcopy(self.document)
        changed['claims'][0]['headlines'][0]['name'] = 'Math115.IdealRepairRefinement.UnrequestedTheorem'
        with self.assertRaisesRegex(ValueError, 'lacks named'):
            ledger.validate_ledger(ROOT, changed)

    def test_claim_scope_is_bound_and_overlap_claim_fails(self):
        changed = copy.deepcopy(self.document)
        changed['claims'][0]['evidence'][0]['scope'] = 'all project theorems'
        with self.assertRaisesRegex(ValueError, 'scope differs'):
            ledger.validate_ledger(ROOT, changed)
        changed = copy.deepcopy(self.document)
        changed['disjoint_component_scopes'].append('linux-focused')
        with self.assertRaisesRegex(ValueError, 'overlap'):
            ledger.validate_ledger(ROOT, changed)

    def test_headline_cannot_be_bound_to_an_unrelated_verified_source(self):
        changed = copy.deepcopy(self.document)
        changed['claims'][0]['sources'] = ['formal/Math115/RepairCoefficient.lean']
        changed['claims'][0]['headlines'][0]['source'] = 'formal/Math115/RepairCoefficient.lean'
        with self.assertRaisesRegex(ValueError, 'attribution differs'):
            ledger.validate_ledger(ROOT, changed)
        changed['claims'][0]['headlines'][0]['module'] = 'Math115.RepairCoefficient'
        with self.assertRaisesRegex(ValueError, 'attribution differs'):
            ledger.validate_ledger(ROOT, changed)
        changed['claims'][0]['headlines'][0]['module'] = 'Math115'
        changed['claims'][0]['headlines'][0]['source'] = 'formal/Math115.lean'
        changed['claims'][0]['sources'] = ['formal/Math115.lean']
        with self.assertRaisesRegex(ValueError, 'attribution differs'):
            ledger.validate_ledger(ROOT, changed)

    def test_commit_binding_kinds_cannot_invent_or_drop_base_commit(self):
        changed = copy.deepcopy(self.document)
        changed['receipts'][0]['commit_kind'] = 'source_hashes_only'
        with self.assertRaisesRegex(ValueError, 'must not invent'):
            ledger.validate_ledger(ROOT, changed)
        changed = copy.deepcopy(self.document)
        next(r for r in changed['receipts'] if r['id']=='boolean-schedule')['commit_kind'] = 'base_commit_plus_source_hashes'
        with self.assertRaisesRegex(ValueError, 'requires a recorded'):
            ledger.validate_ledger(ROOT, changed)

    def test_changed_raw_log_fails_even_when_receipt_count_is_unchanged(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = 'import Lean\n#print axioms Example.test\n'
            output = "'Example.test' does not depend on any axioms\n"
            (root / 'driver.lean').write_text(source)
            (root / 'audit.log').write_text(output)
            files = {n: ledger.digest(root / n) for n in ['driver.lean', 'audit.log']}
            receipt = {'status': 'passed', 'allowed_axioms': sorted(ledger.ALLOWED),
                       'source_checkout_base_commit': 'a' * 40, 'total_audited_declarations': 1,
                       'artifacts_sha256': files,
                       'modules': [{'module': 'Example', 'source': 'Example.lean', 'source_sha256': 'b' * 64,
                           'declaration_count': 1, 'declarations': [{'name': 'Example.test', 'axioms': []}],
                           'compile': {'exit_code': 0}, 'audit': {'status': 'passed', 'exit_code': 0,
                               'driver': 'driver.lean', 'log': 'audit.log',
                               'driver_sha256': files['driver.lean'], 'log_sha256': files['audit.log']}}]}
            (root / 'verification.json').write_text(json.dumps(receipt))
            binding = {'id': 'test', 'path': 'verification.json', 'sha256': ledger.digest(root / 'verification.json'),
                       'status': 'passed', 'commit': 'a' * 40, 'commit_kind': 'base_commit_plus_source_hashes',
                       'label': 'test', 'scope': 'selected test'}
            self.assertEqual(ledger.validate_receipt(root, binding)['count'], 1)
            (root / 'audit.log').write_text(output + 'compiler warning\n')
            with self.assertRaisesRegex(ValueError, 'artifact digest'):
                ledger.validate_receipt(root, binding)

    def test_generated_section_replacement_preserves_outside_and_requires_markers(self):
        old = 'before\n' + ledger.BEGIN + '\nold\n' + ledger.END + '\nafter\n'
        new = ledger.BEGIN + '\nnew\n' + ledger.END + '\n'
        self.assertEqual(ledger.replace_generated(old, new), 'before\n' + new + 'after\n')
        for text in ['missing', old + ledger.BEGIN, ledger.END + ledger.BEGIN]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                ledger.replace_generated(text, new)

    def test_audit_driver_uses_receipt_modules_and_every_ledger_headline(self):
        result = ledger.validate_ledger(ROOT, self.document)
        driver = ledger.audit_driver(result, self.document['disjoint_component_scopes'])
        self.assertIn('import Math115.PhysicalBooleanSampler', driver)
        self.assertIn('prefixes [Math115, OAI.ContingencyTables', driver)
        for claim in self.document['claims']:
            for headline in claim['headlines']:
                self.assertIn(headline['name'], driver)
        self.assertNotIn('#print axioms', driver)

    def test_empty_claims_cannot_leave_only_counts(self):
        changed = copy.deepcopy(self.document)
        changed['claims'] = []
        with self.assertRaisesRegex(ValueError, 'nonempty headline'):
            ledger.validate_ledger(ROOT, changed)

    def test_current_summary_prefers_integrated_scope_without_adding_historical_overlap(self):
        result=ledger.validate_ledger(ROOT,self.document)
        rendered=ledger.render(result)
        self.assertIn('**1242** named declarations (1236 focused + 6 standalone)',rendered)
        self.assertIn('**863** named declarations',rendered)
        for count in [869,46,193,134]:
            self.assertNotIn('**'+str(count)+'** named declarations',rendered)
        self.assertIn('overlap the current integrated aggregate and are not added',rendered)
        self.assertIn('docs/formal-verification.md',rendered)
        for claim in self.document['claims']:
            if claim['evidence_class'].startswith('lean_'):
                self.assertEqual([e['receipt'] for e in claim['evidence']],['integrated-aggregate'])

    def test_historical_changed_sources_cannot_be_promoted_to_current(self):
        changed=copy.deepcopy(self.document)
        changed['current_receipt']='aggregate'
        changed['summary_receipt_ids']=['aggregate','linux-focused']
        changed['disjoint_component_scopes']=['aggregate']
        with self.assertRaisesRegex(ValueError,'current receipt source bytes differ'):
            ledger.validate_ledger(ROOT,changed)

    def test_summary_cannot_hide_current_receipt_or_reference_unvalidated_scope(self):
        for summary in [['linux-focused'],['missing'],['integrated-aggregate','integrated-aggregate']]:
            changed=copy.deepcopy(self.document);changed['summary_receipt_ids']=summary
            with self.subTest(summary=summary), self.assertRaises(ValueError):
                ledger.validate_ledger(ROOT,changed)

    def test_paths_cannot_escape_the_repository(self):
        for path in ['/tmp/private', '../outside', '']:
            with self.subTest(path=path), self.assertRaises(ValueError):
                ledger.local_path(ROOT, path)


class CleanCloneSourceChecks(unittest.TestCase):
    """Synthetic receipts exercise parser/source integrity, not a Lean proof."""
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.owned = 'formal/Math115/Example.lean'
        self.dependency = 'formal/Math115/Dependency.lean'
        self.upstream = '.upstream/openai-math/lean/OAI/Example.lean'
        self.upstream_bytes = b'theorem external : True := True.intro\n'
        for relative in [self.owned, self.dependency]:
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'theorem headline : True := True.intro\n')
        driver = 'import Math115.Example\n#print axioms Math115.Example.headline\n'
        output = "'Math115.Example.headline' does not depend on any axioms\n"
        (self.root / 'driver.lean').write_text(driver, encoding='utf-8')
        (self.root / 'audit.log').write_text(output, encoding='utf-8')
        self.source_hashes = {p: ledger.digest(self.root / p) for p in [self.owned, self.dependency]}
        self.source_hashes[self.upstream] = hashlib.sha256(self.upstream_bytes).hexdigest()
        closure = {'records': [{'source': p, 'source_sha256': h} for p, h in self.source_hashes.items()]}
        (self.root / 'source-closure.json').write_text(json.dumps(closure), encoding='utf-8')
        files = {p: ledger.digest(self.root / p) for p in ['driver.lean', 'audit.log', 'source-closure.json']}
        self.receipt = {
            'status': 'passed', 'allowed_axioms': sorted(ledger.ALLOWED),
            'source_checkout_base_commit': 'a' * 40, 'upstream_revision': 'b' * 40,
            'total_audited_declarations': 1, 'artifacts_sha256': files, 'source_closure': 'source-closure.json',
            'modules': [{'module': 'Math115.Example', 'source': self.owned,
                'source_sha256': self.source_hashes[self.owned], 'declaration_count': 1,
                'declarations': [{'name': 'Math115.Example.headline', 'axioms': []}],
                'compile': {'exit_code': 0}, 'audit': {'status': 'passed', 'exit_code': 0,
                    'driver': 'driver.lean', 'log': 'audit.log',
                    'driver_sha256': files['driver.lean'], 'log_sha256': files['audit.log']}}]}
        self.binding = {'id': 'current', 'path': 'verification.json', 'status': 'passed',
                        'commit': 'a' * 40, 'commit_kind': 'base_commit_plus_source_hashes',
                        'label': 'synthetic parser regression', 'scope': 'synthetic fixture'}
        self.document = {'schema_version': 1, 'receipts': [self.binding], 'current_receipt': 'current',
                         'summary_receipt_ids': ['current'], 'disjoint_component_scopes': ['current'],
                         'claims': [{'id': 'fixture', 'title': 'fixture', 'english_claim': 'fixture',
                             'quantity': 'fixture', 'hypotheses': ['fixture'], 'limitations': ['synthetic'],
                             'evidence_class': 'lean_theorem', 'sources': [self.owned],
                             'headlines': [{'name': 'Math115.Example.headline', 'module': 'Math115.Example', 'source': self.owned}],
                             'evidence': [{'receipt': 'current', 'scope': 'synthetic fixture'}]}]}
        self.save_receipt()

    def save_receipt(self):
        path = self.root / 'verification.json'
        path.write_text(json.dumps(self.receipt), encoding='utf-8')
        self.binding['sha256'] = ledger.digest(path)

    def test_clean_clone_preserves_exact_upstream_digest_and_reports_unchecked(self):
        result = ledger.validate_ledger(self.root, self.document)
        scope = result['scopes']['current']
        self.assertEqual(scope['current_source_mismatches'], [])
        self.assertEqual(scope['unchecked_upstream_source_sha256'], {self.upstream: self.source_hashes[self.upstream]})
        self.assertEqual(scope['source_hashes'], self.source_hashes)
        self.assertIn('absent checkout files are explicitly reported as unchecked', ledger.render(result))

    def test_any_present_upstream_file_is_checked_and_changes_reject_current(self):
        path = self.root / self.upstream
        path.parent.mkdir(parents=True)
        path.write_bytes(self.upstream_bytes)
        result = ledger.validate_ledger(self.root, self.document)
        self.assertEqual(result['scopes']['current']['checked_upstream_sources'], [self.upstream])
        self.assertEqual(result['scopes']['current']['unchecked_upstream_source_sha256'], {})
        path.write_bytes(b'changed upstream source')
        with self.assertRaisesRegex(ValueError, 'current receipt source bytes differ'):
            ledger.validate_ledger(self.root, self.document)

    def test_missing_or_changed_owned_dependency_remains_a_blocker(self):
        path = self.root / self.dependency
        path.write_bytes(b'changed owned dependency')
        with self.assertRaisesRegex(ValueError, 'current receipt source bytes differ'):
            ledger.validate_ledger(self.root, self.document)
        path.unlink()
        with self.assertRaisesRegex(ValueError, 'current receipt source bytes differ'):
            ledger.validate_ledger(self.root, self.document)

    def test_missing_or_changed_headline_source_remains_a_blocker(self):
        path = self.root / self.owned
        path.write_bytes(b'changed owned headline source')
        with self.assertRaisesRegex(ValueError, 'current receipt source bytes differ'):
            ledger.validate_ledger(self.root, self.document)
        path.unlink()
        with self.assertRaisesRegex(ValueError, 'current receipt source bytes differ'):
            ledger.validate_ledger(self.root, self.document)

    def test_unpinned_absent_upstream_is_not_exempt(self):
        del self.receipt['upstream_revision']
        self.save_receipt()
        with self.assertRaisesRegex(ValueError, 'current receipt source bytes differ'):
            ledger.validate_ledger(self.root, self.document)

    def test_a_present_nonfile_upstream_path_is_not_treated_as_absent(self):
        (self.root / self.upstream).mkdir(parents=True)
        with self.assertRaisesRegex(ValueError, 'current receipt source bytes differ'):
            ledger.validate_ledger(self.root, self.document)

    def test_other_ignored_prefix_cannot_hide_missing_owned_inputs(self):
        checks = ledger.source_checks(self.root, {'.upstream/other/lean/Source.lean': 'a' * 64}, 'b' * 40)
        self.assertEqual(checks['unchecked_upstream_source_sha256'], {})
        self.assertEqual(checks['current_source_mismatches'], ['.upstream/other/lean/Source.lean'])


if __name__ == '__main__':
    unittest.main()
