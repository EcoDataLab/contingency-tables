"""Source-bound integration failures; no Lean, Lake, Git or remote execution."""
import copy
import importlib.util
import json
from pathlib import Path, PureWindowsPath
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
PUBLISHED_ROOT = ROOT if (ROOT / 'formal/results/native-sampler-checkpoint').exists() else ROOT.parents[2]
if PUBLISHED_ROOT != ROOT:
    sys.path.insert(0, str(PUBLISHED_ROOT / 'scripts'))
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('candidate_prepare', ROOT / 'scripts/prepare_environment_audit.py')
prepare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prepare)


class DefaultContractTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        files = ['formal/Math115.lean', 'formal/Math115/AxiomAudit.lean',
                 'formal/default-audit-contract.json', 'claims.json']
        files += [str(p.relative_to(ROOT)) for p in (ROOT / 'formal/Math115').glob('*.lean')]
        for relative in files:
            p = self.root / relative
            p.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, p)
        for relative in ['formal/Math115/StandaloneAxiomAudit.lean',
                         'formal/results/native-sampler-checkpoint/checkpoint.json',
                         'formal/results/native-sampler-checkpoint/audit/selection.json',
                         'formal/results/native-sampler-checkpoint/audit/intake-verification.json']:
            p = self.root / relative
            p.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(PUBLISHED_ROOT / relative, p)

    def mutate(self, relative, action):
        p = self.root / relative
        value = json.loads(p.read_text())
        action(value)
        p.write_text(json.dumps(value))

    def test_published_sources_and_all_requirements_are_bound(self):
        contract = prepare.default_contract(self.root)
        self.assertEqual(len(contract['modules']), 13)
        self.assertEqual(len(prepare.headlines(self.root)), 22)
        self.assertEqual(len(prepare.previously_audited(self.root)), 1517)
        self.assertEqual(len(prepare.seam_requirements(self.root)['private_source_helpers']), 3)
        self.assertEqual(len(contract['program_identity_requirements']), 2)
        # These are inclusion requests, not a guessed theorem inventory.
        self.assertEqual(sum(len(m['public_declarations']) for m in contract['modules']), 275)

    def test_default_headlines_follow_evidence_scope_even_when_research_uses_math115_namespace(self):
        document = json.loads((self.root / 'claims.json').read_text())
        baseline = prepare.headlines(self.root)
        selected = document['disjoint_component_scopes'][0]
        default = next(r for r in document['receipts'] if r['id'] == selected)
        research = {'id': 'research-selection-fixture', 'format': 'compiled_environment',
                    'scope': 'synthetic additive research selection; no compiler claim'}
        document['receipts'].append(research)
        name = 'Math115.SharedNamespace.researchSelectionFixture'
        claim = {'headlines': [{'name': name}],
                 'evidence': [{'receipt': research['id'], 'scope': research['scope']}]}
        document['claims'].append(claim)
        path = self.root / 'claims.json'
        path.write_text(json.dumps(document))
        self.assertEqual(prepare.headlines(self.root), baseline)
        # Scope selection, rather than the symbol namespace, controls inclusion.
        claim['evidence'] = [{'receipt': selected, 'scope': default['scope']}]
        path.write_text(json.dumps(document))
        self.assertEqual(prepare.headlines(self.root), sorted([*baseline, name]))
        claim['evidence'][0]['scope'] = 'unrelated scope'
        path.write_text(json.dumps(document))
        with self.assertRaisesRegex(ValueError, 'evidence scope differs'):
            prepare.headlines(self.root)

    def test_contract_file_and_published_authorities_are_input_pinned(self):
        pins = prepare.contract_pins(self.root)
        self.assertEqual(len(pins), 4)
        for pin in pins.values():
            self.assertEqual(prepare.sha(Path(pin['path'])), pin['sha256'])
        native = prepare.contract_pins(self.root, PureWindowsPath('C:/candidate'))
        self.assertTrue(all(p['path'].startswith('C:\\candidate\\') for p in native.values()))

    def test_missing_contract_cannot_silently_restore_old_headlines(self):
        (self.root / prepare.CONTRACT).unlink()
        with self.assertRaisesRegex(ValueError, 'requires its source-bound'):
            prepare.headlines(self.root)
        with patch.object(prepare.shutil, 'which') as lookup:
            with self.assertRaises(ValueError):
                prepare.current_config(self.root)
            lookup.assert_not_called()

    def test_aggregate_omission_fails_even_if_module_file_exists(self):
        p = self.root / 'formal/Math115.lean'
        p.write_text(p.read_text().replace('import Math115.LatticeBoundedSampling\n', ''))
        with self.assertRaisesRegex(ValueError, 'omits a required'):
            prepare.default_contract(self.root)

    def test_changed_actual_source_is_rejected(self):
        p = self.root / 'formal/Math115/LatticeSamplerCost.lean'
        p.write_text(p.read_text() + '\n-- changed source bytes\n')
        with self.assertRaisesRegex(ValueError, 'source bytes differ'):
            prepare.default_contract(self.root)

    def test_source_reassignment_and_digest_rewrite_fail(self):
        original = (self.root / prepare.CONTRACT).read_bytes()
        for field, value in [('source', 'formal/Math115.lean'), ('sha256', '0' * 64)]:
            with self.subTest(field=field):
                (self.root / prepare.CONTRACT).write_bytes(original)
                self.mutate(prepare.CONTRACT, lambda c: c['modules'][0].update({field: value}))
                with self.assertRaisesRegex(ValueError, 'contract differs'):
                    prepare.default_contract(self.root)

    def test_headline_private_and_program_obligations_cannot_be_dropped(self):
        original = (self.root / prepare.CONTRACT).read_bytes()
        for field in ['headlines', 'private_source_helpers', 'program_identity_requirements']:
            with self.subTest(field=field):
                (self.root / prepare.CONTRACT).write_bytes(original)
                self.mutate(prepare.CONTRACT, lambda c: c.update({field: []}))
                with self.assertRaisesRegex(ValueError, 'obligations differ'):
                    prepare.default_contract(self.root)

    def test_named_audit_omission_and_unrequested_addition_fail(self):
        p = self.root / 'formal/Math115/AxiomAudit.lean'
        original = p.read_text()
        for changed in [original.replace('#print axioms Math115.LatticeBoundedSampling.boundedSampling\n', ''),
                        original + '\n#print axioms Math115.Unrequested\n']:
            with self.subTest():
                p.write_text(changed)
                with self.assertRaisesRegex(ValueError, 'named audits differ'):
                    prepare.default_contract(self.root)

    def test_published_authority_change_is_rejected(self):
        p = self.root / 'formal/results/native-sampler-checkpoint/audit/selection.json'
        p.write_text(p.read_text() + ' ')
        with self.assertRaisesRegex(ValueError, 'authority differs'):
            prepare.default_contract(self.root)

    def test_duplicate_contract_json_key_is_rejected(self):
        p = self.root / prepare.CONTRACT
        p.write_text(p.read_text().replace('"schema_version": 1', '"schema_version": 1, "schema_version": 1'))
        with self.assertRaisesRegex(ValueError, 'duplicate JSON key'):
            prepare.default_contract(self.root)

    def test_legacy_root_without_integration_keeps_original_contract(self):
        (self.root / prepare.CONTRACT).unlink()
        (self.root / 'formal/Math115.lean').write_text('import Math115.PhysicalBooleanSampler\n')
        self.mutate('claims.json', lambda c: c.update(claims=[
            claim for claim in c['claims'] if claim['id'] != 'complete-bounded-sampler']))
        self.assertIsNone(prepare.default_contract(self.root))
        self.assertEqual(len(prepare.headlines(self.root)), 6)

    def test_saved_old_normal_root_cannot_certify_new_aggregate(self):
        # Synthetic metadata using the actual published old root source digest.
        # This fixture is not a compiler receipt or an actual normal graph.
        published = json.loads((PUBLISHED_ROOT /
            'formal/results/native-sampler-checkpoint/audit/config.json').read_text())
        old_digest = published['pins']['source:Math115']['sha256']
        evidence = self.root / 'normal'
        evidence.mkdir()
        rows = [{'module': 'Math115', 'exit_code': 0, 'reused': True,
                 'source': 'formal/Math115.lean', 'source_unchanged': True,
                 'source_sha256': old_digest}]
        fixture = {'frozen-plan.json': {'modules': [{'name': 'Math115'}]},
                   'modules.json': rows, 'status.json': {'status': 'passed'},
                   'environment-one.json': {}}
        for name, value in fixture.items():
            (evidence / name).write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, 'fresh successful normal compile'):
            prepare.native_config(self.root, evidence, 'C:/helper/EnvironmentAudit.lean')
        # Even relabeling that historical root as fresh cannot hide changed bytes.
        next(r for r in rows if r['module'] == 'Math115')['reused'] = False
        (evidence / 'modules.json').write_text(json.dumps(rows))
        with self.assertRaisesRegex(ValueError, 'root source differs'):
            prepare.native_config(self.root, evidence, 'C:/helper/EnvironmentAudit.lean')

    def test_current_preparation_carries_bound_contract_and_seams_into_runner(self):
        for relative in ['formal/lakefile.lean', 'formal/lake-manifest.json', 'formal/lean-toolchain',
                         'formal/ResearchAudit/EnvironmentAudit.lean']:
            p = self.root / relative
            p.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(PUBLISHED_ROOT / relative, p)
        compiler = self.root / 'toolchain/bin/lean'
        compiler.parent.mkdir(parents=True)
        compiler.write_bytes(b'synthetic compiler identity; never executed')
        contract = prepare.default_contract(self.root)
        sources = [('Math115', self.root / 'formal/Math115.lean')]
        sources += [(m['module'], self.root / m['source']) for m in contract['modules']]
        modules = [prepare.Module(name, path, ()) for name, path in sources]
        objects = {}
        for name, _ in sources:
            obj = self.root / 'objects' / (name + '.olean')
            obj.parent.mkdir(exist_ok=True)
            obj.write_bytes(('synthetic ' + name).encode())
            objects[name] = obj
        def output(argv, **kwargs):
            return str(compiler.parent.parent) + '\n' if argv[-1] == '--print-prefix' else 'Lean fixture\n'
        with patch.object(prepare.shutil, 'which', return_value=str(compiler)), \
                patch.dict(prepare.os.environ, {'LEAN_PATH': str(self.root / 'unused/lib/lean') +
                                               prepare.os.pathsep + str(self.root / 'objects')}), \
                patch.object(prepare.subprocess, 'check_output', side_effect=output), \
                patch.object(prepare, 'dependency_order', return_value=modules), \
                patch.object(prepare, 'resolve_module', side_effect=lambda n, roots: objects[n]):
            config = prepare.current_config(self.root)
        prepare.config_check(config)
        self.assertEqual(config['headlines'], contract['headlines'])
        self.assertEqual(config['private_source_helpers'], contract['private_source_helpers'])
        self.assertEqual(config['program_identity_requirements'], contract['program_identity_requirements'])
        self.assertIn('integration-contract:formal/default-audit-contract.json', config['pins'])
        self.assertEqual(config['lean_path'][0], str(self.root / 'unused/lib/lean'))

    def native_fixture(self):
        """Two-source synthetic metadata only; no claimed object compilation."""
        root = self.root / 'toy-native'
        sources = {'formal/Math115.lean': 'import Math115.Leaf\n',
                   'formal/Math115/Leaf.lean': 'theorem value : True := True.intro\n',
                   'formal/Math115/AxiomAudit.lean': 'import Math115\n#print axioms Math115.Leaf.value\n',
                   'formal/Math115/StandaloneAxiomAudit.lean': 'import Math115\n',
                   'formal/ResearchAudit/EnvironmentAudit.lean': 'import Lean\n',
                   'formal/lean-toolchain': 'leanprover/lean4:v4.34.1\n',
                   'claims.json': json.dumps({'receipts': [{'id': 'default', 'scope': 'synthetic default'}],
                       'disjoint_component_scopes': ['default'],
                       'claims': [{'headlines': [{'name': 'Math115.Leaf.value'}],
                                   'evidence': [{'receipt': 'default', 'scope': 'synthetic default'}]}]})}
        for path, text in sources.items():
            p = root / path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        records, modules = [], []
        for name, relative in [('Math115', 'formal/Math115.lean'), ('Math115.Leaf', 'formal/Math115/Leaf.lean')]:
            imports = list(prepare.lean_imports(sources[relative]))
            modules.append({'name': name, 'source': relative, 'imports': imports})
            records.append({'module': name, 'source': relative, 'source_sha256': prepare.sha(root / relative),
                'source_unchanged': True, 'exit_code': 0, 'reused': name != 'Math115',
                'olean_sha256': ('a' if name == 'Math115' else 'b') * 64,
                'command': ['C:/toy/toolchain/bin/lean.exe', 'C:/toy/formal/Math115.lean'],
                'dependency_olean_sha256': {'Math115.Leaf': 'b' * 64} if name == 'Math115' else {}})
        plan = {'modules': modules, 'input_sha256': {r['source']: r['source_sha256'] for r in records},
                'configuration_sha256': {'formal/lean-toolchain': prepare.sha(root / 'formal/lean-toolchain')}}
        env = {'lean': 'Lean synthetic version', 'lean_sha256': 'c' * 64, 'lake_sha256': 'd' * 64,
               'lean_path': 'C:/normal/lib/lean', 'external_objects': {}}
        evidence = root / 'normal'
        evidence.mkdir()
        data = {'frozen-plan.json': plan, 'modules.json': records, 'status.json': {'status': 'passed'},
                'environment-one.json': env, 'frozen-environment.json': {}}
        for filename, value in data.items():
            (evidence / filename).write_text(json.dumps(value))
        return root, evidence

    def test_native_dependency_map_and_source_graph_are_exact(self):
        root, evidence = self.native_fixture()
        config = prepare.native_config(root, evidence, 'C:/helper/ResearchAudit/EnvironmentAudit.lean')
        prepare.config_check(config)
        self.assertEqual(config['expected_modules'], ['Math115', 'Math115.Leaf'])
        rows = json.loads((evidence / 'modules.json').read_text())
        rows[0]['dependency_olean_sha256'] = {}
        (evidence / 'modules.json').write_text(json.dumps(rows))
        with self.assertRaisesRegex(ValueError, 'dependency object closure differs'):
            prepare.native_config(root, evidence, 'C:/helper/ResearchAudit/EnvironmentAudit.lean')

    def test_native_disagreeing_environment_cannot_be_selected_by_filename_order(self):
        root, evidence = self.native_fixture()
        env = json.loads((evidence / 'environment-one.json').read_text())
        env['lean_sha256'] = 'e' * 64
        (evidence / 'environment-two.json').write_text(json.dumps(env))
        with self.assertRaisesRegex(ValueError, 'environment identities differ'):
            prepare.native_config(root, evidence, 'C:/helper/ResearchAudit/EnvironmentAudit.lean')

    def test_native_omitted_internal_dependency_cannot_be_treated_as_trusted_cache(self):
        root, evidence = self.native_fixture()
        plan = json.loads((evidence / 'frozen-plan.json').read_text())
        plan['modules'] = plan['modules'][:1]
        (evidence / 'frozen-plan.json').write_text(json.dumps(plan))
        rows = json.loads((evidence / 'modules.json').read_text())[:1]
        (evidence / 'modules.json').write_text(json.dumps(rows))
        with self.assertRaisesRegex(ValueError, 'omits an internal'):
            prepare.native_config(root, evidence, 'C:/helper/ResearchAudit/EnvironmentAudit.lean')


if __name__ == '__main__':
    unittest.main()
