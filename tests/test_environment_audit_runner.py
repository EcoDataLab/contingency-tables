import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('environment_runner', ROOT / 'scripts/run_environment_audit.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def record(name, dependencies=None, kind='theorem'):
    return {'name': name, 'module': 'FixtureModule', 'kind': kind, 'statement': 'True',
            'dependencies': dependencies or [], 'axioms': [], 'standard_axioms': [], 'nonstandard_axioms': []}


def config():
    return {'schema_version': 1, 'scope': 'tiny fixture only', 'imports': ['FixtureModule'],
            'prefixes': ['FixtureModule'], 'source_bound_prefixes': ['FixtureModule'], 'expected_modules': ['FixtureModule'],
            'headlines': ['Fixture.headline'], 'expected_declarations': ['Fixture.headline', 'Fixture.unlisted'],
            'compiler': '/fixture/toolchain/bin/lean', 'compiler_sha256': 'a' * 64, 'compiler_version': 'Lean fixture version', 'helper_source': '/fixture/helper.lean',
            'helper_sha256': 'b' * 64, 'working_directory': '/fixture',
            'lean_path': ['/fixture/lib'], 'builtin_library': '/fixture/toolchain/lib/lean',
            'inventory_roots': ['/fixture/lib', '/fixture/toolchain/lib', '/fixture/toolchain/bin'],
            'pins': {'fixture': {'path': '/fixture/source', 'sha256': 'c' * 64}},
            'threads': 2, 'timeout_seconds': 30}


def report():
    records = [record('Fixture.headline', ['Fixture.hidden']), record('Fixture.hidden'), record('Fixture.unlisted')]
    return {'schema_version': 1, 'method': 'compiled Lean environment',
            'prefixes': ['FixtureModule'], 'modules': ['FixtureModule'],
            'imported_modules': ['FixtureModule', runner.HELPER_MODULE],
            'declaration_count': 3, 'theorem_count': 3,
            'theorem_names': [r['name'] for r in records], 'declarations': records,
            'headlines': [{'name': 'Fixture.headline', 'closure': ['Fixture.headline', 'Fixture.hidden'],
                           'declarations': records[:2]}]}


class EnvironmentRunnerTests(unittest.TestCase):
    def test_valid_report_includes_unlisted_and_private_dependencies(self):
        self.assertEqual(runner.validate_report(report(), config())['theorems'], 3)

    def test_json_framing_and_duplicate_keys_fail_closed(self):
        text = json.dumps(report())
        self.assertEqual(runner.strict_json(text)['theorem_count'], 3)
        for bad in [text + '\nwarning', 'warning\n' + text, text + text,
                    '{"schema_version":1,"schema_version":1}', '{"number":NaN}']:
            with self.subTest(bad=bad[:40]), self.assertRaises(ValueError):
                runner.strict_json(bad)

    def test_unicode_lean_statement_survives_utf8_json_roundtrip(self):
        value=report();value['declarations'][0]['statement']='∀ (x : ℝ), x ≤ x ∧ ∃ y, y = x'
        text=json.dumps(value,ensure_ascii=False)
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'report.stdout';p.write_bytes(text.encode('utf-8'))
            decoded=runner.strict_json(p.read_text(encoding='utf-8'))
            self.assertEqual(decoded['declarations'][0]['statement'],value['declarations'][0]['statement'])
            runner.validate_report(decoded,config())

    def test_missing_modules_headlines_and_known_declarations_fail(self):
        mutations = []
        r = report(); r['imported_modules'].remove('FixtureModule'); mutations.append(r)
        r = report(); r['headlines'] = []; mutations.append(r)
        r = report(); r['declarations'].pop(); r['theorem_names'].pop(); r['theorem_count'] -= 1; r['declaration_count'] -= 1; mutations.append(r)
        for bad in mutations:
            with self.assertRaises(ValueError):
                runner.validate_report(bad, config())

    def test_unexpected_source_bound_project_import_cannot_hide_as_cache(self):
        bad=report();bad['imported_modules'].append('FixtureModule.Unpinned')
        with self.assertRaisesRegex(ValueError,'source-bound imported project graph'):
            runner.validate_report(bad,config())
        good=report();good['imported_modules'].append('Mathlib.TrustedCache')
        runner.validate_report(good,config())

    def test_custom_axioms_and_inconsistent_axiom_classification_fail(self):
        for ax in ['sorryAx', 'Custom.unsupported', 'Classical.choice']:
            bad = report(); bad['declarations'][0]['axioms'] = [ax]
            with self.subTest(ax=ax), self.assertRaises(ValueError):
                runner.validate_report(bad, config())

    def test_exact_headline_dependency_closure_cannot_omit_or_add_dependencies(self):
        bad = report(); bad['headlines'][0]['declarations'][0]['dependencies'] = ['Missing.dependency']
        with self.assertRaisesRegex(ValueError, 'misses a direct'):
            runner.validate_report(bad, config())
        bad = report(); bad['headlines'][0]['closure'].append('Fixture.unrelated')
        bad['headlines'][0]['declarations'].append(record('Fixture.unrelated'))
        with self.assertRaisesRegex(ValueError, 'unrelated'):
            runner.validate_report(bad, config())

    def test_scope_and_kind_count_mismatches_fail(self):
        bad = report(); bad['prefixes'] = ['Other']
        with self.assertRaisesRegex(ValueError, 'scope differs'):
            runner.validate_report(bad, config())
        bad = report(); bad['declarations'][0]['kind'] = 'definition'
        with self.assertRaisesRegex(ValueError, 'theorem inventory'):
            runner.validate_report(bad, config())

    def test_lean_prefix_shadowing_matches_pinned_search_path_semantics(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); first = root / 'first'; second = root / 'second'
            (first / 'Math115').mkdir(parents=True); (second / 'Math115').mkdir(parents=True)
            (second / 'Math115/Target.olean').write_bytes(b'valid')
            with self.assertRaisesRegex(ValueError, 'prefix shadow'):
                runner.resolve_module('Math115.Target', [first, second])
            (first / 'ResearchAudit').mkdir()
            self.assertEqual(runner.resolve_module('Math115.Target', [first / 'ResearchAudit', second]),
                             second / 'Math115/Target.olean')

    def test_before_after_inventory_detects_object_mutation_and_new_object(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in ['lean', 'helper.lean', 'input', 'lib/Fixture.olean']:
                path = root / name; path.parent.mkdir(exist_ok=True); path.write_bytes(name.encode())
            c = config(); c.update(compiler=str(root/'lean'), compiler_sha256=runner.sha(root/'lean'),
                helper_source=str(root/'helper.lean'), helper_sha256=runner.sha(root/'helper.lean'),
                pins={'input': {'path': str(root/'input'), 'sha256': runner.sha(root/'input')}},
                inventory_roots=[str(root/'lib')])
            before = runner.snapshot(c)
            (root/'lib/Fixture.olean').write_bytes(b'changed')
            self.assertNotEqual(before, runner.snapshot(c))
            (root/'input').write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'pinned input changed'):
                runner.snapshot(c)

    def inventory_fixture(self, root):
        for name in ['lean', 'helper.lean', 'input', 'lib/FixtureModule.olean']:
            path=root/name;path.parent.mkdir(exist_ok=True);path.write_bytes(name.encode())
        c=config();c.update(compiler=str(root/'lean'),compiler_sha256=runner.sha(root/'lean'),
            helper_source=str(root/'helper.lean'),helper_sha256=runner.sha(root/'helper.lean'),
            pins={'input':{'path':str(root/'input'),'sha256':runner.sha(root/'input')}},
            lean_path=[str(root/'unused/lib/lean'),str(root/'lib')],
            inventory_roots=[str(root/'unused/lib'),str(root/'lib')])
        return c

    def test_unused_missing_inventory_root_is_bound_without_filtering_search_path(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);c=self.inventory_fixture(root);original_search=list(c['lean_path'])
            snapshot=runner.snapshot(c)
            self.assertEqual(snapshot['inventory_root_states'][str(root/'unused/lib')],'absent')
            self.assertEqual(snapshot['inventory_root_states'][str(root/'lib')],'directory')
            self.assertEqual(c['lean_path'],original_search)
            self.assertEqual(runner.resolve_module('FixtureModule',list(map(Path,c['lean_path']))),root/'lib/FixtureModule.olean')
            with self.assertRaisesRegex(ValueError,'unknown imported module prefix'):
                runner.resolve_module('Missing.Required',[root/'unused/lib/lean',root/'lib'])
            (root/'input').unlink()
            with self.assertRaises(FileNotFoundError):
                runner.snapshot(c)

    def test_empty_inventory_root_appearance_and_disappearance_change_snapshots(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);c=self.inventory_fixture(root)
            absent=runner.snapshot(c)
            (root/'unused/lib').mkdir(parents=True)
            present=runner.snapshot(c)
            self.assertEqual(absent['artifact_inventory'],present['artifact_inventory'])
            self.assertNotEqual(absent,present)
            self.assertEqual(present['inventory_root_states'][str(root/'unused/lib')],'directory')
            (root/'unused/lib').rmdir()
            missing_again=runner.snapshot(c)
            self.assertNotEqual(present,missing_again)
            self.assertEqual(missing_again['inventory_root_states'][str(root/'unused/lib')],'absent')

    def test_existing_nondirectory_inventory_entry_remains_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);c=self.inventory_fixture(root)
            (root/'unused').mkdir();(root/'unused/lib').write_bytes(b'file instead of directory')
            with self.assertRaisesRegex(ValueError,'inventory root is not a directory'):
                runner.snapshot(c)

    def test_ir_signature_mutation_and_new_companion_are_bound(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for name in ['lean','helper.lean','input','lib/Fixture.olean','lib/Fixture.ir.sig']:
                p=root/name; p.parent.mkdir(exist_ok=True); p.write_bytes(name.encode())
            c=config(); c.update(compiler=str(root/'lean'),compiler_sha256=runner.sha(root/'lean'),
                helper_source=str(root/'helper.lean'),helper_sha256=runner.sha(root/'helper.lean'),
                pins={'source':{'path':str(root/'input'),'sha256':runner.sha(root/'input')}},inventory_roots=[str(root/'lib')])
            before=runner.snapshot(c)
            (root/'lib/Fixture.ir.sig').write_bytes(b'changed signature')
            self.assertNotEqual(before,runner.snapshot(c))
            before=runner.snapshot(c)
            (root/'lib/Fixture.olean.private').write_bytes(b'new private companion')
            self.assertNotEqual(before,runner.snapshot(c))

    def test_import_and_native_runtime_directories_must_all_be_inventoried(self):
        c=config(); c['inventory_roots']=['/unrelated']
        with self.assertRaisesRegex(ValueError,'do not cover'):
            runner.config_check(c)
        runner.config_check(config())

    def test_path_inventory_coverage_cannot_be_spoofed_with_parent_traversal(self):
        c=config(); c['lean_path']=['/fixture/lib/../outside']
        with self.assertRaisesRegex(ValueError,'parent traversal'):
            runner.config_check(c)

    def test_new_helper_companion_is_detected_in_complete_helper_inventory(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for name in ['lean','helper.lean','input','helper-lib/ResearchAudit/EnvironmentAudit.olean']:
                p=root/name; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(name.encode())
            c=config(); c.update(compiler=str(root/'lean'),compiler_sha256=runner.sha(root/'lean'),
                helper_source=str(root/'helper.lean'),helper_sha256=runner.sha(root/'helper.lean'),
                pins={'source':{'path':str(root/'input'),'sha256':runner.sha(root/'input')}},inventory_roots=[str(root/'helper-lib')])
            before=runner.snapshot(c)
            (root/'helper-lib/ResearchAudit/EnvironmentAudit.ir.sig').write_bytes(b'new signature')
            self.assertNotEqual(before,runner.snapshot(c))

    def test_failure_receipt_is_preserved_and_attempt_cannot_be_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); path=root/'config.json'; c=config(); path.write_text(json.dumps(c))
            receipt = runner.run(path, root/'attempt')
            self.assertEqual(receipt['status'], 'failed')
            self.assertTrue((root/'attempt/receipt.json').is_file())
            with self.assertRaises(FileExistsError):
                runner.run(path, root/'attempt')

    def test_nonzero_exit_or_stderr_cannot_be_rescued_by_valid_json(self):
        for exit_code, stderr in [(3,b''),(0,b'compiler warning')]:
            with self.subTest(exit_code=exit_code,stderr=stderr), tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);toolchain=root/'toolchain';(toolchain/'bin').mkdir(parents=True);(toolchain/'lib/lean').mkdir(parents=True)
                fixturelib=root/'fixture-lib';fixturelib.mkdir()
                for p in [toolchain/'bin/lean',root/'helper.lean',root/'input',fixturelib/'FixtureModule.olean']:
                    p.write_bytes(b'synthetic test input')
                c=config();c.update(compiler=str(toolchain/'bin/lean'),compiler_sha256=runner.sha(toolchain/'bin/lean'),
                    helper_source=str(root/'helper.lean'),helper_sha256=runner.sha(root/'helper.lean'),working_directory=str(root),
                    lean_path=[str(fixturelib)],builtin_library=str(toolchain/'lib/lean'),
                    inventory_roots=[str(fixturelib),str(toolchain/'lib'),str(toolchain/'bin')],
                    pins={'source':{'path':str(root/'input'),'sha256':runner.sha(root/'input')}})
                path=root/'config.json';path.write_text(json.dumps(c))
                def controlled_execute(argv,cwd,env,output,label,timeout):
                    out,err=b'',b'';code=0
                    if label=='compiler-version':out=c['compiler_version'].encode()
                    elif label=='compiler-prefix':out=str(toolchain).encode()
                    elif label=='helper-compile':Path(argv[argv.index('-o')+1]).write_bytes(b'synthetic helper object')
                    elif label=='environment-audit':out=json.dumps(report()).encode();err=stderr;code=exit_code
                    (output/(label+'.stdout')).write_bytes(out);(output/(label+'.stderr')).write_bytes(err)
                    return {'exit_code':code,'timed_out':False,'stdout_sha256':runner.sha(output/(label+'.stdout'))}
                with patch.object(runner,'execute',side_effect=controlled_execute):
                    result=runner.run(path,root/'attempt')
                self.assertEqual(result['status'],'failed')
                self.assertTrue((root/'attempt/environment-audit.stdout').is_file())
                self.assertEqual(runner.strict_json((root/'attempt/environment-audit.stdout').read_text())['theorem_count'],3)

    def test_driver_uses_all_frozen_modules_and_distinct_helper_prefix(self):
        driver = runner.driver_source(config())
        self.assertIn('import ResearchAudit.EnvironmentAudit', driver)
        self.assertIn('modules [FixtureModule]', driver)
        self.assertNotIn('#print axioms', driver)
        bad=config(); bad['imports']=['FixtureModule\n#print axioms sorryAx']
        with self.assertRaises(ValueError):
            runner.driver_source(bad)


if __name__ == '__main__':
    unittest.main()
