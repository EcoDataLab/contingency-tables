"""Serial orchestration failure boundaries; no test invokes Lean or Lake."""

import importlib.util
import builtins
import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


HELPER = Path(__file__).resolve().parents[1] / "scripts/build_lean_serial.py"
SPEC = importlib.util.spec_from_file_location("build_lean_serial", HELPER)
serial = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = serial
SPEC.loader.exec_module(serial)


class HeaderTests(unittest.TestCase):
    def test_native_windows_import_and_explicit_cli_boundary(self):
        original_import = builtins.__import__
        def no_fcntl(name, *args, **kwargs):
            if name == "fcntl":
                raise ImportError("simulated native Windows")
            return original_import(name, *args, **kwargs)
        spec = importlib.util.spec_from_file_location("build_lean_serial_without_fcntl", HELPER)
        module = importlib.util.module_from_spec(spec)
        with mock.patch.dict(sys.modules, {spec.name: module}):
            with mock.patch("builtins.__import__", side_effect=no_fcntl):
                spec.loader.exec_module(module)
            self.assertEqual(module.lean_imports("import A"), ("Init", "A"))
            errors = io.StringIO()
            with mock.patch.object(sys, "argv", ["build_lean_serial.py", "full", "--plan"]):
                with contextlib.redirect_stderr(errors):
                    self.assertEqual(module.main(), 2)
            self.assertIn("requires Linux or macOS", errors.getvalue())

    def test_nested_comments_and_proof_body_are_not_imports(self):
        source = '''/- outer /- import Not.Real -/ outer -/
import Math115.A -- import Ignored
import/- separator -/ Mathlib.Tactic
def example := "import Also.Ignored"
/- an unclosed proof-body comment is Lean's concern, not the header planner
'''
        self.assertEqual(serial.lean_imports(source), ("Init", "Math115.A", "Mathlib.Tactic"))

    def test_module_modifiers_and_same_line_imports(self):
        source = "module\nprelude\npublic meta import A import all B meta import C\npublic section\n"
        self.assertEqual(serial.lean_imports(source), ("A", "B", "C"))

    def test_implicit_init_and_duplicates(self):
        self.assertEqual(serial.lean_imports("import Init\nimport A\nimport A"), ("Init", "A"))
        self.assertEqual(serial.lean_imports("prelude\ndef x := 1"), ())

    def test_unsupported_imports_fail_instead_of_disappearing(self):
        for source in ("import «Quoted.Name»", "import Unicode.α", "import Foo.", "import", "import ../Foo"):
            with self.subTest(source=source), self.assertRaises(serial.BuildError):
                serial.lean_imports(source)

    def test_invalid_header_modifiers_and_unclosed_header_comment(self):
        for source in ("public import Foo", "meta import Foo", "import all Foo",
                       "module public import all Foo", "/- unclosed"):
            with self.subTest(source=source), self.assertRaises(serial.BuildError):
                serial.lean_imports(source)


class GraphTests(unittest.TestCase):
    def test_diamond_order_roots_and_external_boundary(self):
        deps = {"A": ("B", "C"), "B": ("D", "Mathlib"), "C": ("D",), "D": ()}
        order = serial.dependency_order(("A", "C"), lambda n:
            serial.Module(n, Path(n + ".lean"), deps[n]) if n in deps else None)
        self.assertEqual([m.name for m in order], ["D", "B", "C", "A"])

    def test_cycle_rejected(self):
        deps = {"A": ("B",), "B": ("A",)}
        with self.assertRaisesRegex(serial.BuildError, "Import cycle"):
            serial.dependency_order(("A",), lambda n: serial.Module(n, Path(n), deps[n]))

    def test_missing_source_propagates(self):
        def resolve(_):
            raise serial.BuildError("missing input")
        with self.assertRaisesRegex(serial.BuildError, "missing input"):
            serial.dependency_order(("A",), resolve)

    def test_deep_graph_is_not_limited_by_python_recursion(self):
        count = 1500
        def resolve(name):
            index = int(name[1:])
            deps = (f"M{index - 1}",) if index else ()
            return serial.Module(name, Path(name), deps)
        order = serial.dependency_order((f"M{count - 1}",), resolve)
        self.assertEqual(len(order), count)
        self.assertEqual(order[0].name, "M0")


class SerialExecutionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "formal").mkdir()
        self.source = self.root / "formal/A.lean"
        self.source.write_text("import Init\ndef a := 1\n")
        self.snapshot = serial.Snapshot(self.root)
        self.snapshot.add(self.source)
        self.modules = [serial.Module("A", self.source, ("Init",))]
        self.report = self.root / "report.json"
        self.plan = {"status": "planned_only", "commands": [], "axiom_audit": "not_run_by_this_helper"}
        self.calls = []
        self.output = io.StringIO()

    def record(self, argv, **kwargs):
        self.calls.append((argv, kwargs))
        return subprocess.CompletedProcess(argv, 0)

    def run_with(self, runner):
        with contextlib.redirect_stdout(self.output):
            serial.run_serial(self.root, self.plan, self.snapshot, self.modules, self.report, runner=runner)

    def test_dependencies_checked_then_single_explicit_module_target(self):
        self.run_with(self.record)
        self.assertEqual([call[0][1:] for call in self.calls], [
            ["--no-cache", "--no-build", "build", "+A:deps"],
            ["--no-cache", "build", "+A:olean"],
        ])
        self.assertTrue(all(c[1]["env"]["ELAN_TOOLCHAIN"] == serial.TOOLCHAIN for c in self.calls))
        self.assertTrue(all("LEAN_PATH" not in c[1]["env"] for c in self.calls))
        saved = json.loads(self.report.read_text())
        self.assertEqual(saved["status"], "build_completed")
        self.assertEqual(saved["axiom_audit"], "not_run_by_this_helper")
        self.assertIn("Serial module 1/1: A", self.output.getvalue())
        self.assertIn("Serial module builds completed.", self.output.getvalue())

    def test_missing_dependency_blocks_compile(self):
        def fail(argv, **kwargs):
            self.calls.append(argv)
            return subprocess.CompletedProcess(argv, 3)
        with self.assertRaisesRegex(serial.BuildError, "Dependency preflight failed"):
            self.run_with(fail)
        self.assertEqual(len(self.calls), 1)
        self.assertIn("--no-build", self.calls[0])
        self.assertEqual(json.loads(self.report.read_text())["status"], "failed")

    def test_failed_module_stops_before_next_module(self):
        self.modules.append(serial.Module("B", self.source, ("A",)))
        def fail_second(argv, **kwargs):
            self.calls.append(argv)
            return subprocess.CompletedProcess(argv, 1 if len(self.calls) == 2 else 0)
        with self.assertRaisesRegex(serial.BuildError, "Lake compilation failed for A"):
            self.run_with(fail_second)
        self.assertEqual(len(self.calls), 2)
        saved = json.loads(self.report.read_text())
        self.assertEqual(saved["status"], "failed")
        self.assertEqual(saved["commands"][-1]["returncode"], 1)

    def test_source_change_during_dependency_check_blocks_compile(self):
        def change_source(argv, **kwargs):
            self.calls.append(argv)
            self.source.write_text("import Something.Else\n")
            return subprocess.CompletedProcess(argv, 0)
        with self.assertRaisesRegex(serial.BuildError, "Source/configuration changed"):
            self.run_with(change_source)
        self.assertEqual(len(self.calls), 1)
        self.assertEqual(json.loads(self.report.read_text())["status"], "failed")

    def test_source_removed_before_build_blocks_all_processes(self):
        self.source.unlink()
        with self.assertRaisesRegex(serial.BuildError, "Input disappeared"):
            self.run_with(self.record)
        self.assertEqual(self.calls, [])

    def test_interruption_does_not_record_a_success(self):
        def interrupt(*args, **kwargs):
            raise KeyboardInterrupt
        with self.assertRaises(KeyboardInterrupt):
            self.run_with(interrupt)
        saved = json.loads(self.report.read_text())
        self.assertEqual(saved["status"], "interrupted")
        self.assertNotIn("completed_at", saved)


if __name__ == "__main__":
    unittest.main()
