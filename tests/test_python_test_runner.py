"""The complete-suite entry point must not quietly lose the SciPy lane."""
import contextlib
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

PATH = Path(__file__).resolve().parents[1] / "scripts/run_python_tests.py"
SPEC = importlib.util.spec_from_file_location("run_python_tests", PATH)
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


class PythonTestRunnerTests(unittest.TestCase):
    def run_main(self, args, *, missing=False, skipped=(), success=True):
        result = Mock(skipped=list(skipped))
        result.wasSuccessful.return_value = success
        backend = patch.object(runner, "scientific_backend",
                               side_effect=ModuleNotFoundError("scipy") if missing else None,
                               return_value={"numpy": "test", "scipy": "test"})
        output = io.StringIO()
        with backend as check, patch.object(runner, "configure_checkout"), \
             patch.object(runner.unittest, "TestLoader") as loader, \
             patch.object(runner.unittest, "TextTestRunner") as tests, \
             contextlib.redirect_stderr(output):
            tests.return_value.run.return_value = result
            status = runner.main(args)
        return status, output.getvalue(), check, loader, tests

    def test_full_mode_fails_before_discovery_when_scipy_is_missing(self):
        status, output, check, loader, tests = self.run_main([], missing=True)
        self.assertEqual(status, 2)
        self.assertIn("test extra", output)
        self.assertIn("--core", output)
        self.assertIn(sys.executable, output)
        check.assert_called_once()
        loader.assert_not_called()
        tests.assert_not_called()

    def test_full_mode_rejects_scipy_skip_even_if_unittest_says_success(self):
        skipped = [(Mock(id=lambda: "test_scipy_workers.ScipyWorkerLibraryTests.example"),
                    "optional SciPy random_table unavailable")]
        status, output, *_ = self.run_main([], skipped=skipped)
        self.assertEqual(status, 1)
        self.assertIn("required scientific lane was skipped", output)

    def test_full_mode_keeps_other_explicit_skips_and_real_failures_visible(self):
        skipped = [(Mock(id=lambda: "test_research_integration_plan.example"),
                    "pinned source bootstrap unavailable")]
        status, output, *_ = self.run_main([], skipped=skipped)
        self.assertEqual(status, 0)
        self.assertIn("Required scientific backend", output)
        self.assertEqual(self.run_main([], success=False)[0], 1)

    def test_core_mode_is_an_explicit_opt_out_of_dependency_preflight(self):
        status, output, check, *_ = self.run_main(["--core"], missing=True)
        self.assertEqual(status, 0)
        self.assertIn("Core mode", output)
        check.assert_not_called()

    def test_scientific_preflight_rejects_a_present_but_incomplete_api(self):
        modules = {"numpy": Mock(__version__="test"), "scipy": Mock(__version__="test"),
                   "scipy.stats": Mock(random_table=object())}
        with patch.object(runner.importlib, "import_module", side_effect=modules.__getitem__):
            with self.assertRaisesRegex(ImportError, "pmf and rvs"):
                runner.scientific_backend()

    def test_checkout_and_src_imports_work_in_a_subprocess_outside_the_checkout(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "elsewhere").mkdir()
            (root / "checkout_only_probe.py").write_text("value = 'checkout'\n")
            (root / "src/source_only_probe.py").write_text("value = 'src'\n")
            with patch.object(runner, "ROOT", root), patch.object(sys, "path", list(sys.path)), \
                 patch.dict(os.environ):
                runner.configure_checkout()
                result = subprocess.run(
                    [sys.executable, "-S", "-c",
                     "import checkout_only_probe, source_only_probe; "
                     "print(checkout_only_probe.value, source_only_probe.value)"],
                    cwd=root / "elsewhere", capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), "checkout src")


if __name__ == "__main__":
    unittest.main()
