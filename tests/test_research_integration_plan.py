"""Public integration import assembly; these tests never run Lean or Lake."""

import importlib.util
import contextlib
import gzip
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
BOOTSTRAPPED_SOURCES = all(path.exists() for path in (
    ROOT / ".upstream/openai-math/lean/OAI",
    ROOT / "formal/.lake/packages/mathlib/Mathlib.lean",
    ROOT / ".tools/elan/toolchains/leanprover--lean4---v4.34.1/lib/lean/Init.olean",
))
SPEC = importlib.util.spec_from_file_location(
    "research_scope_verifier", ROOT / "research/repair-accept/verify.py")
verifier = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(verifier)


class IntegrationPlanTests(unittest.TestCase):
    @unittest.skipUnless(BOOTSTRAPPED_SOURCES,
                         "Public source-plan check needs the normal pinned Lean/upstream/package bootstrap; no downloads in Python tests")
    def test_public_hybrid_closure_resolves_in_dependency_order_without_execution(self):
        with mock.patch.object(verifier.subprocess, "run", side_effect=AssertionError("build started")), \
             mock.patch.object(verifier.subprocess, "check_output", side_effect=AssertionError("process started")):
            plan = verifier.integration_plan(ROOT)
        self.assertEqual(plan["status"], "planned_only")
        self.assertIn("ResearchPhysicalTraceJoin.GeneralHybridSampler", plan["audit_modules"])
        self.assertIn("ResearchPhysicalTraceJoin.GeneralExecutableSampler", plan["audit_modules"])
        self.assertIn("Math115.PhysicalTraceJoin.executableSampler_contract", plan["headlines"])
        available = set(plan["baseline_modules"]) | set(plan["trusted_external_imports"])
        self.assertFalse(set(plan["baseline_modules"]) &
                         {entry["module"] for entry in plan["compilation"]})
        for entry in plan["compilation"]:
            with self.subTest(module=entry["module"]):
                source = ROOT / entry["source"]
                self.assertTrue(source.is_file())
                self.assertNotIn(".local", source.relative_to(ROOT).parts)
                self.assertLessEqual(set(entry["imports"]), available)
                self.assertNotIn(entry["module"], available)
                if entry["source"].startswith("research/"):
                    suffix = Path(*entry["module"].split(".")).with_suffix(".lean")
                    candidates = list((ROOT / "research").glob("*/formal/" + str(suffix)))
                    self.assertEqual(candidates, [source])
                available.add(entry["module"])
        self.assertLessEqual(set(plan["audit_modules"]), available)

    def test_existing_scope_keeps_its_original_upstream_preflight(self):
        with mock.patch.object(verifier, "integration_plan", side_effect=AssertionError("new scope selected")), \
             mock.patch.object(verifier.subprocess, "run", side_effect=AssertionError("compiler started")), \
             mock.patch.object(verifier.subprocess, "check_output", return_value="wrong-pin\n"), \
             mock.patch.object(sys, "argv", ["verify.py", "--scope", "repair-accept", "--output", "unused"]):
            with self.assertRaisesRegex(SystemExit, "Pinned upstream checkout differs"):
                verifier.main()

    def test_timeouts_retain_partial_diagnostics_and_failed_stage_without_a_pass_receipt(self):
        for stage in ("compile", "audit"):
            with self.subTest(stage=stage), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "formal/.lake/build/lib/lean").mkdir(parents=True)
                packet = root / "research/repair-accept/formal"
                packet.mkdir(parents=True)
                (packet / "Synthetic.lean").write_text("def example := 1\n")
                auditor = root / "formal/ResearchAudit/EnvironmentAudit.lean"
                auditor.parent.mkdir(parents=True)
                auditor.write_text("-- synthetic auditor\n")
                lean = root / "lean"
                lean.touch()
                output = root / "attempt"

                def run(command, **kwargs):
                    self.assertEqual(kwargs["timeout"], 600)  # Existing scopes retain their allowance.
                    if stage == "compile" or "-o" not in command:
                        raise subprocess.TimeoutExpired(command, 600, output=b"partial stdout", stderr=b"partial stderr")
                    Path(command[command.index("-o") + 1]).write_bytes(b"synthetic object")
                    return subprocess.CompletedProcess(command, 0, "", "")

                with mock.patch.object(verifier, "ROOT", root), \
                     mock.patch.dict(verifier.SCOPES, {"repair-accept": (["Synthetic"], [], [])}), \
                     mock.patch.object(verifier.subprocess, "check_output", return_value=verifier.PIN), \
                     mock.patch.object(verifier.subprocess, "run", side_effect=run), \
                     mock.patch.object(sys, "argv", ["verify.py", "--lean", str(lean), "--output", str(output)]), \
                     contextlib.redirect_stdout(io.StringIO()):
                    with self.assertRaisesRegex(SystemExit, "timed out"):
                        verifier.main()
                self.assertFalse((output / "verification.json").exists())
                if stage == "compile":
                    result = json.loads((output / "compilation.json").read_text())[-1]
                    stdout = (output / "Synthetic.stdout.txt").read_text()
                    stderr = (output / "Synthetic.stderr.txt").read_text()
                else:
                    result = json.loads((output / "audit-result.json").read_text())
                    stdout = gzip.decompress((output / "audit.stdout.json.gz").read_bytes()).decode()
                    stderr = (output / "audit.stderr.txt").read_text()
                self.assertTrue(result["timeout"])
                self.assertIsNone(result["returncode"])
                self.assertEqual(stdout, "partial stdout")
                self.assertEqual(stderr, "partial stderr")


if __name__ == "__main__":
    unittest.main()
