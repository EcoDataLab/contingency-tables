"""Counterexamples for whole-log allocation and exact marker-scan equivalence."""
import ast
from contextlib import contextmanager
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import types
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parents[2]
spec = importlib.util.spec_from_file_location("bounded_output_assembly", HERE / "prepare_candidate.py")
assembly = importlib.util.module_from_spec(spec)
spec.loader.exec_module(assembly)
files = assembly.inputs()

def load(raw, name):
    module = types.ModuleType(name)
    module.__file__ = str(HERE / "unused-derived-observer.py")
    exec(compile(raw, module.__file__, "exec"), module.__dict__)
    return module

old_raw = (REPO / "research/strict-sampler-checkpoints/proc-observer-v2/source/strict_serial_check.py").read_bytes()
old = load(old_raw, "old_output_observer")
fixed = load(files["candidate/tested-runtime/strict_serial_check.py"], "fixed_output_observer")
MARKERS = fixed.COMPARATOR_ACCEPTANCE_MARKERS

@contextmanager
def fixture_digest_compat(module):
    """Support old pinned modules on Python 3.10, without changing global hashlib."""
    original = module.hashlib
    if hasattr(original, "file_digest"):
        yield
        return
    class Proxy:
        def __getattr__(self, name):
            return getattr(original, name)
        def file_digest(self, stream, algorithm):
            value = getattr(original, algorithm)()
            for block in iter(lambda: stream.read(65536), b""):
                value.update(block)
            return value
    module.hashlib = Proxy()
    try:
        yield
    finally:
        module.hashlib = original

class OutputTests(unittest.TestCase):
    def measured(self, module, label, raw):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); (root / "formal").mkdir(); out = root / "evidence"; out.mkdir()
            class Process:
                pid = 123
                def poll(self): return 0
                def wait(self): return 0
            def spawn(argv, **kwargs):
                kwargs["stdout"].write(raw); kwargs["stdout"].flush()
                return Process()
            plan = {"commands": [{}]}
            runner = module.MeasuredRunner(root, out, plan, 60)
            with fixture_digest_compat(module), patch.object(module.subprocess, "Popen", side_effect=spawn), patch.object(Path, "read_text", side_effect=AssertionError("whole-file text read forbidden")):
                result = runner(["fixture-no-process"], label)
            self.assertEqual((out / (label + ".stdout.log")).read_bytes(), raw)
            self.assertEqual(plan["commands"][0]["stdout_sha256"], assembly.digest(raw))
            return result

    def test_old_runner_attempts_whole_log_text_allocation(self):
        with self.assertRaisesRegex(AssertionError, "whole-file text read"):
            self.measured(old, "unchanged_comparator", b"x" * 1024 * 1024)

    def test_new_runner_keeps_raw_log_and_returns_only_marker_summary(self):
        raw = b"x" * (1024 * 1024) + "\n".join(MARKERS).encode() + b"end"
        result = self.measured(fixed, "unchanged_comparator", raw)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "\n".join(MARKERS))
        self.assertLess(len(result.stdout), 200)

    def test_other_command_labels_keep_existing_empty_stdout_contract(self):
        for module in (old, fixed):
            self.assertEqual(self.measured(module, "module_build", b"ordinary full log").stdout, "")

    def test_missing_file_digest_is_scoped_and_restored_even_after_error(self):
        class MissingFileDigest:
            def __getattr__(self, name):
                if name == "file_digest":
                    raise AttributeError(name)
                return getattr(hashlib, name)
        global_present = hasattr(hashlib, "file_digest")
        for module in (old, fixed):
            original = module.hashlib
            missing = MissingFileDigest()
            with patch.object(module, "hashlib", missing):
                self.assertEqual(self.measured(module, "module_build", b"bounded fixture").stdout, "")
                self.assertIs(module.hashlib, missing)
                self.assertFalse(hasattr(module.hashlib, "file_digest"))
                with self.assertRaisesRegex(RuntimeError, "fixture teardown"):
                    with fixture_digest_compat(module):
                        self.assertTrue(hasattr(module.hashlib, "file_digest"))
                        raise RuntimeError("fixture teardown")
                self.assertIs(module.hashlib, missing)
                self.assertFalse(hasattr(module.hashlib, "file_digest"))
            self.assertIs(module.hashlib, original)
        self.assertEqual(hasattr(hashlib, "file_digest"), global_present)

    def test_exact_substring_semantics_across_every_short_chunk_boundary(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "log"
            for chunk in (1, 2, 7, 31, 64):
                for offset in range(chunk):
                    raw = b"x" * offset + b"\xff\r\n".join(s.encode() for s in reversed(MARKERS)) + b"tail"
                    path.write_bytes(raw)
                    result = fixed.comparator_marker_summary(path, chunk)
                    original_text = raw.decode("utf-8", errors="replace")
                    self.assertEqual(tuple(s in result for s in MARKERS), tuple(s in original_text for s in MARKERS))

    def test_missing_partial_duplicate_and_invalid_utf8_do_not_invent_acceptance(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "log"
            for raw in (b"", MARKERS[0][:-1].encode(), MARKERS[0].encode() * 3,
                        MARKERS[1].encode().replace(b"kernel", b"ker\xffnel")):
                path.write_bytes(raw)
                result = fixed.comparator_marker_summary(path, 3)
                text = raw.decode("utf-8", errors="replace")
                self.assertEqual(tuple(s in result for s in MARKERS), tuple(s in text for s in MARKERS))

    def test_both_real_consumers_require_exactly_the_scanned_phrases(self):
        for raw in (old_raw, files["candidate/strict_sampler.py"]):
            tuples = [tuple(v.value for v in node.elts) for node in ast.walk(ast.parse(raw))
                      if isinstance(node, ast.Tuple) and len(node.elts) == 3
                      and all(isinstance(v, ast.Constant) and isinstance(v.value, str) for v in node.elts)]
            self.assertIn(MARKERS, tuples)

    def test_fresh_assembly_binds_new_observer_runner_and_preparation(self):
        with tempfile.TemporaryDirectory() as tmp:
            destination = Path(tmp) / "fresh"
            receipt = assembly.assemble(destination)
            self.assertEqual(receipt["files_sha256"]["candidate/tested-runtime/strict_serial_check.py"], assembly.digest(files["candidate/tested-runtime/strict_serial_check.py"]))
            runner = files["candidate/strict_sampler.py"].decode()
            preparation = files["preparation/prepare_memos.py"].decode()
            self.assertIn(assembly.digest(files["candidate/tested-runtime/strict_serial_check.py"]), runner)
            self.assertIn(assembly.digest(files["candidate/strict_sampler.py"]), preparation)
            self.assertIn(b"OSC frame crosses bounded serial-tail boundary", files["supervisor/vm_sampler_supervisor.py"])
            self.assertIn(b"backwards within serial batch", files["supervisor/vm_sampler_supervisor.py"])

if __name__ == "__main__":
    unittest.main()
