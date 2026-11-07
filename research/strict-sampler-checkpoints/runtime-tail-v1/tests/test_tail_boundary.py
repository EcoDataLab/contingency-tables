"""Adversarial physical-line boundary checks; no process or VM is started."""
import ast
import importlib.util
import json
from pathlib import Path
import re
import types
import unittest
from unittest.mock import patch

PACKET = Path(__file__).resolve().parents[1]
REPO = PACKET.parents[2]
recipe = json.loads((PACKET / "source/supervisor-recipe.json").read_text())
spec = importlib.util.spec_from_file_location("tail_supervisor_derivation", PACKET / "derive_supervisor.py")
derive = importlib.util.module_from_spec(spec)
spec.loader.exec_module(derive)

def load(raw, name):
    module = types.ModuleType(name)
    module.__file__ = str(REPO / recipe["source"])
    exec(compile(raw, module.__file__, "exec"), module.__dict__)
    module.TAIL_LIMIT = 256
    return module

old = load((REPO / recipe["source"]).read_bytes(), "frozen_tail_supervisor")
fixed = load(derive.source(), "fixed_tail_supervisor")
RESULTS = ((b"MATH115_C11_CHECK_RESULT=0\n", "strict_exit_code"),
           (b"MATH115_C11_EVIDENCE_COLLECTION_RESULT=0\n", "collection_exit_code"))

def feed(module, raw, chunks):
    state, tail, offset = {}, b"", 0
    for size in chunks:
        tail = module.parse_tail(tail + raw[offset:offset + size], state)
        offset += size
        if len(tail) > module.TAIL_LIMIT:
            raise AssertionError("Tail exceeded its bound")
    if offset < len(raw):
        tail = module.parse_tail(tail + raw[offset:], state)
    # The supervisor reparses its retained tail even when a read is empty.
    module.parse_tail(tail, state)
    return state

class TailBoundaryTests(unittest.TestCase):
    def test_old_counterexample_really_records_false_result(self):
        for marker, field in RESULTS:
            raw = b"not-a-line-" + marker + b"x" * (old.TAIL_LIMIT - len(marker))
            state = {}; tail = old.parse_tail(raw, state)
            self.assertNotIn(field, state)
            old.parse_tail(tail, state)
            self.assertEqual(state[field], 0)

    def test_repaired_counterexample_never_becomes_anchored(self):
        for marker, field in RESULTS:
            raw = b"not-a-line-" + marker + b"x" * (fixed.TAIL_LIMIT - len(marker))
            self.assertNotIn(field, feed(fixed, raw, [len(raw)]))

    def test_all_split_positions_and_empty_reads_preserve_non_line_context(self):
        for marker, field in RESULTS:
            raw = b"prefix-without-newline-" + marker + b"x" * (fixed.TAIL_LIMIT - len(marker))
            for split in range(len(raw) + 1):
                with self.subTest(field=field, split=split):
                    self.assertNotIn(field, feed(fixed, raw, [split, 0, len(raw) - split]))

    def test_long_single_line_without_newline_cannot_create_a_marker(self):
        for marker, field in RESULTS:
            raw = b"x" * 2048 + marker[:-1]
            for size in (1, 7, 63, 255, 256, 257, 1024):
                sizes = [size] * (len(raw) // size)
                state = feed(fixed, raw, sizes)
                self.assertNotIn(field, state)
                self.assertNotIn(field, feed(fixed, raw + b"\n", sizes))

    def test_actual_256k_tail_and_64k_reads_preserve_physical_context(self):
        with patch.object(fixed, "TAIL_LIMIT", 256 * 1024):
            for marker, field in RESULTS:
                raw = b"x" * 65536 + marker + b"y" * (fixed.TAIL_LIMIT - len(marker))
                self.assertNotIn(field, feed(fixed, raw, [65536] * 5))

    def test_true_line_markers_survive_oversized_prefix_and_split(self):
        for marker, field in RESULTS:
            for newline in (b"\n", b"\r", b"\r\n"):
                raw = b"x" * 2048 + newline + marker
                for size in (1, 7, 63, 255, 256, 257, 1024):
                    self.assertEqual(feed(fixed, raw, [size] * (len(raw) // size))[field], 0)

    def test_context_cut_immediately_after_physical_newline_preserves_marker(self):
        for marker, field in RESULTS:
            # The retained suffix starts at the marker; its predecessor is a real newline.
            raw = b"prefix\n" + marker + b"x" * (fixed.TAIL_LIMIT - len(marker) - 1)
            self.assertEqual(feed(fixed, raw, [len(raw)])[field], 0)

    def test_every_short_chunk_size_matches_full_stream_result_oracle(self):
        for prefix in (b"", b"x" * 1000, b"x" * 1000 + b"\n"):
            for marker, field in RESULTS:
                raw = prefix + marker + b"suffix" * 80
                expected = bool(re.search(rb"(?m)^" + re.escape(marker), raw))
                for size in range(1, 81):
                    actual = field in feed(fixed, raw, [size] * (len(raw) // size))
                    self.assertEqual(actual, expected, (len(prefix), field, size))

    def test_other_marker_families_keep_line_anchoring(self):
        markers = ((b"MATH115_C11_STAGE=proof\n", "guest_phase"),
                   (b"MATH115_C11_PROVISION_READY\n", "guest_provisioning_ready"),
                   (b"MATH115_C11_RUNTIME_FREEZE_SHA256=" + b"a" * 64 + b"\n", "runtime_freeze_sha256"))
        for marker, field in markers:
            raw = b"prefix-" + marker + b"x" * (fixed.TAIL_LIMIT - len(marker))
            self.assertNotIn(field, feed(fixed, raw, [len(raw)]))

    def test_osc_opener_cannot_be_discarded_to_expose_false_success(self):
        markers = b"".join(marker for marker, _ in RESULTS)
        raw = b"\x1b]0;opaque-title\n" + markers + b"x" * (254 - len(markers)) + b"\x07"
        state = {}; tail = old.parse_tail(raw, state)
        self.assertEqual(state, {})
        old.parse_tail(tail, state)
        self.assertEqual((state["strict_exit_code"], state["collection_exit_code"]), (0, 0))
        with self.assertRaisesRegex(fixed.SupervisorError, "OSC frame crosses"):
            fixed.parse_tail(raw, {})

    def test_incomplete_osc_contents_are_not_plain_result_lines(self):
        raw = b"\x1b]title\n" + b"".join(marker for marker, _ in RESULTS)
        for split in range(len(raw) + 1):
            state = feed(fixed, raw, [split, 0, len(raw) - split])
            self.assertNotIn("strict_exit_code", state)
            self.assertNotIn("collection_exit_code", state)

    def test_short_complete_osc_preserves_following_true_markers(self):
        markers = b"".join(marker for marker, _ in RESULTS)
        for terminator in (b"\x07", b"\x1b\\"):
            raw = b"\x1b]title\nignored" + terminator + markers
            for split in range(len(raw) + 1):
                state = feed(fixed, raw, [split, len(raw) - split])
                self.assertEqual((state["strict_exit_code"], state["collection_exit_code"]), (0, 0))

    def test_old_parser_hides_within_batch_phase_reversals(self):
        for names in (("proof", "repair"), ("proof", "repair", "proof")):
            raw = "".join("MATH115_C11_STAGE=" + name + "\n" for name in names).encode()
            state = {}; old.parse_tail(raw, state)
            self.assertEqual(state["guest_phase"], names[-1])

    def test_repaired_parser_rejects_every_within_batch_phase_reversal(self):
        for names in (("proof", "repair"), ("proof", "repair", "proof")):
            raw = "".join("MATH115_C11_STAGE=" + name + "\n" for name in names).encode()
            with self.assertRaisesRegex(fixed.SupervisorError, "backwards within"):
                fixed.parse_tail(raw, {})

    def test_ordered_batch_and_repeated_tail_keep_phase_timer(self):
        raw = b"MATH115_C11_STAGE=install\nMATH115_C11_STAGE=repair\nMATH115_C11_STAGE=proof\n"
        state = {}
        with patch.object(fixed.time, "monotonic", return_value=10):
            tail = fixed.parse_tail(raw, state)
        self.assertEqual(state["guest_phase"], "proof")
        with patch.object(fixed.time, "monotonic", return_value=100):
            fixed.parse_tail(tail, state)
        self.assertEqual(state["guest_phase_observed_monotonic"], 10)
        with self.assertRaisesRegex(fixed.SupervisorError, "moved backwards"):
            fixed.parse_tail(b"MATH115_C11_STAGE=repair\n", state)

    def test_phase_rollback_after_previous_marker_trimmed_is_rejected(self):
        state = {}; tail = fixed.parse_tail(b"MATH115_C11_STAGE=proof\n", state)
        tail = fixed.parse_tail(tail + b"x" * 300 + b"\n", state)
        self.assertEqual(state["_retained_phase_events"], [])
        with self.assertRaisesRegex(fixed.SupervisorError, "backwards at serial batch"):
            fixed.parse_tail(tail + b"MATH115_C11_STAGE=repair\nMATH115_C11_STAGE=proof\n", state)

    def test_new_completed_phase_after_partial_marker_is_processed_once(self):
        state = {}
        with patch.object(fixed.time, "monotonic", return_value=10):
            tail = fixed.parse_tail(b"MATH115_C11_STAGE=repair\nMATH115_C11_STAGE=pro", state)
        self.assertEqual(state["guest_phase"], "repair")
        with patch.object(fixed.time, "monotonic", return_value=20):
            tail = fixed.parse_tail(tail + b"of\n", state)
        self.assertEqual(state["guest_phase"], "proof")
        with patch.object(fixed.time, "monotonic", return_value=30):
            fixed.parse_tail(tail, state)
        self.assertEqual(state["guest_phase_observed_monotonic"], 20)

    def test_partial_result_tokens_never_accept_before_completed_newline(self):
        for marker, field in RESULTS:
            prefix = marker[:-1]
            for suffix, expected in ((b"\n", 0), (b"1\n", 1), (b"junk\n", None)):
                for split in range(len(prefix) + 1):
                    state = {}; tail = fixed.parse_tail(prefix[:split], state)
                    tail = fixed.parse_tail(tail + prefix[split:], state)
                    self.assertNotIn(field, state)
                    fixed.parse_tail(tail + suffix, state)
                    self.assertEqual(state.get(field), expected)

    def test_only_parse_tail_function_changes(self):
        before = ast.parse((REPO / recipe["source"]).read_bytes())
        after = ast.parse(derive.source())
        def without_parser(tree):
            return ast.dump(ast.Module(body=[n for n in tree.body if not isinstance(n, ast.FunctionDef) or n.name != "parse_tail"], type_ignores=[]), include_attributes=False)
        self.assertEqual(without_parser(before), without_parser(after))

if __name__ == "__main__":
    unittest.main()
