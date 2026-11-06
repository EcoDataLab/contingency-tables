"""The frozen fixture bridge preserves real hashes on Python 3.10."""
import hashlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import test_comparator_observer as bridge


class ComparatorHashCompatibilityTests(unittest.TestCase):
    def test_streaming_hash_matches_known_vectors_and_native_binary_files(self):
        native = getattr(hashlib, "file_digest", None)
        vectors = [(b"", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
                   (b"abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
                   (bytes(range(256)) * 8193, None)]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.bin"
            for data, known in vectors:
                with self.subTest(bytes=len(data)):
                    path.write_bytes(data)
                    expected = hashlib.sha256(data).hexdigest()
                    if known is not None:
                        self.assertEqual(expected, known)
                    with path.open("rb") as stream:
                        result = bridge._stream_file_digest(stream, "sha256").hexdigest()
                        self.assertFalse(stream.closed)
                    self.assertEqual(result, expected)
                    if native is not None:
                        with path.open("rb") as stream:
                            self.assertEqual(result, native(stream, "sha256").hexdigest())

        class ShortReads(io.BytesIO):
            def read(self, size=-1):
                self_test.assertEqual(size, 1024 * 1024)
                return super().read(min(size, 7))

        self_test = self
        data = b"partial reads preserve every byte" * 31
        self.assertEqual(bridge._stream_file_digest(ShortReads(data), hashlib.sha256).digest(),
                         hashlib.sha256(data).digest())
        self.assertNotEqual(bridge._stream_file_digest(io.BytesIO(data + b"x"), "sha256").digest(),
                            hashlib.sha256(data).digest())

    def test_native_api_and_module_bindings_are_preserved_outside_scope(self):
        native = getattr(hashlib, "file_digest", None)
        before = [module.hashlib for module in bridge._HASH_MODULES]
        with bridge._fixture_hash_compatibility():
            self.assertIs(getattr(hashlib, "file_digest", None), native)
            if native is not None:
                self.assertEqual([module.hashlib for module in bridge._HASH_MODULES], before)
        self.assertEqual([module.hashlib for module in bridge._HASH_MODULES], before)
        self.assertIs(getattr(hashlib, "file_digest", None), native)

    def test_all_36_frozen_fixtures_pass_without_file_digest(self):
        before = [module.hashlib for module in bridge._HASH_MODULES]
        with patch.object(hashlib, "file_digest", None, create=True):
            del hashlib.file_digest
            suite = unittest.defaultTestLoader.loadTestsFromModule(bridge)
            self.assertEqual(suite.countTestCases(), 36)
            result = unittest.TestResult()
            suite.run(result)
            self.assertEqual(result.testsRun, 36)
            self.assertEqual(result.failures, [])
            self.assertEqual(result.errors, [])
            self.assertEqual(result.skipped, [])
            self.assertFalse(hasattr(hashlib, "file_digest"))
            self.assertEqual([module.hashlib for module in bridge._HASH_MODULES], before)

    def test_fixture_bindings_restore_even_when_suite_debug_raises(self):
        before = [module.hashlib for module in bridge._HASH_MODULES]

        def failure():
            self.assertFalse(hasattr(hashlib, "file_digest"))
            for module in bridge._HASH_MODULES:
                self.assertIsInstance(module.hashlib, bridge._PortableHashlib)
                self.assertEqual(module.hashlib.file_digest(io.BytesIO(b"abc"), "sha256").digest(),
                                 hashlib.sha256(b"abc").digest())
            raise RuntimeError("fixture exception")

        with patch.object(hashlib, "file_digest", None, create=True):
            del hashlib.file_digest
            suite = bridge._CompatibleFixtureSuite([unittest.FunctionTestCase(failure)])
            with self.assertRaisesRegex(RuntimeError, "fixture exception"):
                suite.run(unittest.TestResult(), debug=True)
            self.assertFalse(hasattr(hashlib, "file_digest"))
            self.assertEqual([module.hashlib for module in bridge._HASH_MODULES], before)
