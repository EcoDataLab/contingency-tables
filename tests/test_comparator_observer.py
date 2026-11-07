"""Frozen offline fixtures, with a suite-scoped Python 3.10 hash adapter."""
from contextlib import ExitStack, contextmanager
import hashlib
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[1] / "research/strict-sampler-checkpoints/proc-observer-v2/source"

def _suite_module(name):
    spec = importlib.util.spec_from_file_location("strict_comparator_" + name, SOURCE / ("test_" + name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

_observer = _suite_module("observer")
_supervisor = _suite_module("supervisor")
_progress = _suite_module("progress")

Observer = _observer.Observer
SupervisorTests = _supervisor.SupervisorTests
Progress = _progress.Progress

# These are private module instances loaded by the frozen offline fixtures.
_HASH_MODULES = (_observer.m, _supervisor.vm, _supervisor.installer,
                 _progress.guest, _progress.vm)


def _stream_file_digest(stream, digest):
    """Hash the freshly opened blocking binary streams used by these fixtures."""
    value = hashlib.new(digest) if isinstance(digest, str) else digest()
    while True:
        chunk = stream.read(1024 * 1024)
        if not chunk:
            return value
        value.update(chunk)


class _PortableHashlib:
    file_digest = staticmethod(_stream_file_digest)

    def __getattr__(self, name):
        return getattr(hashlib, name)


@contextmanager
def _fixture_hash_compatibility():
    # Python 3.11+ keeps the native API. Never modify the hashlib module itself.
    with ExitStack() as stack:
        if not hasattr(hashlib, "file_digest"):
            adapter = _PortableHashlib()
            for module in _HASH_MODULES:
                stack.enter_context(patch.object(module, "hashlib", adapter))
        yield


class _CompatibleFixtureSuite(unittest.TestSuite):
    def run(self, result, debug=False):
        with _fixture_hash_compatibility():
            return super().run(result, debug=debug)


def load_tests(loader, tests, pattern):
    return _CompatibleFixtureSuite(tests)
