"""Expose the additive Comparator metadata repair regressions to normal discovery."""
import importlib.util
from pathlib import Path

_source = (Path(__file__).resolve().parents[1] / "research" / "strict-sampler-checkpoints"
           / "metadata-memory-v1" / "tests" / "test_memory_fix.py")
_spec = importlib.util.spec_from_file_location("comparator_metadata_memory_fixtures", _source)
_fixtures = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_fixtures)

def load_tests(loader, tests, pattern):
    return loader.loadTestsFromModule(_fixtures)
