"""Normal discovery for the additive bounded serial-tail parser correction."""
import importlib.util
from pathlib import Path

_path = (Path(__file__).resolve().parents[1] / "research/strict-sampler-checkpoints"
         / "runtime-tail-v1/tests/test_tail_boundary.py")
_spec = importlib.util.spec_from_file_location("comparator_tail_boundary_fixtures", _path)
_module = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_module)

def load_tests(loader, tests, pattern):
    return loader.loadTestsFromModule(_module)
