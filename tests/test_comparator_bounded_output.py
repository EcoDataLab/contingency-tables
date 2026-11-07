"""Normal discovery of the additive bounded Comparator-output regressions."""
import importlib.util
from pathlib import Path

_path = (Path(__file__).resolve().parents[1] / "research/strict-sampler-checkpoints"
         / "runtime-output-v1/tests/test_bounded_output.py")
_spec = importlib.util.spec_from_file_location("comparator_bounded_output_fixtures", _path)
_module = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_module)

def load_tests(loader, tests, pattern):
    return loader.loadTestsFromModule(_module)
