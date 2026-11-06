"""Regression coverage for the strict observer failure and bounded VM supervision."""
import importlib.util
from pathlib import Path

SOURCE = Path(__file__).resolve().parents[1] / "research/strict-sampler-checkpoints/proc-observer-v2/source"

def _suite_module(name):
    spec = importlib.util.spec_from_file_location("strict_comparator_" + name, SOURCE / ("test_" + name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

Observer = _suite_module("observer").Observer
SupervisorTests = _suite_module("supervisor").SupervisorTests
Progress = _suite_module("progress").Progress
