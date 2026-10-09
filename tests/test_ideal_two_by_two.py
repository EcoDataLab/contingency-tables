"""Replay the independent graph and rational witnesses against the backend."""
import importlib.util
import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "ideal_two_by_two", ROOT / "experiments/ideal_two_by_two.py")
experiment = importlib.util.module_from_spec(spec)
spec.loader.exec_module(experiment)


class IdealTwoByTwoCertificate(unittest.TestCase):
    def test_saved_certificate_matches_independent_graph_and_backend(self):
        # run() independently enumerates the base graph, checks a harmonic
        # witness, and compares complete graphs and return kernels at t=1..6.
        actual = experiment.jsonable(experiment.run())
        saved = json.loads((ROOT / "reports/ideal-two-by-two.json").read_text())
        self.assertEqual(actual, saved)


if __name__ == "__main__":
    unittest.main()
