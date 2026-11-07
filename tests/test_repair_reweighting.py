"""Exercise the changed target law and failure modes, not timing thresholds."""
import importlib.util
from fractions import Fraction as F
from pathlib import Path
import unittest

from contingency115.ideal_chain import build_rescaled_ideal_chain
from contingency115.tables import TableProblem

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("repair_reweighting", ROOT / "experiments/repair_reweighting.py")
experiment = importlib.util.module_from_spec(spec)
spec.loader.exec_module(experiment)


class RepairReweightingTests(unittest.TestCase):
    def test_independent_fibers_and_exact_probability_laws(self):
        result = experiment.report()
        self.assertEqual(len(result["cases"]), 11)
        for item in result["cases"][:6]:
            t = item["rows"][0]
            self.assertEqual(item["tables"], t + 1)
            self.assertEqual(item["physical_states"], 13 * t + 1)
        varying = result["cases"][1]
        self.assertFalse(varying["old_law_naive_repair_is_uniform"])
        self.assertEqual(varying["mh_gap_allowance_multiplier"], "13/7")
        self.assertEqual(varying["old_balanced_output_success"], "1/9")
        scaled = varying["scaled_repair_rejection"]
        self.assertEqual(scaled["stationary_success"], "7/9")
        self.assertEqual(scaled["certified_inverse_success_allowance"], "13/7")

    def test_reversed_metropolis_ratio_is_detected(self):
        chain = build_rescaled_ideal_chain(TableProblem((2, 2), (2, 2)), U=3, L=1)
        repaired, loads, weights, _ = experiment.reweighted(chain)
        wrong = []
        for i, row in enumerate(chain.matrix):
            values = [F(0) if i == j else p * min(F(1), F(loads[j], loads[i]))
                      for j, p in enumerate(row)]
            values[i] = 1 - sum(values)
            wrong.append(tuple(values))
        with self.assertRaises(AssertionError):
            experiment.verify(chain, repaired, loads, weights, tuple(wrong))

    def test_rejects_scope_outside_positive_all_small_margins(self):
        for rows, columns, cutoff in [((0, 1), (1,), 2), ((2,), (2,), 2)]:
            chain = build_rescaled_ideal_chain(TableProblem(rows, columns), U=cutoff, L=1)
            with self.assertRaises(ValueError):
                experiment.reweighted(chain)


if __name__ == "__main__":
    unittest.main()
