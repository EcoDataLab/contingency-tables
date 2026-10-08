"""Tests for synthetic feasibility and the constructive fiber-size certificate."""

from copy import deepcopy
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import runpy
import subprocess
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from contingency115.optimize import LinearCertificate, verify_optimality
from contingency115.tables import TableProblem


BENCHMARK = runpy.run_path(str(Path(__file__).resolve().parents[1] / "experiments" / "commute_scaling.py"))


class CommuteScalingTests(unittest.TestCase):
    def test_generator_is_deterministic_nested_and_feasible(self):
        generator = BENCHMARK["synthetic_problem"]
        small = generator(4)
        self.assertEqual(small, generator(4))
        larger = generator(12)
        problem, costs, anchor, distances = larger
        self.assertEqual(anchor[:4], small[2])
        self.assertEqual(costs[:4], small[1])
        self.assertEqual(distances[:4], small[3])
        self.assertEqual(problem.validate_table(anchor), anchor)
        self.assertTrue(all(25 <= total <= 250 for total in problem.row_sums))
        self.assertTrue(all(isinstance(cost, Fraction) for row in costs for cost in row))
        self.assertTrue(any(cost.denominator > 1 for row in costs for cost in row))
        self.assertTrue(any(value == 0 for row in problem.upper_bounds for value in row))
        self.assertTrue(any(value > 0 for row in problem.lower_bounds for value in row))

    def test_switch_product_constructs_distinct_feasible_tables(self):
        problem = TableProblem([2] * 4, [4, 0, 0, 0, 4])
        anchor = ((1, 0, 0, 0, 1),) * 4
        certificate = BENCHMARK["switch_family"](problem, anchor)
        self.assertEqual(certificate["lower_bound"], "9")
        self.assertTrue(BENCHMARK["verify_switch_family"](problem, anchor, certificate))
        distinct = set()
        for amounts in product(*(range(cycle["minimum_t"], cycle["maximum_t"] + 1)
                                 for cycle in certificate["cycles"])):
            table = [list(row) for row in anchor]
            for cycle, t in zip(certificate["cycles"], amounts):
                i, k = cycle["rows"]
                j, ell = cycle["columns"]
                table[i][j] += t
                table[i][ell] -= t
                table[k][j] -= t
                table[k][ell] += t
            distinct.add(problem.validate_table(table))
        self.assertEqual(len(distinct), 9)
        # Independently enumerate the full fiber via its four drive counts.
        all_tables = {tuple((x, 0, 0, 0, 2 - x) for x in counts)
                      for counts in product(range(3), repeat=4) if sum(counts) == 4}
        self.assertEqual(len(all_tables), 19)
        self.assertTrue(distinct < all_tables)

    def test_switch_verifier_rejects_tampering(self):
        problem = TableProblem([2] * 4, [4, 0, 0, 0, 4])
        anchor = ((1, 0, 0, 0, 1),) * 4
        certificate = BENCHMARK["switch_family"](problem, anchor)
        invalid = []
        for key, value in (("lower_bound", "10"), ("is_exact_fiber_count", True)):
            changed = deepcopy(certificate)
            changed[key] = value
            invalid.append(changed)
        for key, value in (("rows", [1, 2]), ("columns", [0, 0]), ("maximum_t", 2),
                           ("choices", 4), ("minimum_t", True)):
            changed = deepcopy(certificate)
            changed["cycles"][1][key] = value
            invalid.append(changed)
        for changed in invalid:
            self.assertFalse(BENCHMARK["verify_switch_family"](problem, anchor, changed))

    def test_small_report_json_reconstructs_verified_results(self):
        case = json.loads(json.dumps(BENCHMARK["run_case"](4, 100_000, 20, 100)))
        problem = TableProblem(**case["problem"])
        costs = [[Fraction(value) for value in row] for row in case["coefficients"]]
        self.assertTrue(BENCHMARK["verify_switch_family"](problem, case["anchor_table"], case["fiber_size_certificate"]))
        self.assertEqual(case["exact_dp"]["status"], "budget_exceeded")
        self.assertLessEqual(case["exact_dp"]["stats"]["states_visited"], 20)
        self.assertLessEqual(case["exact_dp"]["stats"]["transitions_visited"], 100)
        for endpoint in (case["optimizer"]["minimum"], case["optimizer"]["maximum"]):
            raw = endpoint["certificate"]
            cert = LinearCertificate(raw["maximize"], tuple(map(Fraction, raw["row_potentials"])),
                                     tuple(map(Fraction, raw["column_potentials"])), Fraction(raw["bound"]))
            self.assertTrue(verify_optimality(problem, costs, endpoint["table"], cert))

    def test_budget_and_watchdog_do_not_claim_partial_bounds(self):
        case = BENCHMARK["run_case"](4, 1, 20, 100)
        self.assertEqual(case["optimizer"]["status"], "budget_exceeded")
        self.assertEqual(case["optimizer"]["residual_arc_examinations"], 1)
        self.assertFalse(case["optimizer"]["result_available"])
        self.assertNotIn("minimum", case["optimizer"])
        args = SimpleNamespace(max_work=1, max_states=20, max_transitions=100, seed=1152026, case_timeout=0.001)
        with patch("subprocess.run", side_effect=subprocess.TimeoutExpired("benchmark worker", 0.001)):
            result = BENCHMARK["_worker"](args, 4)
        self.assertEqual(result["status"], "watchdog_timeout")
        self.assertNotIn("optimizer", result)


if __name__ == "__main__":
    unittest.main()
