"""Independent finite-fiber oracles and certificate checks for linear bounds."""

from dataclasses import replace
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import random
import runpy
import tempfile
import unittest
from unittest.mock import patch

from contingency115.optimize import (
    FlowCutCertificate,
    InfeasibleFlowError,
    LinearCertificate,
    linear_bounds,
    optimize_linear,
    verify_infeasibility,
    verify_optimality,
)
from contingency115.tables import ComputationBudgetExceeded, InfeasibleTableError, TableProblem


def brute_tables(problem):
    """Cartesian cell enumeration; uses no sampler or flow implementation."""
    m, n = problem.shape
    cells = [range(problem.lower_bounds[i][j], problem.upper_bounds[i][j] + 1)
             for i in range(m) for j in range(n)]
    for flattened in product(*cells):
        table = tuple(tuple(flattened[i * n:(i + 1) * n]) for i in range(m))
        if tuple(map(sum, table)) != problem.row_sums:
            continue
        if tuple(sum(table[i][j] for i in range(m)) for j in range(n)) != problem.column_sums:
            continue
        yield table


def objective(table, costs):
    return sum((value * cost for row, row_costs in zip(table, costs)
                for value, cost in zip(row, row_costs)), Fraction(0))


class LinearBoundsTests(unittest.TestCase):
    def check_against_enumeration(self, problem, costs):
        tables = tuple(brute_tables(problem))
        if not tables:
            with self.assertRaises(InfeasibleTableError):
                linear_bounds(problem, costs)
            return
        values = [objective(table, costs) for table in tables]
        bounds = linear_bounds(problem, costs)
        self.assertEqual((bounds.minimum.value, bounds.maximum.value), (min(values), max(values)))
        for result in (bounds.minimum, bounds.maximum):
            self.assertIn(result.table, tables)
            self.assertEqual(objective(result.table, costs), result.value)
            self.assertTrue(verify_optimality(problem, costs, result.table, result.certificate))

    def test_all_two_by_two_small_caps(self):
        costs = [[Fraction(-2, 3), Fraction(5, 7)], [4, Fraction(-9, 5)]]
        for caps in product(range(3), repeat=4):
            with self.subTest(caps=caps):
                problem = TableProblem([2, 2], [2, 2], [caps[:2], caps[2:]])
                self.check_against_enumeration(problem, costs)

    def test_seeded_bounded_lower_shifted_rectangles(self):
        rng = random.Random(115)
        for m, n in ((1, 3), (2, 3), (3, 2), (3, 1)):
            for trial in range(45):
                witness = [[rng.randrange(3) for _ in range(n)] for _ in range(m)]
                rows = list(map(sum, witness))
                columns = [sum(witness[i][j] for i in range(m)) for j in range(n)]
                lower = [[rng.randrange(witness[i][j] + 1) for j in range(n)] for i in range(m)]
                upper = [[rng.randrange(witness[i][j], 3) for j in range(n)] for i in range(m)]
                # Alternate guaranteed-feasible and potentially incompatible controls.
                if trial % 2:
                    i, j = rng.randrange(m), rng.randrange(n)
                    upper[i][j] = lower[i][j]
                costs = [[Fraction(rng.randrange(-7, 8), rng.randrange(1, 8)) for _ in range(n)]
                         for _ in range(m)]
                with self.subTest(shape=(m, n), trial=trial):
                    self.check_against_enumeration(TableProblem(rows, columns, upper, lower), costs)

    def test_synthetic_commute_range(self):
        fixture_path = Path(__file__).resolve().parents[1] / "examples" / "synthetic_commute.json"
        fixture = json.loads(fixture_path.read_text())
        problem = TableProblem(fixture["row_sums"], fixture["column_sums"],
                               fixture["upper_bounds"], fixture["lower_bounds"])
        costs = [[distance * fixture["commute_legs_per_workday"] * fixture["workdays_per_year"]
                  * Fraction(vehicle_factor) for vehicle_factor in fixture["vehicle_per_worker_by_mode"]]
                 for distance in fixture["one_way_distance_miles"]]
        tables = tuple(brute_tables(problem))
        self.assertEqual(len(tables), 42)
        expected = fixture["expected_reference"]
        bounds = linear_bounds(problem, costs)
        self.assertEqual(bounds.minimum.value, Fraction(expected["minimum_metric"]))
        self.assertEqual(bounds.maximum.value, Fraction(expected["maximum_metric"]))
        self.assertEqual((bounds.minimum.value, bounds.maximum.value), (9460, 25080))
        self.check_against_enumeration(problem, costs)

    def test_binary_capacities_are_not_expanded_to_units(self):
        huge = 1 << 200
        costs = [[1, Fraction(-1, 7)], [Fraction(-4, 3), 2]]
        small_bounds = linear_bounds(TableProblem([1, 1], [1, 1]), costs)
        huge_problem = TableProblem([huge, huge], [huge, huge])
        bounds = linear_bounds(huge_problem, costs)
        self.assertEqual(bounds.minimum.value, huge * Fraction(-31, 21))
        self.assertEqual(bounds.maximum.value, huge * 3)
        self.assertEqual(bounds.minimum.table, ((0, huge), (huge, 0)))
        self.assertEqual(bounds.maximum.table, ((huge, 0), (0, huge)))
        self.assertEqual(bounds.work_used, small_bounds.work_used)
        self.assertEqual((bounds.minimum.augmentations, bounds.maximum.augmentations), (2, 2))
        for result in (bounds.minimum, bounds.maximum):
            self.assertTrue(verify_optimality(huge_problem, costs, result.table, result.certificate))

    def test_fixed_cells_and_zero_total(self):
        self.check_against_enumeration(TableProblem([3, 3], [2, 4],
                                                   [[1, 2], [1, 2]], [[1, 2], [1, 2]]),
                                       [[Fraction(-1, 3), 4], [7, Fraction(-3, 5)]])
        problem = TableProblem([0, 0], [0, 0])
        bounds = linear_bounds(problem, [[-10, 15], [Fraction(7, 3), 0]], max_work=1)
        self.assertEqual((bounds.minimum.value, bounds.maximum.value), (0, 0))
        self.assertEqual(bounds.work_used, 0)

    def test_row_column_cost_shifts_and_transpose(self):
        problem = TableProblem([3, 2], [1, 2, 2], [[1, 2, 2], [1, 1, 2]])
        costs = [[-2, 7, Fraction(1, 3)], [1, Fraction(-4, 5), 9]]
        rows, columns = [Fraction(1, 2), -8], [3, Fraction(-2, 3), 4]
        shifted_costs = [[costs[i][j] + rows[i] + columns[j] for j in range(3)] for i in range(2)]
        shift = sum(a * b for a, b in zip(rows, problem.row_sums)) + sum(
            a * b for a, b in zip(columns, problem.column_sums))
        original, shifted = linear_bounds(problem, costs), linear_bounds(problem, shifted_costs)
        transposed = linear_bounds(problem.transpose(), tuple(zip(*costs)))
        self.assertEqual(shifted.minimum.value, original.minimum.value + shift)
        self.assertEqual(shifted.maximum.value, original.maximum.value + shift)
        self.assertEqual(transposed.minimum.value, original.minimum.value)
        self.assertEqual(transposed.maximum.value, original.maximum.value)

    def test_deterministic_input_validation(self):
        problem = TableProblem([1, 1], [1, 1])
        for invalid in (True, 0.5, "1/2", float("inf"), float("nan")):
            with self.subTest(cost=invalid), self.assertRaises(TypeError):
                optimize_linear(problem, [[invalid, 0], [0, 0]])
        for invalid in ([], [[1, 2]], [[1], [2]], [[1, 2], [3]]):
            with self.subTest(shape=invalid), self.assertRaises(ValueError):
                optimize_linear(problem, invalid)
        for invalid in (True, 1.5, "10"):
            with self.subTest(budget=invalid), self.assertRaises(TypeError):
                optimize_linear(problem, [[0, 0], [0, 0]], max_work=invalid)
        for invalid in (0, -1):
            with self.subTest(budget=invalid), self.assertRaises(ValueError):
                optimize_linear(problem, [[0, 0], [0, 0]], max_work=invalid)
        with self.assertRaises(TypeError):
            optimize_linear(problem, [[0, 0], [0, 0]], maximize=1)
        with self.assertRaises(TypeError):
            optimize_linear(None, [[0]])
        # Malformed scientific inputs are rejected before a feasibility result.
        with self.assertRaises(TypeError):
            optimize_linear(TableProblem([1], [2]), [[False]])

    def test_budget_is_shared_and_never_returns_partial_range(self):
        problem, costs = TableProblem([2, 2], [2, 2]), [[0, 2], [3, 0]]
        bounds = linear_bounds(problem, costs)
        self.assertGreater(bounds.work_used, bounds.minimum.work_used)
        self.assertEqual(linear_bounds(problem, costs, max_work=bounds.work_used), bounds)
        with self.assertRaises(ComputationBudgetExceeded):
            linear_bounds(problem, costs, max_work=bounds.work_used - 1)
        with self.assertRaises(ComputationBudgetExceeded):
            optimize_linear(problem, costs, max_work=1)


class CertificateTests(unittest.TestCase):
    def test_certificate_verifier_is_independent_of_optimizer(self):
        problem, costs = TableProblem([2, 2], [2, 2]), [[0, 3], [2, 0]]
        optimum = optimize_linear(problem, costs)
        with patch("contingency115.optimize._optimize", side_effect=AssertionError("solver called")), \
             patch("contingency115.optimize._distances", side_effect=AssertionError("search called")), \
             patch.object(TableProblem, "feasibility", side_effect=AssertionError("flow called")):
            self.assertTrue(verify_optimality(problem, costs, optimum.table, optimum.certificate))
            manual = LinearCertificate(False, (Fraction(0), Fraction(0)),
                                       (Fraction(0), Fraction(0)), Fraction(0))
            self.assertTrue(verify_optimality(problem, costs, ((2, 0), (0, 2)), manual))

    def test_tampered_witness_cost_direction_value_and_potentials_fail(self):
        problem, costs = TableProblem([2, 2], [2, 2]), [[0, 3], [2, 0]]
        optimum = optimize_linear(problem, costs)
        cert = optimum.certificate
        self.assertFalse(verify_optimality(problem, costs, ((1, 1), (1, 1)), cert))
        self.assertFalse(verify_optimality(problem, costs, ((2, 0), (0, 1)), cert))
        self.assertFalse(verify_optimality(problem, costs, ((True, 1), (1, 1)), cert))
        self.assertFalse(verify_optimality(problem, [[-1, 3], [2, -1]], optimum.table, cert))
        for changed in (replace(cert, bound=cert.bound + 1), replace(cert, maximize=True),
                        replace(cert, row_potentials=(Fraction(100), Fraction(0))),
                        replace(cert, column_potentials=(Fraction(0),)),
                        replace(cert, row_potentials=(True, Fraction(0))), replace(cert, bound=0.0),
                        replace(cert, maximize=1)):
            with self.subTest(certificate=changed):
                self.assertFalse(verify_optimality(problem, costs, optimum.table, changed))
        # Common potential offsets cancel, as a correct dual certificate requires.
        shifted = replace(cert, row_potentials=tuple(p + 17 for p in cert.row_potentials),
                          column_potentials=tuple(p + 17 for p in cert.column_potentials))
        self.assertTrue(verify_optimality(problem, costs, optimum.table, shifted))

    def test_support_obstruction_has_independent_cut_certificate(self):
        problem = TableProblem([2, 2, 2], [2, 2, 2], [[2, 0, 0], [2, 0, 0], [0, 2, 2]])
        costs = [[Fraction(i - j, 7) for j in range(3)] for i in range(3)]
        self.assertEqual(list(brute_tables(problem)), [])
        with self.assertRaises(InfeasibleFlowError) as caught:
            optimize_linear(problem, costs)
        cert = caught.exception.certificate
        self.assertEqual((cert.capacity, cert.required), (4, 6))
        with patch("contingency115.optimize._distances", side_effect=AssertionError("search called")), \
             patch.object(TableProblem, "feasibility", side_effect=AssertionError("flow called")):
            self.assertTrue(verify_infeasibility(problem, cert))
        for changed in (replace(cert, capacity=3), replace(cert, required=7),
                        replace(cert, rows=(0, 0)), replace(cert, columns=(3,)),
                        replace(cert, rows=(True,)), replace(cert, required=True)):
            self.assertFalse(verify_infeasibility(problem, changed))
        self.assertFalse(verify_infeasibility(TableProblem([2, 2, 2], [2, 2, 2]), cert))

    def test_lower_shifted_support_obstruction(self):
        problem = TableProblem([4, 2, 2], [3, 3, 2],
                               [[3, 1, 0], [2, 0, 0], [0, 2, 2]],
                               [[1, 1, 0], [0, 0, 0], [0, 0, 0]])
        with self.assertRaises(InfeasibleFlowError) as caught:
            optimize_linear(problem, [[0] * 3 for _ in range(3)])
        self.assertTrue(verify_infeasibility(problem, caught.exception.certificate))

    def test_elementary_infeasibility_is_explicit(self):
        problems = [TableProblem([1], [2]),
                    TableProblem([1, 3], [2, 2], lower_bounds=[[1, 1], [0, 0]]),
                    TableProblem([2], [2], lower_bounds=[[1]], structural_zeros=[(0, 0)]),
                    TableProblem([1], [1], lower_bounds=[[2]])]
        for problem in problems:
            m, n = problem.shape
            with self.subTest(problem=problem), self.assertRaises(InfeasibleTableError):
                optimize_linear(problem, [[0] * n for _ in range(m)])
            self.assertFalse(verify_infeasibility(problem, FlowCutCertificate((), (), 0, 1)))


class ReportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(__file__).resolve().parents[1]
        cls.fixture = root / "examples" / "synthetic_commute.json"
        cls.example = runpy.run_path(str(root / "examples" / "linear_metric_bounds.py"))

    def test_serialized_report_has_independently_verifiable_endpoints(self):
        report = self.example["build_report"](self.fixture, 100_000)
        # Treat the JSON as a standalone artifact, reconstructing all solver
        # inputs and certificate fields; no in-memory optimizer state is reused.
        report = json.loads(json.dumps(report))
        problem = TableProblem(**report["problem"])
        costs = [[Fraction(value) for value in row] for row in report["metric"]["coefficients"]]
        self.assertEqual(report["status"], "optimal")
        self.assertEqual((report["minimum"]["value"], report["maximum"]["value"]), ("9460", "25080"))
        for direction in ("minimum", "maximum"):
            endpoint = report[direction]
            certificate = endpoint["certificate"]
            cert = LinearCertificate(certificate["maximize"], tuple(map(Fraction, certificate["row_potentials"])),
                                     tuple(map(Fraction, certificate["column_potentials"])),
                                     Fraction(certificate["bound"]))
            self.assertTrue(verify_optimality(problem, costs, endpoint["table"], cert))
            self.assertEqual(certificate["signed_primal"], certificate["signed_dual"])
            self.assertTrue(all(endpoint["verification"].values()))

    def test_serialized_cut_report_and_elementary_failure(self):
        fixture = json.loads(self.fixture.read_text())
        fixture.update(row_sums=[2, 2, 2], column_sums=[2, 2, 2],
                       upper_bounds=[[2, 0, 0], [2, 0, 0], [0, 2, 2]], lower_bounds=[[0] * 3 for _ in range(3)],
                       vehicle_per_worker_by_mode=[1, "1/2", 0])
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "infeasible.json"
            source.write_text(json.dumps(fixture))
            report = json.loads(json.dumps(self.example["build_report"](source, 100_000)))
            self.assertEqual(report["status"], "infeasible")
            payload = report["certificate"]
            cert = FlowCutCertificate(tuple(payload["rows"]), tuple(payload["columns"]),
                                      payload["capacity"], payload["required"])
            self.assertTrue(verify_infeasibility(TableProblem(**report["problem"]), cert))
            self.assertTrue(all(report["verification"].values()))
            fixture["column_sums"] = [2, 2, 1]
            source.write_text(json.dumps(fixture))
            elementary = self.example["build_report"](source, 100_000)
            self.assertEqual(elementary["certificate"]["violations"][0]["kind"], "unequal_margin_totals")
            self.assertTrue(elementary["verification"]["direct_contradictions_verified"])

    def test_budget_report_contains_no_partial_endpoints(self):
        report = self.example["build_report"](self.fixture, 1)
        self.assertEqual(report["status"], "budget_exceeded")
        self.assertIsNone(report["endpoints"])
        self.assertNotIn("minimum", report)
        self.assertNotIn("maximum", report)

    def test_example_rejects_float_and_boolean_coefficients(self):
        for invalid in (0.5, True):
            with self.subTest(value=invalid), self.assertRaises(TypeError):
                self.example["exact_input"](invalid, "test coefficient")


if __name__ == "__main__":
    unittest.main()
