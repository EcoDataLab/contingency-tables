from fractions import Fraction
import unittest

from contingency115.kernels import Cycle, four_cycles, heat_bath_kernel, line_interval, simple_cycles
from contingency115.tables import ComputationBudgetExceeded, ExactTableSampler, ProductWeights, TableProblem


class CycleKernelTests(unittest.TestCase):
    def assert_stationary(self, kernel):
        self.assertTrue(kernel.is_stochastic())
        self.assertTrue(kernel.satisfies_detailed_balance())
        for j, mass in enumerate(kernel.stationary):
            self.assertEqual(sum(kernel.stationary[i] * kernel.matrix[i][j]
                                 for i in range(len(kernel.states))), mass)

    def test_full_line_draw_reaches_every_two_by_two_table(self):
        problem = TableProblem([4, 4], [4, 4], lower_bounds=[[1, 0], [0, 1]])
        tables = list(ExactTableSampler(problem).tables())
        catalog = four_cycles(problem)
        self.assertEqual(len(catalog), 1)
        kernel = heat_bath_kernel(problem, tables, catalog)
        self.assertEqual(len(tables), 4)
        self.assertEqual(kernel.matrix, tuple((Fraction(1, 4),) * 4 for _ in range(4)))
        for table in tables:
            lo, hi = line_interval(problem, table, catalog[0])
            self.assertEqual(hi - lo + 1, 4)
        self.assert_stationary(kernel)

    def test_sparse_six_cycle_is_frozen_for_rectangle_moves(self):
        problem = TableProblem([1, 1, 1], [1, 1, 1], [[1, 1, 0], [0, 1, 1], [1, 0, 1]])
        tables = list(ExactTableSampler(problem).tables())
        self.assertEqual(len(tables), 2)
        self.assertEqual(four_cycles(problem), ())
        rectangles = heat_bath_kernel(problem, tables, four_cycles(problem))
        self.assertEqual(rectangles.matrix, ((1, 0), (0, 1)))
        self.assertEqual(rectangles.communicating_classes(), ((0,), (1,)))
        catalog = simple_cycles(problem)
        self.assertEqual([cycle.length for cycle in catalog], [6])
        connected = heat_bath_kernel(problem, tables, catalog)
        self.assertEqual(connected.matrix, ((Fraction(1, 2), Fraction(1, 2)),) * 2)
        self.assertEqual(connected.communicating_classes(), ((0, 1),))
        self.assert_stationary(connected)

    def test_catalog_has_all_nine_rectangles_and_six_hexagons_in_k33(self):
        problem = TableProblem([2, 2, 2], [2, 2, 2])
        catalog = simple_cycles(problem)
        self.assertEqual(sum(cycle.length == 4 for cycle in catalog), 9)
        self.assertEqual(sum(cycle.length == 6 for cycle in catalog), 6)
        self.assertEqual(set(simple_cycles(problem, max_length=4)), set(four_cycles(problem)))
        with self.assertRaises(ComputationBudgetExceeded):
            simple_cycles(problem, max_cycles=1)
        with self.assertRaises(ComputationBudgetExceeded):
            simple_cycles(problem, max_search_nodes=1)
        for value in (1, 3, 5):
            with self.assertRaises(ValueError):
                simple_cycles(problem, max_length=value)

    def test_nonuniform_input_fixed_catalog_mixture_is_reversible(self):
        problem = TableProblem([3, 3], [2, 2, 2])
        tables = list(ExactTableSampler(problem).tables())
        kernel = heat_bath_kernel(problem, tables, four_cycles(problem),
                                  cycle_probabilities=[Fraction(1, 2), Fraction(1, 3), Fraction(1, 6)],
                                  hold_probability=Fraction(1, 4))
        self.assert_stationary(kernel)
        self.assertEqual(len(kernel.communicating_classes()), 1)
        self.assertTrue(all(kernel.matrix[i][i] >= Fraction(1, 4) for i in range(len(tables))))

    def test_weighted_conditional_line_is_not_a_uniform_line(self):
        problem = TableProblem([2, 2], [2, 2])
        tables = list(ExactTableSampler(problem).tables())
        weights = ProductWeights([[1, 1], [1, 1]], factorial_weight=True)
        kernel = heat_bath_kernel(problem, tables, four_cycles(problem), weights=weights)
        target = (Fraction(1, 6), Fraction(2, 3), Fraction(1, 6))
        self.assertEqual(kernel.stationary, target)
        self.assertEqual(kernel.matrix, (target,) * 3)
        self.assert_stationary(kernel)
        wrong = heat_bath_kernel(problem, tables, four_cycles(problem))
        self.assertNotEqual(target[0] * wrong.matrix[0][1], target[1] * wrong.matrix[1][0])

    def test_rational_weighted_bounded_kernel_and_null_states(self):
        problem = TableProblem([3, 3], [2, 2, 2], [[2, 1, 2], [2, 2, 2]])
        tables = list(ExactTableSampler(problem).tables())
        for activities in ([[1, Fraction(2, 3), 3], [2, 1, 5]], [[0, 1, 1], [1, 1, 1]]):
            kernel = heat_bath_kernel(problem, tables, simple_cycles(problem),
                                      weights=ProductWeights(activities, True))
            self.assert_stationary(kernel)

    def test_complete_fiber_is_required_and_caps_fail_before_allocation(self):
        problem = TableProblem([2, 2], [2, 2])
        tables = list(ExactTableSampler(problem).tables())
        with self.assertRaises(ValueError):
            heat_bath_kernel(problem, tables[:1], four_cycles(problem))
        with self.assertRaises(ValueError):
            heat_bath_kernel(problem, tables + tables[:1], four_cycles(problem))
        with self.assertRaises(ComputationBudgetExceeded):
            heat_bath_kernel(problem, tables, four_cycles(problem), max_kernel_states=2)
        with self.assertRaises(ValueError):
            heat_bath_kernel(problem, tables, four_cycles(problem), cycle_probabilities=[Fraction(1, 2)])
        with self.assertRaises(TypeError):
            heat_bath_kernel(problem, tables, four_cycles(problem), hold_probability=0.5)

    def test_invalid_cycles_are_rejected(self):
        problem = TableProblem([1, 1], [1, 1], structural_zeros=[(0, 0)])
        with self.assertRaises(ValueError):
            Cycle.from_nodes(problem, [0, 1], [0, 1])
        problem = TableProblem([1] * 4, [1] * 4)
        invalid = Cycle(((1, -1, 0, 0), (-1, 1, 0, 0), (0, 0, 1, -1), (0, 0, -1, 1)))
        with self.assertRaises(ValueError):
            invalid.validate(problem)
        with self.assertRaises(ValueError):
            Cycle.from_nodes(problem, [0, 0], [0, 1])

    def test_optional_spectral_diagnostic_on_exactly_known_cases(self):
        try:
            import numpy  # noqa: F401
        except ImportError:
            self.skipTest("NumPy is an optional diagnostic dependency")
        problem = TableProblem([1, 1, 1], [1, 1, 1], [[1, 1, 0], [0, 1, 1], [1, 0, 1]])
        tables = list(ExactTableSampler(problem).tables())
        self.assertAlmostEqual(heat_bath_kernel(problem, tables, ()).spectral_gap(), 0)
        self.assertAlmostEqual(heat_bath_kernel(problem, tables, simple_cycles(problem)).spectral_gap(), 1)
        self.assertAlmostEqual(heat_bath_kernel(problem, tables, simple_cycles(problem),
                                              hold_probability=Fraction(1, 2)).spectral_gap(), 0.5)


if __name__ == "__main__":
    unittest.main()
