from fractions import Fraction
from math import factorial
import unittest
from unittest.mock import patch

from contingency115.kernels import Cycle, ExactKernel, four_cycles, heat_bath_kernel, line_interval, simple_cycles
from contingency115.mixtures import fixed_mixture
from contingency115.tables import (ComputationBudgetExceeded, ExactTableSampler,
                                   ProductWeights, TableProblem, ZeroMassError)


def reachability_classes(matrix):
    """Independent Boolean transitive-closure oracle, including self reachability."""
    size = len(matrix)
    reachable = [[i == j or bool(matrix[i][j]) for j in range(size)] for i in range(size)]
    for middle in range(size):
        for source in range(size):
            for target in range(size):
                reachable[source][target] |= reachable[source][middle] and reachable[middle][target]
    remaining, result = set(range(size)), []
    while remaining:
        first = min(remaining)
        component = tuple(i for i in sorted(remaining) if reachable[first][i] and reachable[i][first])
        result.append(component)
        remaining.difference_update(component)
    return tuple(result)


def direct_heat_bath(states, cycles, weights=None, choices=None, hold=Fraction(0)):
    """Pairwise line-membership oracle; no production interval/shift/cache helpers."""
    masses = []
    for table in states:
        mass = Fraction(1)
        if weights is not None:
            for i, row in enumerate(table):
                for j, value in enumerate(row):
                    mass *= weights.activities[i][j] ** value
                    if weights.factorial_weight:
                        mass /= factorial(value)
        masses.append(mass)
    matrix = [[Fraction(0) for _ in states] for _ in states]
    if choices is None:
        choices = [Fraction(1, len(cycles)) for _ in cycles]
    for source, table in enumerate(states):
        matrix[source][source] = hold if cycles else Fraction(1)
        for cycle, choice in zip(cycles, choices):
            pivot = next((i, j) for i, row in enumerate(cycle.signs) for j, sign in enumerate(row) if sign)
            i, j = pivot
            targets = []
            for target, other in enumerate(states):
                amount = (other[i][j] - table[i][j]) * cycle.signs[i][j]
                if all(other[r][c] - table[r][c] == amount * sign
                       for r, row in enumerate(cycle.signs) for c, sign in enumerate(row)):
                    targets.append(target)
            line_mass = sum(masses[target] for target in targets)
            if line_mass:
                for target in targets:
                    matrix[source][target] += (1 - hold) * choice * masses[target] / line_mass
            else:
                matrix[source][source] += (1 - hold) * choice
    return tuple(tuple(row) for row in matrix), tuple(mass / sum(masses) for mass in masses)


class CommunicatingClassTests(unittest.TestCase):
    def test_all_512_directed_graphs_on_three_vertices(self):
        for bits in range(512):
            matrix = tuple(tuple(Fraction((bits >> (3 * i + j)) & 1) for j in range(3)) for i in range(3))
            kernel = ExactKernel(tuple(((i,),) for i in range(3)), matrix, (Fraction(1, 3),) * 3)
            self.assertEqual(kernel.communicating_classes(), reachability_classes(matrix), bits)

    def test_asymmetric_transient_and_zero_target_classes_keep_order(self):
        matrix = ((0, 1, 0, 0, 0, 0), (Fraction(1, 2), 0, Fraction(1, 2), 0, 0, 0),
                  (0, 0, 1, 0, 0, 0), (0, 0, 0, 0, 1, 0),
                  (0, 0, 0, 1, 0, 0), (0, 0, 1, 0, 0, 0))
        kernel = ExactKernel(tuple(((i,),) for i in range(6)), matrix, (0, 0, 1, 0, 0, 0))
        self.assertEqual(kernel.communicating_classes(), ((0, 1), (2,), (3, 4), (5,)))
        self.assertEqual(kernel.communicating_classes(), reachability_classes(matrix))

    def test_edges_use_exact_truth_values_and_empty_graph(self):
        tiny = Fraction(1, 10**400)
        kernel = ExactKernel((((0,),), ((1,),)), ((0, tiny), (-tiny, 0)), (1, 0))
        self.assertEqual(kernel.communicating_classes(), ((0, 1),))
        self.assertEqual(ExactKernel((), (), ()).communicating_classes(), ())

    def test_deep_cycle_does_not_depend_on_python_recursion_limit(self):
        size = 1100
        matrix = tuple(tuple(int(j == (i + 1) % size) for j in range(size)) for i in range(size))
        kernel = ExactKernel(tuple(((i,),) for i in range(size)), matrix, (Fraction(1, size),) * size)
        self.assertEqual(kernel.communicating_classes(), (tuple(range(size)),))


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

    def test_complete_matrices_against_independent_pairwise_line_oracle(self):
        fixtures = (
            TableProblem([3, 3], [2, 2, 2]),
            TableProblem([3, 3], [2, 2, 2], [[2, 1, 2], [2, 2, 2]],
                         lower_bounds=[[0, 0, 1], [0, 0, 0]]),
            TableProblem([1, 1, 1], [1, 1, 1]),
            TableProblem([1, 1, 1], [1, 1, 1], structural_zeros=[(0, 2), (1, 0), (2, 1)]),
        )
        for problem in fixtures:
            states = tuple(reversed(tuple(ExactTableSampler(problem).tables())))
            m, n = problem.shape
            activities = [[Fraction(i + j + 1, i + 2) for j in range(n)] for i in range(m)]
            null_activities = [[0 if (i, j) == (0, 0) else 1 for j in range(n)] for i in range(m)]
            catalog = simple_cycles(problem)
            for cycles in (catalog, catalog + catalog[:1], ()):
                choices = tuple(Fraction(i + 1, len(cycles) * (len(cycles) + 1) // 2)
                                for i in range(len(cycles)))
                for weights in (None, ProductWeights(activities), ProductWeights(activities, True),
                                ProductWeights(null_activities, True)):
                    for hold in (Fraction(0), Fraction(2, 7), Fraction(1)):
                        with self.subTest(shape=problem.shape, cycles=len(cycles), weights=weights, hold=hold):
                            actual = heat_bath_kernel(problem, states, cycles, weights=weights,
                                                      cycle_probabilities=choices, hold_probability=hold)
                            matrix, stationary = direct_heat_bath(states, cycles, weights, choices, hold)
                            self.assertEqual(actual.states, states)
                            self.assertEqual(actual.matrix, matrix)
                            self.assertEqual(actual.stationary, stationary)
                            self.assert_stationary(actual)
            reversed_cycles = tuple(Cycle(tuple(tuple(-x for x in row) for row in cycle.signs))
                                    for cycle in catalog)
            self.assertEqual(heat_bath_kernel(problem, states, catalog).matrix,
                             heat_bath_kernel(problem, states, reversed_cycles).matrix)

    def test_overlapping_lines_with_zero_mass_holds_and_zero_choice(self):
        problem = TableProblem([3, 3], [2, 2, 2])
        states = tuple(ExactTableSampler(problem).tables())
        cycles = four_cycles(problem)
        weights = ProductWeights([[0, 1, 1], [1, 1, 1]], True)
        choices, hold = (Fraction(2, 3), 0, Fraction(1, 3)), Fraction(1, 5)
        actual = heat_bath_kernel(problem, states, cycles, weights=weights,
                                  cycle_probabilities=choices, hold_probability=hold)
        expected, stationary = direct_heat_bath(states, cycles, weights, choices, hold)
        self.assertEqual(actual.matrix, expected)
        self.assertEqual(actual.stationary, stationary)
        # The last rectangle preserves x[0][0]; its null-state lines have zero
        # mass and must hold rather than choosing among their null targets.
        component = heat_bath_kernel(problem, states, cycles[-1:], weights=weights)
        for i, table in enumerate(states):
            if table[0][0]:
                self.assertEqual(component.matrix[i], tuple(Fraction(int(i == j)) for j in range(len(states))))
        components = tuple(heat_bath_kernel(problem, states, (cycle,), weights=weights,
                                            hold_probability=hold) for cycle in cycles)
        self.assertEqual(actual, fixed_mixture(components, choices))

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
        for caps in ({"max_states": 1}, {"max_transitions": 1}, {"max_kernel_states": 2}):
            with patch("contingency115.kernels._shift", side_effect=AssertionError("preprocessing started")):
                with self.assertRaises(ComputationBudgetExceeded):
                    heat_bath_kernel(problem, tables, four_cycles(problem), **caps)
        with self.assertRaises(ZeroMassError):
            heat_bath_kernel(problem, tables, four_cycles(problem), weights=ProductWeights([[0, 0], [0, 0]]))

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
