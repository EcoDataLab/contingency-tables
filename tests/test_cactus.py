from collections import Counter
from fractions import Fraction
from itertools import product
import random
import unittest

from contingency115.cactus import CactusTableSampler, CactusWeightedSampler, NotCactusError
from contingency115.kernels import simple_cycles
from contingency115.tables import (ComputationBudgetExceeded, ExactTableSampler,
                                   ExactWeightedTableSampler, InfeasibleTableError,
                                   ProductWeights, TableProblem, ZeroMassError)


def cycle_oracle(problem):
    m, n = problem.shape
    active = [[int(problem.upper_bounds[i][j] > problem.lower_bounds[i][j]) for j in range(n)] for i in range(m)]
    graph = TableProblem([n] * m, [m] * n, active)
    counts = Counter((i, j) for cycle in simple_cycles(graph)
                     for i, row in enumerate(cycle.signs) for j, value in enumerate(row) if value)
    return all(count <= 1 for count in counts.values())


def figure_eight(width=2, fixed_chord=0):
    return TableProblem([2 * width, width + fixed_chord, width],
                        [width, width, width + fixed_chord, width],
                        [[width] * 4, [width, width, fixed_chord, 0], [0, 0, width, width]],
                        [[0] * 4, [0, 0, fixed_chord, 0], [0] * 4])


class NoRandom:
    def randrange(self, stop):
        raise AssertionError("RNG must not be used")


class CountingWeights(ProductWeights):
    calls = 0

    def cell_weight(self, i, j, value):
        type(self).calls += 1
        return super().cell_weight(i, j, value)


class CactusTests(unittest.TestCase):
    def compare_dp(self, problem):
        cactus = CactusTableSampler(problem)
        oracle = ExactTableSampler(problem)
        self.assertEqual(cactus.count(), oracle.count())
        tables = list(cactus.tables())
        self.assertEqual(set(tables), set(oracle.tables()))
        for rank, table in enumerate(tables):
            problem.validate_table(table)
            self.assertEqual(cactus.rank(table), rank)
            self.assertEqual(cactus.from_coordinates(cactus.coordinates(table)), table)
        return cactus

    def test_all_binary_two_by_three_supports_and_attainable_margins(self):
        for allowed in product((0, 1), repeat=6):
            margins = set()
            for values in product(*(range(cap + 1) for cap in allowed)):
                rows = (sum(values[:3]), sum(values[3:]))
                columns = tuple(values[j] + values[3 + j] for j in range(3))
                margins.add((rows, columns))
            for rows, columns in margins:
                problem = TableProblem(rows, columns, (allowed[:3], allowed[3:]))
                if cycle_oracle(problem):
                    self.compare_dp(problem)
                else:
                    with self.assertRaises(NotCactusError):
                        CactusTableSampler(problem)

    def test_all_three_by_three_graphs_against_simple_cycle_oracle(self):
        for allowed in product((0, 1), repeat=9):
            upper = tuple(allowed[3 * i:3 * i + 3] for i in range(3))
            # Saturating each allowed cell keeps its effective cap positive.
            problem = TableProblem(tuple(map(sum, upper)),
                                   tuple(sum(upper[i][j] for i in range(3)) for j in range(3)), upper)
            if cycle_oracle(problem):
                sampler = CactusTableSampler(problem)
                self.assertEqual(sampler.count(), 1)
                self.assertEqual(sampler.sample(NoRandom()), upper)
            else:
                with self.assertRaises(NotCactusError):
                    CactusTableSampler(problem)

    def test_cycles_can_share_vertices_and_fixed_chords_are_removed(self):
        for chord in (0, 1, 17):
            sampler = self.compare_dp(figure_eight(fixed_chord=chord))
            self.assertEqual(len(sampler.cycles), 2)
            self.assertEqual(sampler.count(), 9)
            self.assertNotIn((1, 2), sampler.variable_edges)
            self.assertTrue(all(table[1][2] == chord for table in sampler.tables()))
        problem = figure_eight(fixed_chord=1)
        full_graph = TableProblem([4] * 3, [3] * 4,
                                  [[int(x > 0) for x in row] for row in problem.upper_bounds])
        self.assertGreater(len(simple_cycles(full_graph)), 2)

    def test_disconnected_cycles_bridges_and_positive_lower_bounds(self):
        problem = TableProblem([2, 2, 2, 2, 1], [3, 2, 2, 2],
                               [[2, 2, 0, 0], [2, 2, 0, 0], [0, 0, 2, 2], [0, 0, 2, 2], [1, 0, 0, 0]])
        sampler = self.compare_dp(problem)
        self.assertEqual(sampler.count(), 9)
        self.assertEqual(sampler.stats["bridge_edges"], 1)
        self.assertTrue(all(table[4][0] == 1 for table in sampler.tables()))
        self.compare_dp(TableProblem([6, 6], [6, 6], [[4, 4], [4, 4]], [[1, 2], [2, 1]]))

    def test_empty_zero_and_forest_fibers(self):
        for problem in (TableProblem([1, 0], [0, 0]),
                        TableProblem([1, 1], [1, 1], structural_zeros=[(0, 0), (0, 1)]),
                        TableProblem([1], [1], lower_bounds=[[1]], structural_zeros=[(0, 0)])):
            sampler = CactusTableSampler(problem)
            self.assertEqual(sampler.count(), 0)
            self.assertEqual(list(sampler.tables()), [])
            with self.assertRaises(InfeasibleTableError):
                sampler.sample(NoRandom())
        for problem in (TableProblem([0, 0], [0, 0, 0]), TableProblem([2, 3], [5])):
            sampler = self.compare_dp(problem)
            self.assertEqual(sampler.count(), 1)
            self.assertEqual(sampler.sample(NoRandom()), sampler.unrank(0))

    def test_binary_encoded_huge_width_uses_mixed_radix(self):
        width = 2**200 + 17
        sampler = CactusTableSampler(figure_eight(width))
        self.assertEqual(sampler.count(), (width + 1)**2)
        for rank in (0, 1, width, width + 1, sampler.count() // 2, sampler.count() - 1):
            self.assertEqual(sampler.rank(sampler.unrank(rank)), rank)
        with self.assertRaises(ComputationBudgetExceeded):
            sampler.tables(max_tables=100)
        class Endpoint:
            def randrange(self, stop):
                self.stop = stop
                return stop - 1
        rng = Endpoint()
        self.assertEqual(sampler.sample(rng), sampler.unrank(sampler.count() - 1))
        self.assertEqual(rng.stop, sampler.count())

    def test_rank_parameters_and_structural_budgets(self):
        sampler = CactusTableSampler(figure_eight())
        for value in (-1, True, 0.5):
            with self.assertRaises((ValueError, TypeError)):
                sampler.unrank(value)
        with self.assertRaises(IndexError):
            sampler.unrank(9)
        for values in ((0,), (0, 100), (False, 0)):
            with self.assertRaises((TypeError, ValueError)):
                sampler.from_coordinates(values)
        with self.assertRaises(ComputationBudgetExceeded):
            CactusTableSampler(figure_eight(), max_cells=11)
        with self.assertRaises(ComputationBudgetExceeded):
            CactusTableSampler(figure_eight(), max_cycle_edges=7)
        with self.assertRaises(ValueError):
            CactusTableSampler(figure_eight(), max_cycle_edges=0)

    def test_weighted_factorization_against_seeded_dp(self):
        rng = random.Random(115_2026_10_09)
        tested = 0
        while tested < 80:
            upper = [[rng.randrange(4) for _ in range(3)] for _ in range(3)]
            lower = [[rng.randrange(cap + 1) for cap in row] for row in upper]
            witness = [[rng.randint(lower[i][j], upper[i][j]) for j in range(3)] for i in range(3)]
            problem = TableProblem(tuple(map(sum, witness)), tuple(sum(row[j] for row in witness) for j in range(3)), upper, lower)
            if not cycle_oracle(problem):
                continue
            self.compare_dp(problem)
            activities = [[Fraction(rng.randrange(4), rng.randrange(1, 4)) for _ in range(3)] for _ in range(3)]
            for factorial in (False, True):
                weights = ProductWeights(activities, factorial)
                sampler = CactusWeightedSampler(problem, weights)
                oracle = ExactWeightedTableSampler(problem, weights)
                self.assertEqual(sampler.normalizer(), oracle.normalizer())
                if oracle.normalizer():
                    tables = tuple(ExactTableSampler(problem).tables())
                    self.assertEqual(sampler.support_count(), sum(weights.table_weight(table) > 0 for table in tables))
                    for table in tables:
                        self.assertEqual(sampler.probability(table), oracle.probability(table))
                    stored = sampler.normalizer().numerator.bit_length() + sampler.normalizer().denominator.bit_length()
                    for line in sampler.lines:
                        stored += sum(mass.numerator.bit_length() + mass.denominator.bit_length() for mass in line.masses)
                        stored += line.total.numerator.bit_length() + line.total.denominator.bit_length()
                        stored += sum(value.bit_length() for value in line.cumulative)
                    self.assertLessEqual(stored, sampler.plan.stored_coefficient_bits_bound)
                else:
                    with self.assertRaises(ZeroMassError):
                        sampler.sample(NoRandom())
            tested += 1

    def test_weighted_random_choice_tree_is_exact(self):
        problem = figure_eight()
        weights = ProductWeights([[1] * 4 for _ in range(3)], True)
        sampler = CactusWeightedSampler(problem, weights)
        frequencies = Counter()
        class Tape:
            def __init__(self, values):
                self.values = iter(values)
            def randrange(self, stop):
                self_stop = 6
                if stop != self_stop:
                    raise AssertionError((stop, self_stop))
                return next(self.values)
        for first, second in product(range(6), repeat=2):
            frequencies[sampler.sample(Tape((first, second)))] += 1
        for table, count in frequencies.items():
            self.assertEqual(Fraction(count, 36), sampler.probability(table))

    def test_storage_plan_with_large_rational_activity_coefficients(self):
        problem = figure_eight(fixed_chord=1)
        large = Fraction(2**201 + 1, 2**199 + 3)
        activities = [[large, Fraction(3, 11), 2, 1], [5, large, large, 1], [1, 1, Fraction(7, 13), large]]
        for factorial in (False, True):
            weights = ProductWeights(activities, factorial)
            sampler = CactusWeightedSampler(problem, weights)
            oracle = ExactWeightedTableSampler(problem, weights)
            self.assertEqual(sampler.normalizer(), oracle.normalizer())
            stored = sampler.normalizer().numerator.bit_length() + sampler.normalizer().denominator.bit_length()
            for line in sampler.lines:
                stored += sum(mass.numerator.bit_length() + mass.denominator.bit_length() for mass in line.masses)
                stored += line.total.numerator.bit_length() + line.total.denominator.bit_length()
                stored += sum(value.bit_length() for value in line.cumulative)
            self.assertLessEqual(stored, sampler.plan.stored_coefficient_bits_bound)

    def test_zero_activities_restrict_intervals_before_planning(self):
        problem = TableProblem([2, 2], [2, 2])
        sampler = CactusWeightedSampler(problem, ProductWeights([[0, 1], [1, 0]], True), max_line_states=1)
        self.assertEqual(sampler.plan.line_states, 1)
        self.assertEqual(sampler.normalizer(), Fraction(1, 4))
        self.assertEqual(sampler.support_count(), 1)
        self.assertEqual(sampler.sample(NoRandom()), ((0, 2), (2, 0)))
        self.assertEqual(sampler.probability(((1, 1), (1, 1))), 0)
        zero = CactusWeightedSampler(problem, ProductWeights([[0, 0], [1, 1]]))
        self.assertEqual(zero.normalizer(), 0)
        with self.assertRaises(ZeroMassError):
            zero.sample(NoRandom())
        fixed = CactusWeightedSampler(TableProblem([2], [2]), ProductWeights([[0]]))
        self.assertEqual(fixed.normalizer(), 0)

    def test_weight_planner_rejects_before_weight_arithmetic_or_rng(self):
        problem = figure_eight()
        for limits in ({"max_line_states": 1}, {"max_cell_value": 1},
                       {"max_weight_evaluations": 1}, {"max_stored_weight_bits": 1}):
            CountingWeights.calls = 0
            with self.assertRaises(ComputationBudgetExceeded):
                CactusWeightedSampler(problem, CountingWeights([[1] * 4 for _ in range(3)], True), **limits).sample(NoRandom())
            self.assertEqual(CountingWeights.calls, 0)
        CountingWeights.calls = 0
        with self.assertRaises(ComputationBudgetExceeded):
            CactusWeightedSampler(figure_eight(2**200), CountingWeights([[1] * 4 for _ in range(3)], True)).sample(NoRandom())
        self.assertEqual(CountingWeights.calls, 0)

    def test_weighted_empty_and_validation(self):
        empty = CactusWeightedSampler(TableProblem([1], [0]), ProductWeights([[1]]))
        self.assertEqual(empty.normalizer(), 0)
        with self.assertRaises(InfeasibleTableError):
            empty.sample(NoRandom())
        with self.assertRaises(ValueError):
            CactusWeightedSampler(figure_eight(), ProductWeights([[1]]))
        with self.assertRaises(TypeError):
            CactusWeightedSampler(figure_eight(), ProductWeights([[1] * 4 for _ in range(3)]), max_line_states=True)


if __name__ == "__main__":
    unittest.main()
