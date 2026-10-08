"""Independent finite oracles; no frequency-test evidence is needed for exactness."""

from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import factorial
import random
import unittest

from contingency115.tables import (ComputationBudgetExceeded, ExactTableSampler,
                                  ExactWeightedTableSampler, InfeasibleTableError,
                                  ProductWeights, TableProblem, ZeroMassError)


def brute_tables(problem):
    m, n = problem.shape
    result = []
    ranges = [range(problem.lower_bounds[i][j], problem.upper_bounds[i][j] + 1)
              for i in range(m) for j in range(n)]
    for flat in product(*ranges):
        table = tuple(tuple(flat[i * n:(i + 1) * n]) for i in range(m))
        if tuple(map(sum, table)) == problem.row_sums and tuple(
            sum(table[i][j] for i in range(m)) for j in range(n)
        ) == problem.column_sums:
            result.append(table)
    return result


class PrescribedRank:
    def __init__(self, rank, expected_stop):
        self.rank, self.expected_stop, self.calls = rank, expected_stop, 0

    def randrange(self, stop):
        if stop != self.expected_stop:
            raise AssertionError((stop, self.expected_stop))
        self.calls += 1
        return self.rank


class ForbiddenRNG:
    def randrange(self, stop):
        raise AssertionError("no random draw is allowed before the exact calculation succeeds")


def exhaustive_random_law(sample):
    """Expand an algorithm's discrete RNG tree, with exact path probabilities."""
    class Request(Exception):
        def __init__(self, stop):
            self.stop = stop

    class Replay:
        def __init__(self, values):
            self.values = iter(values)

        def randrange(self, stop):
            try:
                value = next(self.values)
            except StopIteration:
                raise Request(stop)
            if not 0 <= value < stop:
                raise AssertionError("invalid replay")
            return value

    law = defaultdict(Fraction)
    paths = [((), Fraction(1))]
    while paths:
        values, probability = paths.pop()
        try:
            table = sample(Replay(values))
        except Request as request:
            if request.stop > 1000:
                raise AssertionError("test RNG tree unexpectedly large")
            paths.extend((values + (i,), probability / request.stop) for i in range(request.stop))
        else:
            law[table] += probability
    return dict(law)


class TableValidationTests(unittest.TestCase):
    def test_reject_malformed_data(self):
        for rows, columns in [([], [0]), ([0], []), ([True], [1]), ([1.0], [1]), ([-1], [-1])]:
            with self.assertRaises((ValueError, TypeError)):
                TableProblem(rows, columns)
        with self.assertRaises(ValueError):
            TableProblem([1, 1], [1, 1], [[1, 1]])
        with self.assertRaises(ValueError):
            TableProblem([1], [1], [[0]], [[1]])
        with self.assertRaises(ValueError):
            TableProblem([1], [1], structural_zeros=[(0, 1)])
        with self.assertRaises(TypeError):
            ProductWeights([[0.5]])
        with self.assertRaises(ValueError):
            ProductWeights([[Fraction(-1, 2)]])

    def test_constraints_are_copied_and_upper_bounds_tightened(self):
        rows, columns, upper = [1, 2], [2, 1], [[8, 7], [6, 5]]
        problem = TableProblem(rows, columns, upper)
        rows[0], columns[0], upper[0][0] = 100, 100, 100
        self.assertEqual(problem.row_sums, (1, 2))
        self.assertEqual(problem.upper_bounds, ((1, 1), (2, 1)))
        witness = problem.feasibility()
        self.assertTrue(witness.feasible)
        self.assertEqual(problem.validate_table(witness.table), witness.table)
        self.assertEqual(problem.transpose().transpose(), problem)

    def test_feasibility_detects_sparse_hall_obstruction(self):
        problem = TableProblem([1, 1, 1], [1, 1, 1], [[1, 0, 0], [1, 0, 0], [0, 1, 1]])
        self.assertTrue(all(sum(row) >= 1 for row in problem.upper_bounds))
        self.assertTrue(all(sum(problem.upper_bounds[i][j] for i in range(3)) >= 1 for j in range(3)))
        self.assertFalse(problem.feasibility().feasible)
        self.assertEqual(ExactTableSampler(problem).count(), 0)
        with self.assertRaises(InfeasibleTableError):
            ExactTableSampler(problem).sample(ForbiddenRNG())

    def test_empty_fibers_and_structural_zero_lower_conflict(self):
        problems = [TableProblem([1], [0]), TableProblem([1], [1], [[0]]),
                    TableProblem([1, 1], [1, 1], lower_bounds=[[1, 1], [0, 0]]),
                    TableProblem([1], [1], lower_bounds=[[1]], structural_zeros=[(0, 0)])]
        for problem in problems:
            self.assertFalse(problem.feasibility().feasible)
            self.assertEqual(ExactTableSampler(problem).count(), 0)
            self.assertEqual(list(ExactTableSampler(problem).tables()), [])
            self.assertFalse(problem.transpose().feasibility().feasible)

    def test_zero_margins_and_one_row(self):
        zero = TableProblem([0, 0], [0, 0, 0])
        self.assertEqual(ExactTableSampler(zero).sample(), ((0, 0, 0), (0, 0, 0)))
        large = TableProblem([2**90 + 2], [2**90, 0, 2])
        sampler = ExactTableSampler(large)
        self.assertEqual(sampler.count(), 1)
        self.assertEqual(sampler.sample(), ((2**90, 0, 2),))


class CompletionCountTests(unittest.TestCase):
    def assert_oracle(self, problem):
        expected = brute_tables(problem)
        sampler = ExactTableSampler(problem)
        self.assertEqual(sampler.count(), len(expected))
        self.assertEqual(list(sampler.tables()), expected)
        self.assertEqual(problem.feasibility().feasible, bool(expected))
        for rank, table in enumerate(expected):
            self.assertEqual(sampler.rank(table), rank)
            self.assertEqual(sampler.unrank(rank), table)
            rng = PrescribedRank(rank, len(expected))
            self.assertEqual(sampler.sample(rng), table)
            self.assertEqual(rng.calls, 1)

    def test_all_binary_two_by_three_supports_and_attainable_margins(self):
        # Independent cell enumeration groups every binary table by its margins.
        # This includes every structural-zero pattern and every nonempty fiber
        # inside each pattern, including deterministic and disconnected fibers.
        for caps in product(range(2), repeat=6):
            margins = set()
            for flat in product(*(range(cap + 1) for cap in caps)):
                rows = (sum(flat[:3]), sum(flat[3:]))
                columns = tuple(flat[j] + flat[3 + j] for j in range(3))
                margins.add((rows, columns))
            upper = (caps[:3], caps[3:])
            for rows, columns in margins:
                with self.subTest(caps=caps, rows=rows, columns=columns):
                    self.assert_oracle(TableProblem(rows, columns, upper))

    def test_random_small_lower_and_upper_bound_oracles(self):
        rng = random.Random(115)
        for _ in range(120):
            lower = [[rng.randrange(2) for _ in range(3)] for _ in range(2)]
            upper = [[lower[i][j] + rng.randrange(3) for j in range(3)] for i in range(2)]
            table = [[rng.randrange(lower[i][j], upper[i][j] + 1) for j in range(3)] for i in range(2)]
            rows = list(map(sum, table))
            columns = [sum(table[i][j] for i in range(2)) for j in range(3)]
            if rng.randrange(3) == 0:
                columns[0] += 1  # Includes empty fibers, without conditioning on feasibility.
            self.assert_oracle(TableProblem(rows, columns, upper, lower))

    def test_three_row_lower_bounded_oracles(self):
        rng = random.Random(11503)
        for _ in range(50):
            lower = [[rng.randrange(2) for _ in range(3)] for _ in range(3)]
            upper = [[lower[i][j] + rng.randrange(2) for j in range(3)] for i in range(3)]
            table = [[rng.randrange(lower[i][j], upper[i][j] + 1) for j in range(3)] for i in range(3)]
            rows = list(map(sum, table))
            columns = [sum(table[i][j] for i in range(3)) for j in range(3)]
            self.assert_oracle(TableProblem(rows, columns, upper, lower))

    def test_rank_validation_and_enumeration_output_cap(self):
        sampler = ExactTableSampler(TableProblem([2, 2], [2, 2]))
        for rank in (-1, 3, 100):
            with self.assertRaises((ValueError, IndexError)):
                sampler.unrank(rank)
        with self.assertRaises(TypeError):
            sampler.unrank(True)
        with self.assertRaises(ValueError):
            sampler.rank([[1, 1], [2, 0]])
        with self.assertRaises(ComputationBudgetExceeded):
            sampler.tables(max_tables=2)
        self.assertEqual(sampler.count(), 3)  # Output cap does not invalidate the DP.

    def test_resource_exhaustion_never_returns_partial_count_or_draw(self):
        problem = TableProblem([10, 10], [10, 10])
        for options in ({"max_states": 1}, {"max_transitions": 1}):
            sampler = ExactTableSampler(problem, **options)
            for operation in (sampler.count, lambda: sampler.sample(ForbiddenRNG()), sampler.count):
                with self.assertRaises(ComputationBudgetExceeded):
                    operation()
            self.assertFalse(sampler.stats["complete"])
        # Binary encoding alone does not make this numeric-margin DP efficient.
        large = ExactTableSampler(TableProblem([2**80, 2**80], [2**80, 2**80]), max_transitions=5)
        with self.assertRaises(ComputationBudgetExceeded):
            large.count()
        self.assertEqual(large.stats["transitions_visited"], 5)


class WeightedLawTests(unittest.TestCase):
    def test_worker_and_table_laws_are_different(self):
        problem = TableProblem([2, 2], [2, 2])
        tables = list(ExactTableSampler(problem).tables())
        uniform = ExactWeightedTableSampler(problem, ProductWeights([[1, 1], [1, 1]]))
        worker = ExactWeightedTableSampler(problem, ProductWeights([[1, 1], [1, 1]], factorial_weight=True))
        self.assertEqual([uniform.probability(table) for table in tables], [Fraction(1, 3)] * 3)
        expected = [Fraction(1, 6), Fraction(2, 3), Fraction(1, 6)]
        self.assertEqual([worker.probability(table) for table in tables], expected)
        self.assertEqual(worker.normalizer(), Fraction(3, 2))
        self.assertEqual(exhaustive_random_law(worker.sample), dict(zip(tables, expected)))

    def test_exact_rational_sampling_tree_matches_independent_weight_oracle(self):
        problem = TableProblem([2, 2], [2, 2])
        activities = [[1, Fraction(1, 2)], [1, 1]]
        sampler = ExactWeightedTableSampler(problem, ProductWeights(activities, True))
        tables = brute_tables(problem)
        weights = []
        for table in tables:
            value = Fraction(1)
            for i in range(2):
                for j in range(2):
                    value *= Fraction(activities[i][j]) ** table[i][j] / factorial(table[i][j])
            weights.append(value)
        normalizer = sum(weights)
        self.assertEqual(sampler.normalizer(), normalizer)
        expected = {table: weight / normalizer for table, weight in zip(tables, weights)}
        self.assertEqual(exhaustive_random_law(sampler.sample), expected)
        self.assertEqual([expected[table] for table in tables], [Fraction(1, 13), Fraction(8, 13), Fraction(4, 13)])

    def test_row_and_column_activity_gauge_invariance(self):
        problem = TableProblem([2, 3], [2, 1, 2])
        activities = [[1, 2, 3], [4, 5, 6]]
        alpha, beta = [Fraction(2, 3), 5], [7, Fraction(3, 2), 11]
        scaled = [[activities[i][j] * alpha[i] * beta[j] for j in range(3)] for i in range(2)]
        for factorial_weight in (False, True):
            first = ExactWeightedTableSampler(problem, ProductWeights(activities, factorial_weight))
            second = ExactWeightedTableSampler(problem, ProductWeights(scaled, factorial_weight))
            for table in brute_tables(problem):
                self.assertEqual(first.probability(table), second.probability(table))

    def test_multistage_weighted_rng_tree_and_three_row_partition(self):
        problem = TableProblem([2, 2, 2], [3, 3])
        weights = ProductWeights([[1, 1]] * 3, True)
        sampler = ExactWeightedTableSampler(problem, weights)
        tables = brute_tables(problem)
        oracle_weights = [Fraction(1, factorial(table[0][0]) * factorial(table[0][1])
                                    * factorial(table[1][0]) * factorial(table[1][1])
                                    * factorial(table[2][0]) * factorial(table[2][1])) for table in tables]
        normalizer = sum(oracle_weights)
        self.assertEqual(normalizer, Fraction(5, 2))
        self.assertEqual(sampler.normalizer(), normalizer)
        self.assertEqual(exhaustive_random_law(sampler.sample),
                         {table: mass / normalizer for table, mass in zip(tables, oracle_weights)})

    def test_zero_activities_and_empty_target(self):
        problem = TableProblem([2, 2], [2, 2])
        weighted = ExactWeightedTableSampler(problem, ProductWeights([[0, 1], [1, 1]], True))
        expected = ((0, 2), (2, 0))
        self.assertEqual(weighted.sample(random.Random(115)), expected)
        self.assertEqual(weighted.probability(expected), 1)
        self.assertEqual(weighted.probability(((1, 1), (1, 1))), 0)
        zero = ExactWeightedTableSampler(problem, ProductWeights([[0, 0], [1, 1]], True))
        self.assertEqual(zero.normalizer(), 0)
        with self.assertRaises(ZeroMassError):
            zero.sample(ForbiddenRNG())
        infeasible = ExactWeightedTableSampler(TableProblem([1], [2]), ProductWeights([[1]]))
        with self.assertRaises(InfeasibleTableError):
            infeasible.sample(ForbiddenRNG())

    def test_weighted_budgets_and_transpose(self):
        problem = TableProblem([2, 3], [2, 1, 2])
        weights = ProductWeights([[1, 2, 3], [4, 5, 6]], True)
        self.assertEqual(ExactWeightedTableSampler(problem, weights).normalizer(),
                         ExactWeightedTableSampler(problem.transpose(), weights.transpose()).normalizer())
        with self.assertRaises(ComputationBudgetExceeded):
            ExactWeightedTableSampler(problem, weights, max_states=1).sample(ForbiddenRNG())


if __name__ == "__main__":
    unittest.main()
