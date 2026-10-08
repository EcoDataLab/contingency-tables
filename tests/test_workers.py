"""Independent exact-law and operational checks for the ordinary urn sampler."""

from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import factorial
import random
import unittest

from contingency115.tables import (ComputationBudgetExceeded, InfeasibleTableError,
                                  TableProblem)
from contingency115.workers import OrdinaryWorkerSampler, worker_linear_moments


class ForbiddenRNG:
    def randrange(self, stop):
        raise AssertionError("this path must not consume randomness")


def expanded_rng_law(rows, columns):
    """Replay every branch of the implemented uniform-integer RNG tree."""
    class Request(Exception):
        def __init__(self, stop):
            self.stop = stop

    class Replay:
        def __init__(self, path):
            self.path = iter(path)

        def randrange(self, stop):
            try:
                rank = next(self.path)
            except StopIteration:
                raise Request(stop)
            if not 0 <= rank < stop:
                raise AssertionError("invalid replay rank")
            return rank

    sampler = OrdinaryWorkerSampler(rows, columns)
    law = defaultdict(Fraction)
    stack = [((), Fraction(1))]
    while stack:
        path, probability = stack.pop()
        try:
            draw = sampler.sample_with_stats(Replay(path))
        except Request as request:
            stack.extend((path + (rank,), probability / request.stop)
                         for rank in range(request.stop))
        else:
            if draw.random_draws > sampler.plan.maximum_random_draws:
                raise AssertionError("draw count exceeds preflight bound")
            if draw.random_draws + draw.deterministically_assigned_workers != sum(rows):
                raise AssertionError("worker accounting failed")
            law[draw.table] += probability
    return dict(law)


def independent_table_law(rows, columns):
    """Enumerate cell boxes independently and normalize reciprocal factorials."""
    m, n = len(rows), len(columns)
    weights = {}
    ranges = [range(min(rows[i], columns[j]) + 1) for i in range(m) for j in range(n)]
    for flat in product(*ranges):
        table = tuple(tuple(flat[i * n:(i + 1) * n]) for i in range(m))
        if tuple(map(sum, table)) != tuple(rows):
            continue
        if tuple(sum(table[i][j] for i in range(m)) for j in range(n)) != tuple(columns):
            continue
        denominator = 1
        for value in flat:
            denominator *= factorial(value)
        weights[table] = Fraction(1, denominator)
    total = sum(weights.values())
    return {table: weight / total for table, weight in weights.items()}


def compositions(total, length):
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, length - 1):
            yield (first, *rest)


class WorkerExactLawTests(unittest.TestCase):
    def test_every_two_by_three_margin_pair_up_to_four_workers(self):
        for total in range(5):
            for rows in compositions(total, 2):
                for columns in compositions(total, 3):
                    with self.subTest(rows=rows, columns=columns):
                        law = expanded_rng_law(rows, columns)
                        self.assertEqual(sum(law.values()), 1)
                        self.assertEqual(law, independent_table_law(rows, columns))

    def test_every_three_by_two_margin_pair_up_to_four_workers(self):
        for total in range(5):
            for rows in compositions(total, 3):
                for columns in compositions(total, 2):
                    with self.subTest(rows=rows, columns=columns):
                        self.assertEqual(expanded_rng_law(rows, columns),
                                         independent_table_law(rows, columns))

    def test_three_by_three_multistage_decision_tree(self):
        for rows, columns in [((1, 1, 2), (1, 2, 1)),
                              ((2, 2, 1), (2, 1, 2)),
                              ((2, 0, 3), (0, 2, 3))]:
            self.assertEqual(expanded_rng_law(rows, columns),
                             independent_table_law(rows, columns))

    def test_worker_law_is_not_uniform_table_law(self):
        law = expanded_rng_law((2, 2), (2, 2))
        self.assertEqual({table[0][0]: mass for table, mass in law.items()},
                         {0: Fraction(1, 6), 1: Fraction(2, 3), 2: Fraction(1, 6)})


class WorkerValidationTests(unittest.TestCase):
    def test_malformed_margins_and_budgets(self):
        for rows, columns in [([], [0]), ([0], []), ([True], [1]),
                              ([1.0], [1]), ([-1], [-1]), ([1], [False])]:
            with self.assertRaises((TypeError, ValueError)):
                OrdinaryWorkerSampler(rows, columns)
        with self.assertRaises(InfeasibleTableError):
            OrdinaryWorkerSampler([2], [1])
        for name in ("max_draws", "max_cells"):
            for value in (-1, True, 1.0, None):
                with self.assertRaises((ValueError, TypeError)):
                    OrdinaryWorkerSampler([1], [1], **{name: value})

    def test_bounds_activities_and_problem_objects_are_not_accepted(self):
        problem = TableProblem([1, 1], [1, 1], [[1, 0], [0, 1]])
        with self.assertRaises(TypeError):
            OrdinaryWorkerSampler(problem, [1, 1])
        for name in ("upper_bounds", "lower_bounds", "structural_zeros", "activities"):
            with self.assertRaises(TypeError):
                OrdinaryWorkerSampler([1, 1], [1, 1], **{name: [[1, 1], [1, 1]]})

    def test_budget_rejection_precedes_rng_and_dense_output_allocation(self):
        with self.assertRaises(ComputationBudgetExceeded):
            OrdinaryWorkerSampler([2**80, 2**80], [2**80, 2**80], max_draws=5).sample(ForbiddenRNG())
        with self.assertRaises(ComputationBudgetExceeded):
            OrdinaryWorkerSampler([0] * 1000, [0] * 1000, max_cells=1).sample(ForbiddenRNG())
        # This plan could use fewer draws on favorable branches, but it is
        # rejected in advance rather than selecting only those branches.
        with self.assertRaises(ComputationBudgetExceeded):
            OrdinaryWorkerSampler([4, 4], [7, 1], max_draws=3).sample(ForbiddenRNG())

    def test_deterministic_large_counts_and_zero_margins(self):
        count = 2**120
        cases = [([0, 0], [0, 0, 0], ((0, 0, 0), (0, 0, 0))),
                 ([0, count, 0], [1, 0, count - 1], ((0, 0, 0), (1, 0, count - 1), (0, 0, 0))),
                 ([count, 0, 7], [0, count + 7, 0], ((0, count, 0), (0, 0, 0), (0, 7, 0)))]
        for rows, columns, expected in cases:
            sampler = OrdinaryWorkerSampler(rows, columns, max_draws=0)
            draw = sampler.sample_with_stats(ForbiddenRNG())
            self.assertEqual(draw.table, expected)
            self.assertEqual(draw.random_draws, 0)
            self.assertEqual(draw.deterministically_assigned_workers, sum(rows))

    def test_largest_row_saved_and_remaining_category_shortcut(self):
        class FirstRank:
            def randrange(self, stop):
                return 0

        sampler = OrdinaryWorkerSampler([10, 0, 3], [1, 12], max_draws=3)
        self.assertEqual(sampler.plan.final_row, 0)
        self.assertEqual(sampler.plan.maximum_random_draws, 3)
        draw = sampler.sample_with_stats(FirstRank())
        self.assertEqual(draw.table, ((0, 10), (0, 0), (1, 2)))
        self.assertEqual(draw.random_draws, 1)
        self.assertEqual(draw.deterministically_assigned_workers, 12)

    def test_inputs_copied_and_samples_have_no_shared_mutable_state(self):
        rows, columns = [2, 3], [1, 2, 2]
        sampler = OrdinaryWorkerSampler(rows, columns)
        rows[0], columns[0] = 100, 100
        first = sampler.sample(random.Random(115))
        second = sampler.sample(random.Random(115))
        self.assertEqual(first, second)
        self.assertEqual(tuple(map(sum, first)), (2, 3))
        self.assertEqual(tuple(map(sum, zip(*first))), (1, 2, 2))

    def test_invalid_rng_results_raise(self):
        class Invalid:
            def __init__(self, value):
                self.value = value

            def randrange(self, stop):
                return self.value(stop) if callable(self.value) else self.value

        sampler = OrdinaryWorkerSampler([1, 1], [1, 1])
        for value in (-1, 0.5, True, lambda stop: stop):
            with self.assertRaises((TypeError, ValueError)):
                sampler.sample(Invalid(value))

    def test_moderate_count_case_needs_no_completion_dp(self):
        rows = [1000] * 100
        columns = [40000, 20000, 20000, 10000, 10000]
        sampler = OrdinaryWorkerSampler(rows, columns, max_draws=99_000)
        draw = sampler.sample_with_stats(random.Random(115))
        self.assertEqual(tuple(map(sum, draw.table)), tuple(rows))
        self.assertEqual(tuple(map(sum, zip(*draw.table))), tuple(columns))
        self.assertLessEqual(draw.random_draws, 99_000)
        self.assertLessEqual(draw.fenwick_steps, 5 + 7 * 99_000)


class WorkerMomentTests(unittest.TestCase):
    def test_general_signed_rational_moments_match_independent_enumeration(self):
        rng = random.Random(11526)
        for total in range(5):
            for rows in compositions(total, 2):
                for columns in compositions(total, 3):
                    coefficients = [[Fraction(rng.randrange(-5, 6), rng.randrange(1, 5))
                                     for _ in columns] for _ in rows]
                    law = independent_table_law(rows, columns)
                    values = {table: sum(coefficients[i][j] * table[i][j]
                                         for i in range(2) for j in range(3))
                              for table in law}
                    mean = sum(law[table] * value for table, value in values.items())
                    variance = sum(law[table] * (value - mean)**2 for table, value in values.items())
                    result = worker_linear_moments(rows, columns, coefficients)
                    self.assertEqual((result.mean, result.variance), (mean, variance))

    def test_huge_binary_margins_need_no_worker_loop(self):
        count = 2**200
        result = worker_linear_moments([count, count], [count, count], [[1, 0], [0, 0]])
        self.assertEqual(result.mean, Fraction(count, 2))
        self.assertEqual(result.variance, Fraction(count**2, 4 * (2 * count - 1)))

    def test_additive_row_column_observable_has_zero_variance(self):
        rows, columns = [3, 6, 1], [2, 3, 5]
        row_values, column_values = [4, -2, 7], [3, 8, -6]
        coefficients = [[a + b for b in column_values] for a in row_values]
        result = worker_linear_moments(rows, columns, coefficients)
        expected = sum(r * a for r, a in zip(rows, row_values)) + sum(c * b for c, b in zip(columns, column_values))
        self.assertEqual(result.mean, expected)
        self.assertEqual(result.variance, 0)

    def test_rejects_incompatible_shape_floats_and_work_budget(self):
        for coefficients in ([[1]], [[1, 0], [0]], [[True, 0], [0, 1]], [[1.0, 0], [0, 1]]):
            with self.assertRaises((ValueError, TypeError)):
                worker_linear_moments([1, 1], [1, 1], coefficients)
        with self.assertRaises(ComputationBudgetExceeded):
            worker_linear_moments([1, 1], [1, 1], [[1, 0], [0, 1]], max_cells=3)
        with self.assertRaises(InfeasibleTableError):
            worker_linear_moments([1], [2], [[1]])


if __name__ == "__main__":
    unittest.main()
