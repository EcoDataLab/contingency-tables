"""A shared line-state cap must permit later zero-line-state factors."""

from fractions import Fraction
from itertools import product
import unittest
from unittest.mock import patch

from contingency115.block_sampler import BlockSamplerBudget, BlockWeightedSampler
from contingency115.cactus import CactusWeightedSampler
from contingency115.tables import (
    ComputationBudgetExceeded, ProductWeights, TableProblem, ZeroMassError,
)


class NoRandom:
    def randrange(self, stop):
        raise AssertionError("budget exhaustion must precede sampling")


def two_factor_problem(reverse=False):
    rows, columns = (1, 1, 1, 2), (2, 1, 1, 1)
    upper = ((1, 1, 0, 0), (1, 1, 0, 0),
             (1, 0, 1, 1), (0, 0, 1, 1))
    lower = ((0, 0, 0, 0), (0, 0, 0, 0),
             (1, 0, 0, 0), (0, 0, 0, 0))
    # Relabel both axes to put the zero-line-state block first.
    order = (2, 3, 0, 1) if reverse else (0, 1, 2, 3)
    return TableProblem(
        tuple(rows[i] for i in order), tuple(columns[j] for j in order),
        tuple(tuple(upper[i][j] for j in order) for i in order),
        tuple(tuple(lower[i][j] for j in order) for i in order))


def independent_tables(problem):
    ranges = [range(lo, hi + 1) for low_row, high_row in
              zip(problem.lower_bounds, problem.upper_bounds)
              for lo, hi in zip(low_row, high_row)]
    tables = []
    for flat in product(*ranges):
        table = tuple(tuple(flat[4*i:4*i+4]) for i in range(4))
        if (tuple(map(sum, table)) == problem.row_sums
                and tuple(map(sum, zip(*table))) == problem.column_sums):
            tables.append(table)
    return tables


class ZeroLineStateBudgetTests(unittest.TestCase):
    def test_shared_cap_allows_zero_state_factor_in_either_order(self):
        for reverse in (False, True):
            problem = two_factor_problem(reverse)
            expected = independent_tables(problem)
            self.assertEqual(len(expected), 2)
            weights = ProductWeights(((1,) * 4,) * 4)
            sampler = BlockWeightedSampler(
                problem, weights,
                budget=BlockSamplerBudget(max_cycle_line_states_total=2))
            self.assertEqual(sampler.normalizer(), Fraction(2))
            self.assertEqual(sampler.stats["prepared_factors"], 2)
            self.assertEqual(sampler.stats["cycle_line_states"], 2)
            for table in expected:
                self.assertEqual(sampler.probability(table), Fraction(1, 2))

    def test_zero_cactus_cap_accepts_forest(self):
        problem = TableProblem((0, 2), (1, 1))
        sampler = CactusWeightedSampler(
            problem, ProductWeights(((1, 1), (1, 1))), max_line_states=0)
        self.assertEqual(sampler.plan.line_states, 0)
        self.assertEqual(sampler.normalizer(), Fraction(1))
        self.assertEqual(sampler.sample(NoRandom()), ((0, 0), (1, 1)))

    def test_zero_cactus_cap_rejects_positive_plan_before_coefficients(self):
        problem = TableProblem((1, 1), (1, 1))
        weights = ProductWeights(((1, 1), (1, 1)))
        with patch.object(ProductWeights, "cell_weight",
                          side_effect=AssertionError("preflight must precede coefficients")):
            with self.assertRaises(ComputationBudgetExceeded):
                CactusWeightedSampler(problem, weights, max_line_states=0)

    def test_positive_plan_cannot_exceed_shared_cap(self):
        for reverse in (False, True):
            sampler = BlockWeightedSampler(
                two_factor_problem(reverse), ProductWeights(((1,) * 4,) * 4),
                budget=BlockSamplerBudget(max_cycle_line_states_total=1))
            for operation in (sampler.normalizer, lambda: sampler.sample(NoRandom())):
                with self.assertRaises(ComputationBudgetExceeded):
                    operation()
            self.assertLessEqual(sampler.stats["cycle_line_states"], 1)
            self.assertTrue(sampler.stats["failed"])

    def test_zero_mass_factor_needs_no_remaining_preparation_budget(self):
        for reverse in (False, True):
            problem = two_factor_problem(reverse)
            activities = [[1] * 4 for _ in range(4)]
            i, j = (1, 0) if reverse else (3, 2)
            activities[i][j] = 0
            expected = independent_tables(problem)
            self.assertTrue(all(table[i][j] == 1 for table in expected))
            sampler = BlockWeightedSampler(
                problem, ProductWeights(activities),
                budget=BlockSamplerBudget(
                    max_cycle_line_states_total=2,
                    max_cycle_weight_evaluations_total=8,
                    max_cycle_stored_weight_bits_total=14))
            self.assertEqual(sampler.normalizer(), Fraction(0))
            self.assertTrue(sampler.stats["complete"])
            self.assertFalse(sampler.stats["failed"])
            self.assertLessEqual(sampler.stats["cycle_line_states"], 2)
            self.assertLessEqual(sampler.stats["cycle_weight_evaluations"], 8)
            self.assertLessEqual(sampler.stats["cycle_stored_weight_bits"], 14)
            with self.assertRaises(ZeroMassError):
                sampler.sample(NoRandom())

    def test_zero_evaluation_or_storage_cap_rejects_before_coefficients(self):
        problem = TableProblem((0, 2), (1, 1))
        weights = ProductWeights(((1, 1), (1, 1)))
        for limit in ("max_weight_evaluations", "max_stored_weight_bits"):
            with self.subTest(limit=limit):
                with patch.object(ProductWeights, "cell_weight",
                                  side_effect=AssertionError("preflight must precede coefficients")):
                    with self.assertRaises(ComputationBudgetExceeded):
                        CactusWeightedSampler(problem, weights, **{limit: 0})

    def test_cumulative_caps_reject_negative_and_boolean_values(self):
        problem = TableProblem((0, 2), (1, 1))
        weights = ProductWeights(((1, 1), (1, 1)))
        for limit in ("max_line_states", "max_weight_evaluations", "max_stored_weight_bits"):
            for value, error in ((-1, ValueError), (True, TypeError)):
                with self.subTest(limit=limit, value=value):
                    with self.assertRaises(error):
                        CactusWeightedSampler(problem, weights, **{limit: value})
        with self.assertRaises(ValueError):
            CactusWeightedSampler(problem, weights, max_cell_value=0)


if __name__ == "__main__":
    unittest.main()
