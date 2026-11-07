"""Regression for malformed integer-source outputs that bisect accepted."""

from fractions import Fraction
import unittest

from contingency115.tables import (
    ExactWeightedTableSampler, ProductWeights, TableProblem,
    _draw_rational_choice,
)


class ConstantSource:
    def __init__(self, value):
        self.value = value

    def randrange(self, stop):
        return self.value


class WeightedIntegerSourceValidationTests(unittest.TestCase):
    def test_exact_sampler_rejects_noninteger_or_negative_rng_outputs(self):
        # Activities 2 ensure every reached stop exceeds 1. Previously bools,
        # negative integers and nonintegers all silently selected a table.
        problem = TableProblem((1, 1), (1, 1))
        weights = ProductWeights(((2, 2), (2, 2)))
        for value, error in ((-1, ValueError), (True, TypeError),
                             (False, TypeError), (Fraction(1, 2), TypeError),
                             (Fraction(0), TypeError), (0.5, TypeError)):
            with self.subTest(value=repr(value)):
                sampler = ExactWeightedTableSampler(problem, weights)
                with self.assertRaises(error):
                    sampler.sample(ConstantSource(value))

    def test_rational_choice_preserves_every_valid_integer_mapping(self):
        cumulative = (2, 5, 8)
        actual = [_draw_rational_choice(cumulative, ConstantSource(value))
                  for value in range(8)]
        self.assertEqual(actual, [0, 0, 1, 1, 1, 2, 2, 2])
        with self.assertRaisesRegex(AssertionError, "outside the requested range"):
            _draw_rational_choice(cumulative, ConstantSource(8))


if __name__ == "__main__":
    unittest.main()
