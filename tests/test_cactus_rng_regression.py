"""Independent law and invalid-source regression for the cached line draw."""

from collections import Counter
from fractions import Fraction
from itertools import product
import unittest

from contingency115.cactus import CactusWeightedSampler
from contingency115.tables import ProductWeights, TableProblem


class Tape:
    def __init__(self, *values):
        self.values = iter(values)

    def randrange(self, stop):
        return next(self.values)


class CactusRngRegressionTests(unittest.TestCase):
    def test_factorial_law_from_every_integer_choice(self):
        # The three feasible tables have raw weights 1/4, 1, 1/4:
        # each extreme has two cells of count 2, while the middle has four 1s.
        sampler = CactusWeightedSampler(
            TableProblem([2, 2], [2, 2]), ProductWeights([[1, 1], [1, 1]], True)
        )
        actual = Counter(sampler.sample(Tape(rank)) for rank in range(6))
        self.assertEqual(actual, {
            ((0, 2), (2, 0)): 1,
            ((1, 1), (1, 1)): 4,
            ((2, 0), (0, 2)): 1,
        })

    def test_invalid_rng_output_rejected_on_each_cycle(self):
        # Two disjoint cycles sharing the first row. Exercise invalid output
        # both before and after a valid choice; neither may silently select a table.
        sampler = CactusWeightedSampler(
            TableProblem([4, 2, 2], [2] * 4,
                         [[2] * 4, [2, 2, 0, 0], [0, 0, 2, 2]]),
            ProductWeights([[1] * 4 for _ in range(3)], True),
        )
        for prefix, bad in product(((), (0,)), (-1, True, Fraction(1, 2), 0.5, 6)):
            with self.subTest(prefix=prefix, bad=bad):
                # Extra valid choices let the old code finish instead of
                # accidentally passing by exhausting the supplied tape.
                error = AssertionError if bad == 6 else (TypeError, ValueError)
                with self.assertRaises(error):
                    sampler.sample(Tape(*prefix, bad, 0))


if __name__ == "__main__":
    unittest.main()
