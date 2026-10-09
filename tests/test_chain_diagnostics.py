from fractions import Fraction as F
import unittest

from contingency115.chain_diagnostics import stationary_variance
from contingency115.kernels import ExactKernel
from contingency115.tables import ComputationBudgetExceeded


def kernel(matrix, pi):
    return ExactKernel(tuple(((i,),) for i in range(len(pi))), tuple(tuple(F(x) for x in row) for row in matrix), tuple(F(p) for p in pi))


class StationaryVarianceTests(unittest.TestCase):
    def test_iid_weighted_two_states(self):
        result = stationary_variance(kernel([[F(1, 3), F(2, 3)]] * 2, [F(1, 3), F(2, 3)]), [0, 3])
        self.assertEqual((result.mean, result.variance, result.asymptotic_variance), (2, 2, 2))
        self.assertEqual(result.variance_inflation_factor, 1)
        self.assertTrue(result.irreducible_on_positive_support)

    def test_persistent_two_state_analytic_answer(self):
        # Eigenvalue 1/2, variance 1/4, inflation (1+lambda)/(1-lambda)=3.
        result = stationary_variance(kernel([[F(3, 4), F(1, 4)], [F(1, 4), F(3, 4)]], [F(1, 2)] * 2), [0, 1])
        self.assertEqual(result.asymptotic_variance, F(3, 4))
        self.assertEqual(result.variance_inflation_factor, 3)

    def test_periodic_alternation_has_zero_limit_not_covariance_sum(self):
        result = stationary_variance(kernel([[0, 1], [1, 0]], [F(1, 2)] * 2), [0, 2])
        self.assertEqual(result.variance, 1)
        self.assertEqual(result.asymptotic_variance, 0)
        self.assertEqual(result.status, "zero_asymptotic_variance")

    def test_constant_observable(self):
        result = stationary_variance(kernel([[F(1, 2)] * 2] * 2, [F(1, 2)] * 2), [7, 7])
        self.assertEqual((result.variance, result.asymptotic_variance), (0, 0))
        self.assertIsNone(result.variance_inflation_factor)
        self.assertEqual(result.status, "zero_observable_variance")

    def test_disconnected_different_means(self):
        result = stationary_variance(kernel([[1, 0], [0, 1]], [F(1, 2)] * 2), [0, 2])
        self.assertFalse(result.irreducible_on_positive_support)
        self.assertEqual(result.component_means, (0, 2))
        self.assertEqual(result.between_class_variance, 1)
        self.assertIsNone(result.asymptotic_variance)
        self.assertEqual(result.status, "infinite_between_classes")

    def test_disconnected_identical_means_have_finite_stationary_ensemble_limit(self):
        result = stationary_variance(kernel([[F(1, 2), F(1, 2), 0, 0], [F(1, 2), F(1, 2), 0, 0],
                                             [0, 0, F(1, 2), F(1, 2)], [0, 0, F(1, 2), F(1, 2)]], [F(1, 4)] * 4), [0, 2, -1, 3])
        self.assertFalse(result.irreducible_on_positive_support)
        self.assertEqual(result.component_means, (1, 1))
        self.assertEqual(result.between_class_variance, 0)
        self.assertEqual(result.asymptotic_variance, F(5, 2))

    def test_null_target_states_are_excluded(self):
        result = stationary_variance(kernel([[F(1, 2), F(1, 2), 0], [F(1, 2), F(1, 2), 0], [1, 0, 0]], [F(1, 2), F(1, 2), 0]), [0, 2, 1000])
        self.assertEqual(result.positive_support_classes, ((0, 1),))
        self.assertEqual(result.asymptotic_variance, 1)

    def test_validation_and_resource_failures(self):
        valid = kernel([[F(1, 2)] * 2] * 2, [F(1, 2)] * 2)
        with self.assertRaises(ComputationBudgetExceeded): stationary_variance(valid, [0, 1], max_states=1)
        with self.assertRaises(ComputationBudgetExceeded): stationary_variance(valid, [0, 1000], max_rational_bits=3)
        invalid = [kernel([[1, 0], [0, 1]], [1, 1]), kernel([[0, 1], [0, 1]], [F(1, 2)] * 2),
                   kernel([[2, -1], [-1, 2]], [F(1, 2)] * 2), ExactKernel(valid.states, ((F(1),),), valid.stationary)]
        for bad in invalid:
            with self.assertRaises(ValueError): stationary_variance(bad, [0, 1])
        with self.assertRaises(ValueError): stationary_variance(valid, [0, 1.0])
        with self.assertRaises(ValueError): stationary_variance(valid, [0, True])
        with self.assertRaises(ValueError): stationary_variance(valid, [0])
        with self.assertRaises(ValueError): stationary_variance(valid, [0, 1], max_states=True)


if __name__ == "__main__":
    unittest.main()
