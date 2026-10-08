from fractions import Fraction
from itertools import combinations, permutations, product
import unittest

from contingency115.kernels import ExactKernel
from contingency115.mixtures import (certify_gap_lower_bound, check_psd, fixed_mixture,
                                      mixture_gap_upper_bound, rayleigh_quotient)
from contingency115.tables import ComputationBudgetExceeded


def kernel(matrix, pi=None):
    size = len(matrix)
    return ExactKernel(tuple(((i,),) for i in range(size)),
                       tuple(tuple(Fraction(x) for x in row) for row in matrix),
                       tuple(Fraction(x) for x in (pi or [Fraction(1, size)] * size)))


def determinant(matrix):
    size = len(matrix)
    result = Fraction(0)
    for permutation in permutations(range(size)):
        sign = (-1) ** sum(permutation[i] > permutation[j]
                           for i in range(size) for j in range(i + 1, size))
        term = sign
        for i in range(size):
            term *= matrix[i][permutation[i]]
        result += term
    return result


class ExactMixtureTests(unittest.TestCase):
    def test_fraction_free_psd_against_all_principal_minors(self):
        # Independent characterization, including indefinite zero-pivot cases.
        for entries in product((-1, 0, 1), repeat=6):
            a, b, c, d, e, f = entries
            matrix = ((a, b, c), (b, d, e), (c, e, f))
            expected = all(determinant(tuple(tuple(matrix[i][j] for j in subset) for i in subset)) >= 0
                           for count in (1, 2, 3) for subset in combinations(range(3), count))
            self.assertEqual(check_psd(matrix).is_psd, expected, entries)

    def test_psd_rational_rank_and_skipped_zero_pivots(self):
        matrices = [
            ((0, 0, 0), (0, Fraction(1, 3), Fraction(2, 5)), (0, Fraction(2, 5), Fraction(12, 25))),
            ((4, 0, 6, 0), (0, 0, 0, 0), (6, 0, 9, 0), (0, 0, 0, Fraction(2, 7))),
            ((Fraction(2**201, 3), 1), (1, Fraction(3, 2**201))),
        ]
        for matrix, rank in zip(matrices, (1, 2, 1)):
            result = check_psd(matrix)
            self.assertTrue(result.is_psd)
            self.assertEqual(result.positive_pivots, rank)
            self.assertEqual(result.zero_pivots, len(matrix) - rank)
        self.assertTrue(check_psd(()).is_psd)
        self.assertFalse(check_psd(((0, 1), (1, 0))).is_psd)

    def test_psd_input_validation_and_dimension_budget(self):
        with self.assertRaises(ValueError):
            check_psd(((1, 0),))
        with self.assertRaises(ValueError):
            check_psd(((1, 1), (0, 1)))
        for value in (0.5, True, "1/2"):
            with self.assertRaises(TypeError):
                check_psd(((value,),))
        with self.assertRaises(ComputationBudgetExceeded):
            check_psd(((1, 0), (0, 1)), max_states=1)
        with self.assertRaises(ValueError):
            check_psd(((1,),), max_states=True)

    def test_exact_nonuniform_two_state_gap_and_sharp_witness(self):
        p = kernel(((Fraction(2, 3), Fraction(1, 3)),
                    (Fraction(1, 2), Fraction(1, 2))), (Fraction(3, 5), Fraction(2, 5)))
        exact = Fraction(5, 6)
        self.assertTrue(certify_gap_lower_bound(p, exact).certified)
        self.assertFalse(certify_gap_lower_bound(p, exact + Fraction(1, 100)).certified)
        self.assertEqual(rayleigh_quotient(p, (0, 7)), exact)

    def test_certifies_algebraic_not_absolute_gap(self):
        periodic = kernel(((0, 1), (1, 0)))
        self.assertTrue(certify_gap_lower_bound(periodic, 2).certified)
        self.assertEqual(rayleigh_quotient(periodic, (1, -1)), 2)

    def test_zero_target_mass_and_singleton_convention(self):
        p = kernel(((Fraction(1, 2), Fraction(1, 2), 0),
                    (Fraction(1, 2), Fraction(1, 2), 0), (1, 0, 0)),
                   (Fraction(1, 2), Fraction(1, 2), 0))
        proof = certify_gap_lower_bound(p, 1)
        self.assertTrue(proof.certified)
        self.assertEqual(proof.positive_support, (0, 1))
        self.assertEqual(rayleigh_quotient(p, (1, -1, 2**200)), 1)
        with self.assertRaises(ValueError):
            rayleigh_quotient(p, (0, 0, 1))
        single = kernel(((1,),))
        self.assertTrue(certify_gap_lower_bound(single, 1).certified)
        self.assertFalse(certify_gap_lower_bound(single, Fraction(3, 2)).certified)

    def test_disconnected_kernel_has_zero_gap(self):
        p = kernel(((1, 0), (0, 1)))
        self.assertTrue(certify_gap_lower_bound(p, 0).certified)
        self.assertFalse(certify_gap_lower_bound(p, Fraction(1, 10**30)).certified)
        self.assertEqual(rayleigh_quotient(p, (0, 1)), 0)

    def test_fixed_mixture_and_global_dual_certificate(self):
        h = Fraction(1, 2)
        components = (kernel(((h, h, 0), (h, h, 0), (0, 0, 1))),
                      kernel(((1, 0, 0), (0, h, h), (0, h, h))),
                      kernel(((h, 0, h), (0, 1, 0), (h, 0, h))))
        mixture = fixed_mixture(components, [Fraction(1, 3)] * 3)
        self.assertTrue(mixture.is_stochastic())
        self.assertTrue(mixture.satisfies_detailed_balance())
        self.assertTrue(certify_gap_lower_bound(mixture, h).certified)
        dual = mixture_gap_upper_bound(components, ((1, -1, 0), (1, 1, -2)), (h, h))
        self.assertEqual(dual.bound, h)
        self.assertEqual(dual.component_bounds, (h, h, h))
        edge = fixed_mixture(components, (h, h, 0))
        self.assertTrue(certify_gap_lower_bound(edge, Fraction(1, 4)).certified)
        self.assertFalse(certify_gap_lower_bound(edge, Fraction(1, 4) + Fraction(1, 10**20)).certified)

    def test_kernel_validation_is_exact(self):
        states = (((0,),), ((1,),))
        invalid = (
            ExactKernel(states, ((1, 0),), (Fraction(1, 2),) * 2),
            ExactKernel(states, ((1, 0), (0, 1)), (1,)),
            ExactKernel(states, ((1, 0), (0, 1)), (1, 1)),
            ExactKernel(states, ((2, -1), (0, 1)), (Fraction(1, 2),) * 2),
            ExactKernel(states, ((1, 0), (1, 0)), (Fraction(1, 2),) * 2),
            ExactKernel(states, ((Fraction(1, 2), 0), (0, 1)), (Fraction(1, 2),) * 2),
            ExactKernel((states[0], states[0]), ((1, 0), (0, 1)), (Fraction(1, 2),) * 2),
        )
        for value in invalid:
            with self.assertRaises(ValueError):
                certify_gap_lower_bound(value, 0)
        bad_float = ExactKernel(states, ((0.5, 0.5), (0.5, 0.5)), (Fraction(1, 2),) * 2)
        with self.assertRaises(TypeError):
            certify_gap_lower_bound(bad_float, 0)

    def test_mixture_and_witness_validation(self):
        p = kernel(((1, 0), (0, 1)))
        q = kernel(((1, 0), (0, 1)), (Fraction(1, 3), Fraction(2, 3)))
        for probabilities in ((1, 1), (-1, 2), (1,), ()):
            with self.assertRaises(ValueError):
                fixed_mixture((p, p), probabilities)
        with self.assertRaises(ValueError):
            fixed_mixture((p, q), (Fraction(1, 2),) * 2)
        with self.assertRaises(ValueError):
            fixed_mixture((), ())
        with self.assertRaises(TypeError):
            fixed_mixture((p,), (1.0,))
        with self.assertRaises(ValueError):
            mixture_gap_upper_bound((p,), ((1, 1),), (1,))
        with self.assertRaises(ValueError):
            mixture_gap_upper_bound((p,), ((1,),), (1,))
        with self.assertRaises(ValueError):
            rayleigh_quotient(p, (1,))
        for bound in (-1, 3):
            with self.assertRaises(ValueError):
                certify_gap_lower_bound(p, bound)
        with self.assertRaises(TypeError):
            certify_gap_lower_bound(p, 0.5)


if __name__ == "__main__":
    unittest.main()
