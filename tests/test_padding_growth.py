from fractions import Fraction
import unittest

from contingency115.padding_growth import (
    growth_envelope, sequential_padding_bound, sequential_scales,
    sequential_shape_scales,
)
from contingency115.tables import ExactTableSampler, TableProblem


class SequentialPaddingTests(unittest.TestCase):
    def test_power_bound_with_exact_independent_powers(self):
        cases = 0
        for q in range(31):
            for numerator in range(7):
                for denominator in (1, 3, 7, 19, 101):
                    x = Fraction(numerator, denominator)
                    if q*x < 3:
                        self.assertLessEqual((1+x)**q, growth_envelope(q*x))
                        cases += 1
        self.assertGreater(cases, 400)

    def test_actual_padded_fibers_for_every_marked_set(self):
        rows, columns = (13, 13), (9, 9, 8)
        original = ExactTableSampler(TableProblem(rows, columns)).count()
        for mask in range(64):
            marked = [(i, j) for i in range(2) for j in range(3)
                      if mask & (1 << (3*i+j))]
            U = min((min(rows[i], columns[j]) for i, j in marked), default=0)
            for L in (1, 2):
                padded_rows, padded_columns = list(rows), list(columns)
                for i, j in marked:
                    padded_rows[i] += L
                    padded_columns[j] += L
                enlarged = ExactTableSampler(TableProblem(padded_rows, padded_columns)).count()
                q, e = len(marked)*L, 2
                self.assertLessEqual(enlarged*(U+1)**q, original*(U+1+e)**q)
                bound = sequential_padding_bound(q, e, U)
                self.assertLessEqual(enlarged, original*bound.count_growth_upper_bound)
                self.assertLessEqual(bound.acceptance_lower_bound, Fraction(original, enlarged))

    def test_rational_certificate_and_large_dimensions(self):
        certificate = growth_envelope(Fraction(32, 47))
        self.assertEqual(certificate, Fraction(10147, 5123))
        self.assertLess(certificate, 2)
        for d in (14, 19, 100, 10**20):
            s = sequential_scales(d)
            self.assertEqual(s.U, 47*d**5)
            result = sequential_padding_bound(d*s.L, d, s.U)
            self.assertLess(result.rate, Fraction(32, 47))
            self.assertGreater(result.acceptance_lower_bound, Fraction(1, 2))
            self.assertGreaterEqual(s.U, 2*s.L)

    def test_shape_threshold(self):
        for rows in range(1, 8):
            for columns in range(1, 9):
                s = sequential_shape_scales(rows, columns)
                e = (rows-1)*(columns-1)
                result = sequential_padding_bound(rows*columns*s.L, e, s.U)
                self.assertLessEqual(result.rate, Fraction(32, 47))
                self.assertGreater(result.acceptance_lower_bound, Fraction(1, 2))
                self.assertGreaterEqual(s.U, 2*s.L)

    def test_degenerate_cases_and_validation(self):
        for q, e, U in ((0, 2, 0), (100, 0, 0), (0, 0, 0)):
            result = sequential_padding_bound(q, e, U)
            self.assertEqual(result.acceptance_lower_bound, 1)
            self.assertEqual(result.count_growth_upper_bound, 1)
        for args in ((True, 1, 1), (1, -1, 1), (1, 1, Fraction(1)), (1, 1, -1)):
            with self.assertRaises((TypeError, ValueError)):
                sequential_padding_bound(*args)
        for t in (-1, 3, Fraction(10, 3)):
            with self.assertRaises(ValueError):
                growth_envelope(t)
        for t in (True, 0.5, "1/2"):
            with self.assertRaises(TypeError):
                growth_envelope(t)
        with self.assertRaises(ValueError):
            sequential_scales(13)
        with self.assertRaises(ValueError):
            sequential_shape_scales(0, 2)


if __name__ == "__main__":
    unittest.main()
