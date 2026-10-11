import unittest
from fractions import Fraction

from contingency115.general_scales import (local_completion_scales, reduced_completion_scales,
                                         two_by_two_core_scales)
from contingency115.tables import ExactTableSampler, TableProblem


def prescribed_block(m, n, r, c, padding):
    cutoff = max(2, 2*padding, (47*r*c*padding*(m-1)*(n-1)+31)//32-1)
    rows = [cutoff]*r + [cutoff-1]*(m-r)
    columns = [cutoff]*c + [cutoff-1]*(n-c)
    difference = sum(rows)-sum(columns)
    if difference > 0:
        columns[0] += difference
    else:
        rows[0] -= difference
    return TableProblem(rows, columns)


class GeneralScaleTests(unittest.TestCase):
    def test_residual_floors_reduce_padding_with_real_count_check(self):
        problem = TableProblem((1, 46, 46), (1, 46, 46))
        scales = reduced_completion_scales(problem, large_row_count=2, large_column_count=2)
        self.assertEqual((scales.U, scales.L, scales.small_cells), (46, 2, 5))
        self.assertIsNone(scales.local_completion_dimension)
        original = ExactTableSampler(problem).count()
        padded = ExactTableSampler(TableProblem((1, 50, 50), (1, 50, 50))).count()
        self.assertEqual((original, padded), (231, 251))
        self.assertLessEqual(padded, 2*original)
        for m, n, r, c, padding in ((5, 7, 2, 3, 3), (7, 5, 3, 2, 3),
                                    (8, 9, 5, 6, 7), (3, 7, 1, 4, 1), (100, 3, 100, 2, 7)):
            with self.subTest(shape=(m, n), block=(r, c)):
                scales = reduced_completion_scales(prescribed_block(m, n, r, c, padding),
                                               large_row_count=r, large_column_count=c)
                self.assertEqual(scales.L, padding)
                self.assertTrue(3*(r-1)*(c-1) <= min(r, c)*scales.L or scales.L >= 7)
                self.assertLessEqual(47*r*c*scales.L*(m-1)*(n-1), 32*(scales.U+1))

    def test_tight_core_padding_and_real_completion_scope(self):
        problem = TableProblem((1, 70, 70), (1, 70, 70))
        scales = two_by_two_core_scales(problem)
        self.assertEqual((scales.U, scales.L, scales.small_cells, scales.effective_width),
                         (70, 3, 5, 2))
        self.assertEqual((scales.degree_bound, scales.proposal_bits), (11, 5))
        self.assertEqual((scales.rational_inverse_gap, scales.dyadic_inverse_gap),
                         (88000, 128000))
        self.assertEqual(scales.stationary_success_lower_bound, Fraction(1, 25))
        self.assertEqual(scales.completion_margin_bound, 76)
        self.assertIsNone(scales.local_completion_dimension)
        original = ExactTableSampler(problem).count()
        padded = ExactTableSampler(TableProblem((1, 76, 76), (1, 76, 76))).count()
        self.assertEqual((original, padded), (351, 381))
        self.assertLessEqual(padded, 2*original)

    def test_rectangular_self_consistency_and_local_program_floors(self):
        for m, n in ((2, 3), (3, 2), (4, 7), (7, 4), (5, 5)):
            with self.subTest(m=m, n=n):
                direct = two_by_two_core_scales(prescribed_block(m, n, 2, 2, 3))
                self.assertEqual(direct.small_cells, m*n-4)
                self.assertLessEqual(47*4*3*(m-1)*(n-1), 32*(direct.U+1))
                self.assertLessEqual(direct.degree_bound, 6*(m+n))
                self.assertLessEqual(direct.rational_inverse_gap, direct.dyadic_inverse_gap)
                self.assertLess(direct.dyadic_inverse_gap, 2*direct.rational_inverse_gap)
        for m, n, r, c in ((5, 7, 2, 3), (7, 5, 3, 2), (8, 9, 5, 6), (3, 7, 1, 4)):
            dimension = max(14, r, c, (r-1)*(c-1)+1)
            problem = prescribed_block(m, n, r, c, 3*dimension)
            scales = local_completion_scales(problem, large_row_count=r, large_column_count=c)
            self.assertEqual(scales.local_completion_dimension, dimension)
            self.assertEqual(scales.L, 3*dimension)
            self.assertLessEqual((r-1)*(c-1), dimension-1)
            self.assertLessEqual(47*r*c*scales.L*(m-1)*(n-1), 32*(scales.U+1))
            self.assertLessEqual(2*scales.L, scales.U)
            self.assertGreater(scales.stationary_success_lower_bound, 0)
            self.assertLessEqual(scales.effective_width, scales.U)

    def test_classification_and_ordinary_scope_are_checked(self):
        for problem in (TableProblem((1, 2, 2), (1, 2, 2)),
                        TableProblem((0, 70, 70), (0, 70, 70)),
                        TableProblem((70, 70), (70, 70)),
                        TableProblem((1, 70, 70), (1, 70, 70),
                                     upper_bounds=((0, 1, 1), (1, 70, 70), (1, 70, 70)))):
            with self.assertRaises(ValueError):
                two_by_two_core_scales(problem)
        problem = TableProblem((1, 70, 70), (1, 70, 70))
        for count in (0, -1, True, 2.0):
            with self.assertRaises((ValueError, TypeError)):
                local_completion_scales(problem, large_row_count=count, large_column_count=2)
        with self.assertRaises(ValueError):
            local_completion_scales(problem, large_row_count=4, large_column_count=2)


if __name__ == "__main__":
    unittest.main()
