import unittest
from fractions import Fraction

from contingency115.general_scales import (local_completion_scales, reduced_completion_scales,
                                         two_by_two_core_scales)
from contingency115.tables import ExactTableSampler, TableProblem


def prescribed_block(m, n, r, c, padding, *, refined_growth=False):
    growth = min((m-1)*(n-1),m+n-2) if refined_growth else (m-1)*(n-1)
    cutoff = max(2, 2*padding, (47*r*c*padding*growth+31)//32-1)
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
        self.assertEqual((scales.rational_inverse_gap,scales.dyadic_inverse_gap),
                         (39600,57600))
        self.assertIsNone(scales.local_completion_dimension)
        original = ExactTableSampler(problem).count()
        padded = ExactTableSampler(TableProblem((1, 50, 50), (1, 50, 50))).count()
        self.assertEqual((original, padded), (231, 251))
        self.assertLessEqual(padded, 2*original)
        for m, n, r, c, padding in ((5, 7, 2, 3, 3), (7, 5, 3, 2, 3),
                                    (8, 9, 5, 6, 7), (3, 7, 1, 4, 1), (100, 3, 100, 2, 7)):
            with self.subTest(shape=(m, n), block=(r, c)):
                scales = reduced_completion_scales(prescribed_block(m, n, r, c, padding,
                                                                   refined_growth=True),
                                               large_row_count=r, large_column_count=c)
                self.assertEqual(scales.L, padding)
                self.assertTrue(3*(r-1)*(c-1) <= min(r, c)*scales.L or scales.L >= 7)
                growth = min((m-1)*(n-1),m+n-2)
                self.assertLessEqual(47*r*c*scales.L*growth, 32*(scales.U+1))

    def test_tight_core_padding_and_real_completion_scope(self):
        problem = TableProblem((1, 70, 70), (1, 70, 70))
        scales = two_by_two_core_scales(problem)
        self.assertEqual((scales.U, scales.L, scales.small_cells, scales.effective_width),
                         (70, 3, 5, 2))
        self.assertEqual((scales.degree_bound, scales.proposal_bits), (11, 5))
        self.assertEqual((scales.rational_inverse_gap, scales.dyadic_inverse_gap),
                         (39600, 57600))
        self.assertEqual(scales.stationary_success_lower_bound, Fraction(1, 25))
        self.assertEqual(scales.completion_margin_bound, 76)
        self.assertIsNone(scales.local_completion_dimension)
        original = ExactTableSampler(problem).count()
        padded = ExactTableSampler(TableProblem((1, 76, 76), (1, 76, 76))).count()
        self.assertEqual((original, padded), (351, 381))
        self.assertLessEqual(padded, 2*original)

    def test_reduced_rectangular_cutoff_requires_new_actual_classification(self):
        problem = prescribed_block(5,7,2,3,3,refined_growth=True)
        scales = reduced_completion_scales(problem,large_row_count=2,large_column_count=3)
        self.assertEqual((scales.U,scales.L,scales.small_cells,scales.effective_width),
                         (264,3,29,264))
        self.assertEqual(sum(r>=scales.U for r in problem.row_sums),2)
        self.assertEqual(sum(c>=scales.U for c in problem.column_sums),3)
        # A fixture classified at the old cutoff has its former small margins
        # above the new cutoff. The helper must refuse the requested class.
        old_problem = prescribed_block(5,7,2,3,3)
        self.assertEqual(min(old_problem.row_sums),633)
        with self.assertRaisesRegex(ValueError,"computed cutoff"):
            reduced_completion_scales(old_problem,large_row_count=2,large_column_count=3)
        # Historical core helper retains the donor-pair cutoff and class.
        historical = two_by_two_core_scales(prescribed_block(5,7,2,2,3))
        self.assertEqual(historical.U,422)
        # In a 2x3 outer table the old donor-pair growth parameter is smaller.
        smaller_old = reduced_completion_scales(prescribed_block(2,3,1,1,1),
                                                large_row_count=1,large_column_count=1)
        self.assertEqual((smaller_old.U,smaller_old.L),(2,1))

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
