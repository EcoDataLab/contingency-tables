"""Independent finite switching checks and universal scale arithmetic certificates."""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
import unittest

from contingency115.scales import (
    evaluate_polynomial,
    proposed_scale_certificates,
    proposed_scales,
    reference_adjustment,
    scale_probability_bounds,
    scale_residuals,
    small_entry_bound,
    small_entry_bound_refined,
    switching_outdegree,
)


def compositions(total, length):
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in compositions(total - first, length - 1):
            yield (first,) + tail


def fiber_catalog(rows, columns, total):
    fibers = defaultdict(list)
    for flat in compositions(total, rows * columns):
        table = tuple(tuple(flat[i * columns:(i + 1) * columns]) for i in range(rows))
        r = tuple(sum(row) for row in table)
        c = tuple(sum(table[i][j] for i in range(rows)) for j in range(columns))
        fibers[r, c].append(table)
    return fibers


class SwitchingTests(unittest.TestCase):
    def test_minimum_sum_inequality(self):
        # Includes empty donor lists and concentrated versus diffuse donors.
        vectors = [v for n in range(4) for v in product(range(4), repeat=n)]
        for a in vectors:
            for b in vectors:
                self.assertGreaterEqual(sum(min(x, y) for x in a for y in b),
                                        min(sum(a), sum(b)))

    def test_all_small_fiber_probabilities(self):
        # Every table, hence every margin fiber, of these shapes and totals.
        shapes = ((1, 1), (1, 3), (3, 1), (2, 2), (2, 3), (3, 2), (3, 3))
        checked = 0
        for rows, columns in shapes:
            for total in range(7):
                for (r, c), tables in fiber_catalog(rows, columns, total).items():
                    for i, j in product(range(rows), range(columns)):
                        margin = min(r[i], c[j])
                        for threshold in range(1, margin + 1):
                            bad = sum(table[i][j] < threshold for table in tables)
                            actual = Fraction(bad, len(tables))
                            self.assertLessEqual(actual, small_entry_bound(
                                rows, columns, margin, threshold))
                            self.assertLessEqual(actual, small_entry_bound_refined(
                                rows, columns, margin, threshold))
                            checked += 1
        self.assertGreater(checked, 10_000)

    def test_refined_bound_is_exact_at_zero_for_balanced_two_by_two(self):
        for margin in range(1, 20):
            tables = [((x, margin - x), (margin - x, x))
                      for x in range(margin + 1)]
            probability = Fraction(sum(t[0][0] == 0 for t in tables), len(tables))
            self.assertEqual(probability, small_entry_bound_refined(2, 2, margin, 1))
            self.assertLess(probability, small_entry_bound(2, 2, margin, 1))

    def test_switching_labels_determine_source(self):
        # Exhaustively check the incidence multigraph, without assuming that
        # different choices have different target tables.
        checked_switches = 0
        for rows, columns in ((2, 2), (2, 3), (3, 2), (3, 3)):
            for total in range(7):
                for (r, c), tables in fiber_catalog(rows, columns, total).items():
                    table_set = set(tables)
                    for i, j in product(range(rows), range(columns)):
                        inverse = {}
                        for table in tables:
                            h = table[i][j]
                            self.assertGreaterEqual(switching_outdegree(table, i, j),
                                                    min(r[i] - h, c[j] - h))
                            for ii in range(rows):
                                if ii == i:
                                    continue
                                for jj in range(columns):
                                    if jj == j:
                                        continue
                                    for amount in range(1, min(table[i][jj], table[ii][j]) + 1):
                                        target = [list(row) for row in table]
                                        for a, b, sign in ((i, j, 1), (ii, jj, 1),
                                                           (i, jj, -1), (ii, j, -1)):
                                            target[a][b] += sign * amount
                                        target = tuple(map(tuple, target))
                                        self.assertIn(target, table_set)
                                        key = (target, ii, jj, h)
                                        self.assertNotIn(key, inverse)
                                        inverse[key] = table
                                        self.assertEqual(target[i][j] - h, amount)
                                        checked_switches += 1
                        for threshold in range(1, min(r[i], c[j]) + 1):
                            incoming = Counter(key[0] for key in inverse if key[3] < threshold)
                            for target in tables:
                                self.assertLessEqual(incoming[target],
                                                     (rows - 1) * (columns - 1)
                                                     * min(threshold, target[i][j]))
        self.assertGreater(checked_switches, 20_000)

    def test_boundary_domain_and_cap_negative_control(self):
        self.assertEqual(small_entry_bound(1, 5, 7, 7), 0)
        self.assertEqual(small_entry_bound(5, 1, 7, 1), 0)
        for args in ((0, 2, 1, 1), (2, 2, 0, 1), (2, 2, 1, 2), (2, 2, 2, 0)):
            with self.assertRaises(ValueError):
                small_entry_bound(*args)
        # A forbidden marked cell breaks closure under switches and the bound.
        # Margins (5,5)/(5,5), cap(0,0)=0: unique table has X00=0.
        self.assertLess(small_entry_bound(2, 2, 5, 1), Fraction(1))


class ReferenceAdjustmentTests(unittest.TestCase):
    def test_every_elementary_margin_family_and_reference_cell(self):
        count = 0
        for rows, columns in product(range(1, 6), repeat=2):
            cases = {((0,) * rows, (0,) * columns)}
            for a, b in product(range(rows), repeat=2):
                r = [0] * rows
                r[a] += 1
                r[b] -= 1
                cases.add((tuple(r), (0,) * columns))
            for a, b in product(range(columns), repeat=2):
                c = [0] * columns
                c[a] += 1
                c[b] -= 1
                cases.add(((0,) * rows, tuple(c)))
            for a, b, sign in product(range(rows), range(columns), (-1, 1)):
                r, c = [0] * rows, [0] * columns
                r[a], c[b] = sign, sign
                cases.add((tuple(r), tuple(c)))
            for r, c in cases:
                for i0, j0 in product(range(rows), range(columns)):
                    adjustment = reference_adjustment(r, c, i0, j0)
                    flat = [x for row in adjustment for x in row]
                    self.assertEqual(tuple(sum(row) for row in adjustment), r)
                    self.assertEqual(tuple(sum(adjustment[i][j] for i in range(rows))
                                           for j in range(columns)), c)
                    self.assertLessEqual(max(map(abs, flat)), 1)
                    self.assertLessEqual(sum(x != 0 for x in flat), 3)
                    self.assertLessEqual(sum(x < 0 for x in flat), 2)
                    self.assertLessEqual(min(sum(x < 0 for x in flat),
                                             sum(x > 0 for x in flat)), 1)
                    reverse = reference_adjustment(tuple(-x for x in r),
                                                   tuple(-x for x in c), i0, j0)
                    self.assertEqual(reverse, tuple(tuple(-x for x in row) for row in adjustment))
                    count += 1
        self.assertGreater(count, 10_000)

    def test_empty_blocks_and_incompatible_inputs(self):
        self.assertEqual(reference_adjustment((), ()), ())
        self.assertEqual(reference_adjustment((), (0, 0)), ())
        self.assertEqual(reference_adjustment((0, 0), ()), ((), ()))
        with self.assertRaises(ValueError):
            reference_adjustment((), (1, -1))
        with self.assertRaises(ValueError):
            reference_adjustment((1,), (0,))


class ScaleCertificateTests(unittest.TestCase):
    def test_universal_integer_polynomial_certificates(self):
        certificates = proposed_scale_certificates()
        self.assertTrue(all(c.verify() for c in certificates))
        for d in (14, 19, 22, 100, 10**6):
            residuals = scale_residuals(proposed_scales(d))
            self.assertEqual(set(residuals), {c.name for c in certificates})
            for c in certificates:
                self.assertEqual(evaluate_polynomial(c.coefficients, d), residuals[c.name])
                self.assertEqual(evaluate_polynomial(c.shifted_coefficients, d - c.lower),
                                 residuals[c.name])

    def test_parameter_fractions_and_old_unpadding_negative_control(self):
        for d in (14, 19, 22, 100):
            scales = proposed_scales(d)
            bounds = scale_probability_bounds(scales)
            self.assertEqual(bounds["inner_volume_loss"], Fraction(1, 4))
            self.assertEqual(bounds["log_density_change_per_bin"], 1)
            self.assertEqual(bounds["layer_exponent_sum"], Fraction(1, 4))
            self.assertLess(bounds["directional_completion_rejection"], Fraction(1, 2))
            self.assertLess(bounds["unpadding_bad_fraction"], Fraction(1, 2))
            # The new U cannot be justified by rechecking the old six inequalities.
            self.assertGreater(Fraction(4 * scales.L * d**4, scales.U), Fraction(1, 2))
        for d in (0, 13, 14.0, True):
            with self.assertRaises(ValueError):
                proposed_scales(d)


if __name__ == "__main__":
    unittest.main()
