"""Independent finite count and incidence checks for the padding obstruction."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb
import unittest
from unittest.mock import patch

from contingency115.padding import (count_padded_tables,
                                    half_acceptance_necessary_margin,
                                    padding_count_plan, padding_target_indegree,
                                    unpadding_success_upper_bound)
from contingency115.tables import ComputationBudgetExceeded


def direct_rows(n, u, ell):
    """Enumerate a Cartesian box and solve the last coordinate, without counts."""
    cap, total = u + 2 * ell, u + n * ell
    for prefix in product(range(cap + 1), repeat=n - 1):
        last = total - sum(prefix)
        if 0 <= last <= cap:
            yield (*prefix, last)


def direct_incidences(n, u, ell):
    all_rows = set(direct_rows(n, u, ell))
    good = {row for row in all_rows if min(row) >= ell}
    incoming = Counter()
    for row in good:
        for j in range(n):
            for k in range(n):
                if j == k:
                    continue
                for h in range(ell):
                    target = list(row)
                    amount = row[j] - h
                    target[j] = h
                    target[k] += amount
                    target = tuple(target)
                    if target not in all_rows or target in good:
                        raise AssertionError("switching left the target family")
                    if [index for index, value in enumerate(target) if value < ell] != [j]:
                        raise AssertionError("target does not have the specified unique low cell")
                    incoming[target] += 1
    return all_rows, good, incoming


class PaddingCountTests(unittest.TestCase):
    def test_direct_counts_and_incidence_degrees(self):
        for n in range(2, 6):
            for u in range(1, 5):
                for ell in (1, 2):
                    with self.subTest(n=n, u=u, ell=ell):
                        all_rows, good, incoming = direct_incidences(n, u, ell)
                        result = count_padded_tables(n, u, ell)
                        self.assertEqual((result.good, result.total), (len(good), len(all_rows)))
                        self.assertEqual(result.success_probability, Fraction(len(good), len(all_rows)))
                        self.assertLessEqual(result.success_probability, result.success_upper_bound)
                        self.assertEqual(sum(incoming.values()), len(good) * ell * n * (n - 1))
                        for row in all_rows:
                            self.assertEqual(incoming[row], padding_target_indegree(row, u, ell))
                            self.assertLessEqual(incoming[row], u + 1)
                        # Both rows, not only the first, must survive unpadding.
                        cap = u + 2 * ell
                        self.assertEqual(good, {row for row in all_rows
                                                if all(ell <= value <= cap - ell for value in row)})

    def test_two_by_two_equality_and_half_acceptance_boundary(self):
        for ell in (1, 2, 10, 10**9):
            for u in (1, 2, 10, 2 * ell - 1, 2**100):
                result = count_padded_tables(2, u, ell)
                self.assertEqual(result.good, u + 1)
                self.assertEqual(result.total, u + 2 * ell + 1)
                self.assertEqual(result.success_probability, result.success_upper_bound)
            boundary = half_acceptance_necessary_margin(2, ell)
            self.assertEqual(count_padded_tables(2, boundary, ell).success_probability, Fraction(1, 2))

    def test_necessary_threshold_is_not_sufficient(self):
        n, ell = 3, 2
        u = half_acceptance_necessary_margin(n, ell)
        result = count_padded_tables(n, u, ell)
        self.assertEqual(result.success_upper_bound, Fraction(1, 2))
        self.assertLess(result.success_probability, Fraction(1, 2))

    def test_large_dimension_exact_count_and_bit_budget_certificate(self):
        for n in (2, 4, 10, 30, 100):
            d = 3 * n + 13
            ell = 32 * d**3
            for u in (ell * n, ell * n**2, 2 * ell * n**2):
                result = count_padded_tables(n, u, ell)
                self.assertLessEqual(result.success_probability, result.success_upper_bound)
                self.assertGreater(result.good, 0)
                self.assertGreaterEqual(result.total, result.good)
                s, cap = u + n * ell, u + 2 * ell
                partial = 0
                intermediates = [result.good, result.total]
                for k in range(result.plan.inclusion_exclusion_terms):
                    term = (-1)**k * comb(n, k) * comb(s - k * (cap + 1) + n - 1, n - 1)
                    partial += term
                    intermediates.extend((abs(term), abs(partial)))
                self.assertLessEqual(max(value.bit_length() for value in intermediates),
                                     result.plan.integer_bit_bound)


class PaddingValidationTests(unittest.TestCase):
    def test_reject_malformed_parameters(self):
        for parameters in ((1, 1, 1), (True, 1, 1), (2.0, 1, 1),
                           (2, 0, 1), (2, -1, 1), (2, 1, 0), (2, 1, True)):
            for function in (count_padded_tables, padding_count_plan, unpadding_success_upper_bound):
                with self.assertRaises((TypeError, ValueError)):
                    function(*parameters)
        for name in ("max_terms", "max_binomial_order_sum", "max_integer_bits"):
            for value in (-1, True, 1.0, None):
                with self.assertRaises((ValueError, TypeError)):
                    count_padded_tables(2, 1, 1, **{name: value})

    def test_budget_rejection_occurs_before_binomial_evaluation(self):
        with patch("contingency115.padding.comb", side_effect=AssertionError("too late")):
            for options in ({"max_terms": 0}, {"max_binomial_order_sum": 0}, {"max_integer_bits": 1}):
                with self.assertRaises(ComputationBudgetExceeded):
                    count_padded_tables(10, 10, 10, **options)
            with self.assertRaises(ComputationBudgetExceeded):
                count_padded_tables(2**80, 1, 1)

    def test_target_must_belong_to_the_padded_family(self):
        for row in ((1,), (0, 0), (1, 1), (-1, 4), (True, 2), (1.0, 2), (4, -1)):
            with self.assertRaises((ValueError, TypeError)):
                padding_target_indegree(row, 1, 1)
        self.assertEqual(padding_target_indegree((1, 2), 1, 1), 0)
        self.assertEqual(padding_target_indegree((0, 3), 1, 1), 2)


if __name__ == "__main__":
    unittest.main()
