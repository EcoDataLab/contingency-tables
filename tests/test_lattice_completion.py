from collections import Counter
from fractions import Fraction
from itertools import product
import random
import unittest

from contingency115.lattice_completion import (
    LatticeCompletionPlan, decode_completion, encode_completion,
    geometric_count_envelope, plan_dense_completion, plan_lattice_completion,
)
from contingency115.tables import ComputationBudgetExceeded, TableProblem


def two_row_tables(problem):
    """Independent cell-coordinate enumeration, without a DP or codec."""
    for top in product(*(range(c+1) for c in problem.column_sums)):
        if sum(top) == problem.row_sums[0]:
            yield (top, tuple(c-x for c, x in zip(problem.column_sums, top)))


def offsets_for(plan):
    a, b = plan.original.shape
    for flat in product(range(plan.k), repeat=plan.dimension):
        yield tuple(tuple(flat[i*(b-1)+j] for j in range(b-1)) for i in range(a-1))


class LatticeCompletionTests(unittest.TestCase):
    def test_every_tiny_fine_table_and_balanced_preimages(self):
        cases = (((0, 0), (0, 0)), ((1, 1), (1, 1)),
                 ((0, 2), (1, 1)), ((1, 2), (1, 1, 1)),
                 ((0, 1), (0, 1, 0)))
        for rows, columns in cases:
            for k in (1, 2, 3) if len(columns) == 2 else (1, 2):
                plan = plan_lattice_completion(TableProblem(rows, columns), k)
                original = set(two_row_tables(plan.original))
                groups = Counter()
                for fine in two_row_tables(plan.fine):
                    decoded = decode_completion(plan, fine)
                    # Margins are checked even on rejected signed candidates.
                    self.assertEqual(tuple(map(sum, decoded.candidate)), rows)
                    self.assertEqual(tuple(sum(decoded.candidate[i][j] for i in range(2))
                                           for j in range(len(columns))), columns)
                    self.assertTrue(all(abs(x) < 2 for row in decoded.rounding_errors for x in row))
                    if decoded.accepted:
                        groups[decoded.candidate] += 1
                        self.assertEqual(encode_completion(plan, decoded.candidate, decoded.offsets), fine)
                    else:
                        self.assertIsNone(decoded.table)
                        self.assertTrue(any(x < 0 for row in decoded.candidate for x in row))
                self.assertEqual(set(groups), original)
                self.assertEqual(set(groups.values()), {k**plan.dimension})
                for table in original:
                    for offsets in offsets_for(plan):
                        fine = encode_completion(plan, table, offsets)
                        decoded = decode_completion(plan, fine)
                        self.assertEqual(decoded.table, table)
                        self.assertEqual(decoded.offsets, offsets)

    def test_random_higher_dimension_roundtrips_and_independent_prefix_residues(self):
        rng = random.Random(11512)
        for a, b in ((2, 4), (3, 3), (4, 3), (5, 6)):
            for k in (1, 2, 7, 10**30):
                for _ in range(10):
                    table = tuple(tuple(rng.randrange(5) for _ in range(b)) for _ in range(a))
                    problem = TableProblem(tuple(map(sum, table)),
                                           tuple(sum(table[i][j] for i in range(a)) for j in range(b)))
                    plan = plan_lattice_completion(problem, k)
                    offsets = tuple(tuple(rng.randrange(k) for _ in range(b-1)) for _ in range(a-1))
                    fine = encode_completion(plan, table, offsets)
                    decoded = decode_completion(plan, fine)
                    self.assertEqual(decoded.table, table)
                    self.assertEqual(decoded.offsets, offsets)
                    for i in range(a-1):
                        for j in range(b-1):
                            independent = sum(fine[r][c] for r in range(i+1) for c in range(j+1))
                            self.assertEqual(independent % k, offsets[i][j])

    def test_negative_decoding_and_sharp_rounding_error(self):
        plan = plan_lattice_completion(TableProblem((0, 0), (0, 0)), 2)
        rejected = decode_completion(plan, ((0, 8), (8, 0)))
        self.assertEqual(rejected.candidate, ((-2, 2), (2, -2)))
        self.assertFalse(rejected.accepted)
        for k in (2, 3, 101):
            plan = plan_lattice_completion(TableProblem((0, 0, 0), (0, 0, 0)), k)
            decoded = decode_completion(plan, encode_completion(plan, ((0,)*3,)*3,
                                                                 ((0, k-1), (k-1, 0))))
            self.assertEqual(decoded.rounding_errors[1][1], Fraction(-2*(k-1), k))
            self.assertLess(abs(decoded.rounding_errors[1][1]), 2)

    def test_singleton_dimensions_have_one_preimage_and_zero_rounding_error(self):
        for table in (((0, 3, 7),), ((0,), (3,), (7,)), ((0,),)):
            a, b = len(table), len(table[0])
            problem = TableProblem(tuple(map(sum, table)),
                                   tuple(sum(table[i][j] for i in range(a)) for j in range(b)))
            for k in (1, 17, 10**200):
                plan = plan_lattice_completion(problem, k)
                offsets = tuple(() for _ in range(a-1))
                fine = encode_completion(plan, table, offsets)
                decoded = decode_completion(plan, fine)
                self.assertEqual(plan.preimages_per_table, 1)
                self.assertEqual(decoded.table, table)
                self.assertEqual(decoded.offsets, offsets)
                self.assertTrue(all(x == 0 for row in decoded.rounding_errors for x in row))

    def test_dense_actual_scales_and_ambient_d(self):
        for a, b in ((1, 1), (1, 5), (2, 2), (2, 3), (3, 4)):
            for d in (10+(a+1)*(b+1), 10**30):
                table = tuple((3*d,)*b for _ in range(a))
                dense = plan_dense_completion(TableProblem((3*b*d,)*a, (3*a*d,)*b), d)
                plan = dense.codec
                self.assertEqual(plan.k, d**12)
                self.assertEqual(dense.L, 3*d)
                self.assertEqual(sum(plan.fine.row_sums), plan.k*(sum(plan.original.row_sums)+2*a*b))
                self.assertGreater(dense.conditional_acceptance_lower_bound, Fraction(1, 4))
                offsets = tuple(tuple((i+j) % 2*(plan.k-1) for j in range(b-1)) for i in range(a-1))
                self.assertEqual(decode_completion(plan, encode_completion(plan, table, offsets)).table, table)

    def test_exact_geometric_arithmetic_and_preallocation_budget(self):
        for a in range(1, 8):
            for b in range(1, 9):
                d = 10+(a+1)*(b+1)
                k = 2*d
                expected = Fraction(k*(3*d+2)+2, k*(3*d-2))**((a-1)*(b-1))
                self.assertEqual(geometric_count_envelope(a, b, d, k), expected)
                self.assertLess(expected, 4)
        with self.assertRaises(ComputationBudgetExceeded):
            geometric_count_envelope(10**9, 10**9, 10**30, 10**40, max_bound_bits=100)
        with self.assertRaises(ComputationBudgetExceeded):
            plan_dense_completion(TableProblem((10**30,)*2, (10**30,)*2), 10**20, max_bound_bits=100)

    def test_semantic_bounds_and_invalid_inputs(self):
        ordinary = TableProblem((1, 1), (1, 1))
        equivalent = TableProblem((1, 1), (1, 1), upper_bounds=((9, 9), (9, 9)),
                                  lower_bounds=((0, 0), (0, 0)))
        self.assertEqual(plan_lattice_completion(ordinary, 2), plan_lattice_completion(equivalent, 2))
        # A structural zero on a zero margin is semantically unrestricted.
        plan_lattice_completion(TableProblem((0, 1), (0, 1), structural_zeros=((0, 0),)), 2)
        for problem in (TableProblem((1, 1), (1, 1), structural_zeros=((0, 0),)),
                        TableProblem((1, 1), (1, 1), lower_bounds=((1, 0), (0, 0))),
                        TableProblem((1,), (2,))):
            with self.assertRaises(ValueError):
                plan_lattice_completion(problem, 2)
        for k in (True, 2.0, Fraction(2), "2"):
            with self.assertRaises(TypeError):
                plan_lattice_completion(ordinary, k)
        for k in (0, -1):
            with self.assertRaises(ValueError):
                plan_lattice_completion(ordinary, k)
        plan = plan_lattice_completion(ordinary, 2)
        for offsets in (((True,),), ((0.0,),), ((Fraction(0),),)):
            with self.assertRaises(TypeError):
                encode_completion(plan, ((1, 0), (0, 1)), offsets)
        for offsets in ((), ((-1,),), ((2,),), ((0, 0),)):
            with self.assertRaises(ValueError):
                encode_completion(plan, ((1, 0), (0, 1)), offsets)
        for fine in (((True, 0), (0, 0)), ((1.0, 0), (0, 0))):
            with self.assertRaises(TypeError):
                decode_completion(plan, fine)
        with self.assertRaises(ValueError):
            decode_completion(plan, ((0, 0), (0, 0)))
        with self.assertRaises(ValueError):
            LatticeCompletionPlan(ordinary, ordinary, 2)
        with self.assertRaises(ValueError):
            plan_dense_completion(ordinary)
        for args in ((2, 2, 18, 40), (2, 2, 19, 37)):
            with self.assertRaises(ValueError):
                geometric_count_envelope(*args)
        for bad in (True, 20.0, Fraction(20)):
            with self.assertRaises(TypeError):
                plan_dense_completion(ordinary, bad)


if __name__ == "__main__":
    unittest.main()
