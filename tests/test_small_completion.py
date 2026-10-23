"""Independent exact-fiber and complete finite-word law checks."""

from collections import Counter
from fractions import Fraction as F
from itertools import product
import unittest

from contingency115.general_defect_chain import (
    CompletionContext, CompletionRequest, _Execution,
)
from contingency115.small_completion import SmallCompletionOracle
from contingency115.tables import (
    ComputationBudgetExceeded, ExactTableSampler, InfeasibleTableError, TableProblem,
)


class Words:
    def __init__(self, word=0):
        self.value, self.widths = word, []

    def getrandbits(self, bits):
        self.widths.append(bits)
        return self.value


def draw(oracle, request, word=0):
    source = Words(word)
    context = CompletionContext(_Execution(source, oracle.contract.max_fair_bits), oracle.contract)
    table = oracle.draw(request, context)
    return table, context, source


class SmallCompletionTests(unittest.TestCase):
    def test_complete_word_laws_against_independent_exact_sampler(self):
        cases = (
            ((0, 0), (0, 0), 0), ((2, 2), (2, 2), 2),
            ((3, 3), (3, 3), 3), ((5, 5), (5, 5), 3),
            ((4, 2), (3, 3), 3), ((2, 4), (4, 2), 3),
            ((0, 3), (1, 2), 2), ((4, 4), (4, 4), 2),
        )
        for rows, columns, capacity in cases:
            request = CompletionRequest(rows, columns, capacity)
            problem = TableProblem(rows, columns, upper_bounds=((capacity,)*2,)*2)
            exact = ExactTableSampler(problem)
            tables = tuple(exact.unrank(i) for i in range(exact.count()))
            for bits in range(5):
                oracle = SmallCompletionOracle(max_margin=5, word_bits=bits, max_cells=4)
                width = 1 << bits
                counts = Counter(draw(oracle, request, w)[0] for w in range(width))
                self.assertTrue(set(counts) <= set(tables))
                self.assertEqual(sum(counts.values()), width)
                tv = sum(abs(F(counts[t], width)-F(1, len(tables))) for t in tables)/2
                self.assertEqual(tv, oracle.request_tv_error(request))
                self.assertLessEqual(tv, oracle.contract.tv_error)
                # Lexicographic exact ranks independently verify both interval
                # endpoints and the floor-rank finite-word partition.
                for w in range(width):
                    table, context, source = draw(oracle, request, w)
                    self.assertEqual(table, tables[len(tables)*w//width])
                    self.assertEqual(context.work_units, 26)
                    self.assertEqual(context.fair_bits, bits if len(tables) > 1 else 0)
                    self.assertEqual(source.widths, [bits] if bits and len(tables) > 1 else [])

    def test_every_tiny_capacity_fiber_and_infeasible_requests(self):
        oracle = SmallCompletionOracle(max_margin=4, word_bits=3, max_cells=4)
        for rows in product(range(5), repeat=2):
            for c0 in range(5):
                c1 = sum(rows)-c0
                if not 0 <= c1 <= 4:
                    continue
                columns = (c0, c1)
                for capacity in range(4):
                    request = CompletionRequest(rows, columns, capacity)
                    exact = ExactTableSampler(TableProblem(rows, columns,
                        upper_bounds=((capacity,)*2,)*2))
                    size = exact.count()
                    if not size:
                        self.assert_rejects_without_rng(oracle, request, InfeasibleTableError)
                    else:
                        for word in range(8):
                            table, _, _ = draw(oracle, request, word)
                            self.assertEqual(table, exact.unrank(size*word//8))

    def test_empty_and_unique_fibers_use_no_words(self):
        oracle = SmallCompletionOracle(max_margin=9, word_bits=11, max_cells=10)
        cases = (
            ((), (), 0, ()), ((), (0, 0, 0), 0, ()),
            ((0, 0), (), 0, ()), ((0,), (0,), 0, ((0,),)),
            ((9,), (1, 0, 3, 5), 5, ((1, 0, 3, 5),)),
            ((1, 0, 3, 5), (9,), 5, ((1,), (0,), (3,), (5,))),
            ((2, 2), (2, 2), 1, ((1, 1), (1, 1))),
        )
        for rows, columns, capacity, expected in cases:
            request = CompletionRequest(rows, columns, capacity)
            table, context, source = draw(oracle, request, -1)
            self.assertEqual(table, expected)
            self.assertEqual((context.fair_bits, source.widths), (0, []))
            self.assertEqual(oracle.request_tv_error(request), 0)
        zero = SmallCompletionOracle(max_margin=0, word_bits=0)
        self.assertEqual(zero.contract.tv_error, 0)

    def assert_rejects_without_rng(self, oracle, request, exception):
        source = Words()
        context = CompletionContext(_Execution(source, oracle.contract.max_fair_bits), oracle.contract)
        with self.assertRaises(exception):
            oracle.draw(request, context)
        self.assertEqual(source.widths, [])
        self.assertLessEqual(context.work_units, oracle.contract.max_work_units)

    def test_input_validation_and_declared_limits(self):
        oracle = SmallCompletionOracle(max_margin=8, word_bits=5, max_input_bits=16, max_cells=6)
        # Immutable requests reject malformed inputs at construction; feasible
        # but unsupported/out-of-contract requests reject at the oracle seam.
        for rows, columns, capacity, exception in (
            ((True,), (1,), 1, TypeError),
            ((1,), (1,), True, TypeError),
            ((1.0,), (1,), 1, TypeError),
            ((1,), iter((1,)), 1, TypeError),
            ((-1,), (0,), 1, ValueError),
            ((0,), (0,), -1, ValueError),
            ((1,), (0,), 1, InfeasibleTableError),
            ((), (1,), 1, InfeasibleTableError),
        ):
            with self.assertRaises(exception):
                CompletionRequest(rows, columns, capacity)
        cases = (
            (None, TypeError),
            (CompletionRequest((2,), (2,), 1), InfeasibleTableError),
            (CompletionRequest((0, 0), (0, 0, 0), 0), ValueError),
            (CompletionRequest((0,), (0,)*7, 0), ComputationBudgetExceeded),
            (CompletionRequest((), (0,)*7, 0), ComputationBudgetExceeded),
            (CompletionRequest((9,), (9,), 9), ComputationBudgetExceeded),
            (CompletionRequest((0,), (0,), 1 << 16), ComputationBudgetExceeded),
        )
        for request, exception in cases:
            self.assert_rejects_without_rng(oracle, request, exception)
        bit_limited = SmallCompletionOracle(max_margin=8, word_bits=2, max_input_bits=8)
        self.assert_rejects_without_rng(bit_limited,
            CompletionRequest((4, 4), (4, 4), 4), ComputationBudgetExceeded)
        for kwargs, exception in (
            ({"max_margin": True, "word_bits": 2}, TypeError),
            ({"max_margin": 1, "word_bits": -1}, ValueError),
            ({"max_margin": 1, "word_bits": True}, TypeError),
            ({"max_margin": 1, "word_bits": 4, "max_word_bits": 3}, ComputationBudgetExceeded),
            ({"max_margin": 8, "word_bits": 2, "max_input_bits": 3}, ComputationBudgetExceeded),
            ({"max_margin": 1, "word_bits": 2, "max_cells": 0}, ValueError),
        ):
            with self.assertRaises(exception):
                SmallCompletionOracle(**kwargs)

    def test_request_snapshots_mutable_margin_lists(self):
        rows, columns = [2, 2], [2, 2]
        request = CompletionRequest(rows, columns, 2)
        rows[0], columns[0] = 100, 100
        oracle = SmallCompletionOracle(max_margin=2, word_bits=3, max_cells=4)
        self.assertEqual(request.row_sums, (2, 2))
        self.assertEqual(request.column_sums, (2, 2))
        self.assertEqual(draw(oracle, request, 0)[0], ((0, 2), (2, 0)))

    def test_huge_margin_uses_one_bounded_word_and_no_fiber_enumeration(self):
        margin = 10**200
        oracle = SmallCompletionOracle(max_margin=margin, word_bits=700, max_cells=4)
        request = CompletionRequest((margin, margin), (margin, margin), margin)
        word = (1 << 699)+13
        table, context, source = draw(oracle, request, word)
        x = (margin+1)*word//(1 << 700)
        self.assertEqual(table, ((x, margin-x), (margin-x, x)))
        self.assertEqual((context.fair_bits, context.work_units, source.widths), (700, 26, [700]))
        self.assertLessEqual(oracle.request_tv_error(request), oracle.contract.tv_error)

    def test_context_enforces_work_and_word_caps(self):
        oracle = SmallCompletionOracle(max_margin=2, word_bits=4, max_cells=4)
        request = CompletionRequest((2, 2), (2, 2), 2)
        for word, exception in ((True, TypeError), (-1, ValueError), (16, ValueError)):
            with self.assertRaises(exception):
                draw(oracle, request, word)
        context = CompletionContext(_Execution(Words(), 3), oracle.contract)
        with self.assertRaises(ComputationBudgetExceeded):
            oracle.draw(request, context)
        context = CompletionContext(_Execution(Words(), 4), oracle.contract)
        context.charge(oracle.contract.max_work_units)
        with self.assertRaises(ComputationBudgetExceeded):
            oracle.draw(request, context)


if __name__ == "__main__":
    unittest.main()
