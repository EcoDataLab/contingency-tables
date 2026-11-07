"""Exact joint-law evidence and bounded execution checks for the terminal."""

from collections import Counter, defaultdict
from dataclasses import FrozenInstanceError
from fractions import Fraction as F
import unittest

from contingency115.general_defect_chain import CompletionOracleContract, GeneralDefectChain
from contingency115.general_defect_terminal import GeneralRepairTerminal
from contingency115.ideal_chain import PhysicalState, build_rescaled_ideal_chain
from contingency115.tables import ComputationBudgetExceeded, ExactTableSampler, TableProblem


class Words:
    def __init__(self, *words):
        self.words, self.widths = iter(words), []

    def getrandbits(self, bits):
        self.widths.append(bits)
        return next(self.words)


class SuppliedCompletion:
    """Diagnostic selector; joint tests enumerate its input, not a uniform draw."""
    contract = CompletionOracleContract(0, 0, 1)

    def __init__(self):
        self.completion, self.calls = None, 0

    def draw(self, request, context):
        self.calls += 1
        context.charge(1)
        return self.completion


def backend(problem, oracle, U=2, L=3):
    return GeneralDefectChain(problem, U=U, L=L, oracle=oracle, geometry_bits=4, star_trials=0)


class GeneralTerminalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.problem = TableProblem((2, 2, 1), (2, 2, 1))
        cls.exact = build_rescaled_ideal_chain(cls.problem, U=2, L=3)
        cls.defects = [(state, completion)
                       for state, completions in zip(cls.exact.states, cls.exact.completions)
                       if not state.balanced for completion in completions]

    def test_actual_weighted_joint_fibers_and_entire_finite_stationary_law(self):
        oracle = SuppliedCompletion()
        chain = backend(self.problem, oracle)
        high = GeneralRepairTerminal(chain, acceptance_bits=16)
        # Enumerating the existing physical reference backend is confined to
        # this test. Equal joint masses = weighted state law + uniform completion.
        weights = [len(completions) for state, completions in zip(self.exact.states, self.exact.completions)
                   if not state.balanced]
        self.assertGreater(len(set(weights)), 1)
        observed, fibers, joint_outputs = Counter(), {}, []
        unpadding = small_crossing = large_crossing = False
        for state, completion in self.defects:
            oracle.completion = completion
            result = high.terminal(state, Words(0))
            if result.outcome == "unpadding_rejection":
                unpadding = True
                self.assertIsNone(result.fiber_size)
                joint_outputs.append(None)
                continue
            self.assertEqual(result.outcome, "accepted")
            observed[result.table] += 1
            fibers[result.table] = result.fiber_size
            joint_outputs.append(result.table)
            repaired = chain.repair(state)
            large_crossing |= chain.repair_crossing(state) not in chain.locations
            small_crossing |= chain.repair_crossing(state) in chain.locations
            crossing = chain.repair_crossing(state)
            for ri, i in enumerate(chain.large_rows):
                for cj, j in enumerate(chain.large_columns):
                    self.assertEqual(result.table[i][j]+chain.L,
                                     completion[ri][cj]+int(crossing == (i, j)))
        independent = set(ExactTableSampler(self.problem).tables())
        self.assertEqual(set(observed), independent)
        self.assertEqual(dict(observed), fibers)
        self.assertTrue(unpadding and small_crossing and large_crossing)
        ideal = {table: F(count*high.fiber_lower_bound, fibers[table]*len(self.defects))
                 for table, count in observed.items()}
        self.assertEqual(set(ideal.values()), {F(high.fiber_lower_bound, len(self.defects))})
        self.assertGreater(len(set(fibers.values())), 1)
        # Exhaust all words. Compare the full successful law and None mass,
        # retaining the real varying weights rather than treating profiles equally.
        for bits in range(4):
            terminal = GeneralRepairTerminal(chain, acceptance_bits=bits)
            law, failed = defaultdict(F), F(0)
            for (state, completion), expected_table in zip(self.defects, joint_outputs):
                oracle.completion = completion
                for word in range(1 << bits):
                    rng = Words(word)
                    result = terminal.terminal(state, rng)
                    mass = F(1, len(self.defects)*(1 << bits))
                    if result.table is None:
                        failed += mass
                    else:
                        self.assertEqual(result.table, expected_table)
                        law[result.table] += mass
                    self.assertEqual(rng.widths, [bits] if bits and expected_table is not None else [])
            expected = {table: F(count*((terminal.fiber_lower_bound << bits)//fibers[table]),
                                  len(self.defects)*(1 << bits))
                        for table, count in observed.items()}
            self.assertEqual(dict(law), {table: mass for table, mass in expected.items() if mass})
            self.assertEqual(failed, 1-sum(expected.values()))
            self.assertLess(sum(ideal.values())-sum(expected.values()), F(1, 1 << bits))
            self.assertEqual(terminal.error.total_variation_bound, F(1, 1 << bits))
            if bits == 3:
                self.assertGreater(len(set(law.values())), 1)  # Accepted finite law really can be biased.

    def test_positive_padded_entries_do_not_replace_zero_ordinary_slack(self):
        problem = TableProblem((2, 1, 1), (2, 1, 1))
        oracle = SuppliedCompletion()
        chain = backend(problem, oracle, L=1)
        terminal = GeneralRepairTerminal(chain, acceptance_bits=8)
        exact = build_rescaled_ideal_chain(problem, U=2, L=1)
        observed, fibers = Counter(), {}
        zero_slack = False
        for state, completions in zip(exact.states, exact.completions):
            if state.balanced:
                continue
            for completion in completions:
                oracle.completion = completion
                result = terminal.terminal(state, Words(0))
                if result.table is None:
                    continue
                observed[result.table] += 1
                fibers[result.table] = result.fiber_size
                repaired = chain.repair(state)
                rr, cc = chain.residual_margins(repaired)
                if rr == (chain.L,) and cc == (chain.L,):
                    zero_slack = True
                    self.assertEqual(result.table[0][0], 0)
                    # abuv is zero despite the repaired padded entry being L.
                    d0 = sum((2 if i == 0 else 3)*(2 if j == 0 else 3)-1
                             for (i, j), value in zip(chain.cells, repaired.row_view) if value)
                    self.assertEqual(result.fiber_size, d0)
        self.assertTrue(zero_slack)
        self.assertEqual(dict(observed), fibers)
        self.assertEqual(set(observed), set(ExactTableSampler(problem).tables()))

    def test_unit_branch_both_or_one_side_small_and_no_oracle(self):
        for rows, columns in [((2, 2), (2, 2)), ((2, 2), (3, 1)), ((3, 1), (2, 2))]:
            problem = TableProblem(rows, columns)
            oracle = SuppliedCompletion()
            oracle.contract = CompletionOracleContract(F(1, 2), 100, 1)
            chain = backend(problem, oracle, U=3, L=1)
            terminal = GeneralRepairTerminal(chain, acceptance_bits=8, max_fair_bits=8)
            self.assertTrue(chain.unit_branch)
            self.assertEqual(terminal.fiber_lower_bound, (chain.p-1)*max(chain.m, chain.n))
            exact = build_rescaled_ideal_chain(problem, U=3, L=1)
            counts = Counter()
            for state in exact.states:
                if state.balanced:
                    continue
                result = terminal.terminal(state, Words(0))
                self.assertEqual((result.oracle_calls, result.oracle_work, result.fair_bits), (0, 0, 8))
                self.assertEqual(result.error.completion_oracle, 0)
                counts[result.table] += 1
                self.assertLessEqual(terminal.fiber_lower_bound, result.fiber_size)
            self.assertEqual(set(counts), set(ExactTableSampler(problem).tables()))
            self.assertEqual(oracle.calls, 0)

    def test_shared_stream_oracle_failure_and_completion_snapshot(self):
        class BitOracle(SuppliedCompletion):
            contract = CompletionOracleContract(F(1, 8), 2, 1)

            def draw(self, request, context):
                self.calls += 1
                self.selected = context.word(2)
                context.charge(1)
                return self.completion

        oracle = BitOracle()
        chain = backend(self.problem, oracle)
        terminal = GeneralRepairTerminal(chain, acceptance_bits=3, max_fair_bits=5)
        # Pick a successful pair using the deterministic fixture, then use a
        # mutable completion container to check the returned table is a snapshot.
        selector = SuppliedCompletion()
        finder = GeneralRepairTerminal(backend(self.problem, selector), acceptance_bits=3)
        state, completion = next((state, completion) for state, completion in self.defects
                                 if self._accepts(finder, selector, state, completion))
        oracle.completion = [list(row) for row in completion]
        rng = Words(2, 0)
        result = terminal.terminal(state, rng)
        self.assertEqual(rng.widths, [2, 3])
        self.assertEqual((result.fair_bits, result.oracle_calls, result.oracle_work), (5, 1, 1))
        self.assertEqual(result.error.total_variation_bound, F(1, 4))
        saved = result.table
        oracle.completion[0][0] += 100
        self.assertEqual(result.table, saved)
        with self.assertRaises(FrozenInstanceError):
            result.table = None
        with self.assertRaises(FrozenInstanceError):
            terminal.acceptance_bits = 100
        oracle.completion = None
        failed_rng = Words(1)
        failed = terminal.terminal(state, failed_rng)
        self.assertEqual((failed.table, failed.outcome, failed.fair_bits), (None, "oracle_failure", 2))
        self.assertEqual(failed_rng.widths, [2])
        self.assertIsNone(failed.fiber_size)

        class MutatingOracle(SuppliedCompletion):
            def draw(self, request, context):
                self.original.row_view[0] = 100
                self.original.column_view[0] = 100
                return self.completion

        mutator = MutatingOracle()
        mutator.original = PhysicalState(list(state.row_view), list(state.column_view))
        mutator.completion = completion
        mutating_terminal = GeneralRepairTerminal(backend(self.problem, mutator), acceptance_bits=3)
        self.assertEqual(mutating_terminal.terminal(mutator.original, Words(0)).table, saved)

    @staticmethod
    def _accepts(terminal, oracle, state, completion):
        oracle.completion = completion
        return terminal.terminal(state, Words(0)).table is not None

    def test_preflight_bit_cap_and_scope(self):
        oracle = SuppliedCompletion()
        oracle.contract = CompletionOracleContract(0, 7, 1)
        chain = backend(self.problem, oracle)
        for bits, cap in [(3, 9), (1_000_000_000, 10)]:
            with self.assertRaises(ComputationBudgetExceeded):
                GeneralRepairTerminal(chain, acceptance_bits=bits, max_fair_bits=cap)
        self.assertEqual(oracle.calls, 0)
        for bits in [True, 0.5, -1]:
            with self.assertRaises((ValueError, TypeError)):
                GeneralRepairTerminal(chain, acceptance_bits=bits)
        for cap in [True, 0.5, -1]:
            with self.assertRaises((ValueError, TypeError)):
                GeneralRepairTerminal(chain, acceptance_bits=1, max_fair_bits=cap)
        with self.assertRaises(TypeError):
            GeneralRepairTerminal(object(), acceptance_bits=1)
        zero = backend(TableProblem((2, 0, 0), (2, 0, 0)), oracle, L=1)
        with self.assertRaisesRegex(ValueError, "positive ordinary"):
            GeneralRepairTerminal(zero, acceptance_bits=1)
        terminal = GeneralRepairTerminal(chain, acceptance_bits=1)
        rng = Words(0)
        for state in [PhysicalState((0,)*chain.p, (0,)*chain.p),
                      PhysicalState((True,)*chain.p, (0,)*chain.p)]:
            with self.assertRaises((ValueError, TypeError)):
                terminal.terminal(state, rng)
        self.assertEqual(rng.widths, [])
        self.assertEqual(oracle.calls, 0)

    def test_suspect_words_and_malformed_completion(self):
        oracle = SuppliedCompletion()
        terminal = GeneralRepairTerminal(backend(self.problem, oracle), acceptance_bits=3)
        state, completion = next((state, completion) for state, completion in self.defects
                                 if self._accepts(terminal, oracle, state, completion))
        oracle.completion = completion
        for word in [True, -1, 0.5, 8]:
            with self.assertRaises((ValueError, TypeError)):
                terminal.terminal(state, Words(word))
        with self.assertRaises(TypeError):
            terminal.terminal(state, object())
        for value in [(), ((True,),), ((-1,),), ((1000,),)]:
            oracle.completion = value
            rng = Words(0)
            with self.assertRaises((ValueError, TypeError)):
                terminal.terminal(state, rng)
            self.assertEqual(rng.widths, [])


if __name__ == "__main__":
    unittest.main()
