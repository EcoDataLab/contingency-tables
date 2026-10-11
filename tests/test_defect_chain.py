"""Exact induced word laws and bounded direct-step checks on small rectangles."""

from collections import Counter, defaultdict
from fractions import Fraction as F
import unittest

from contingency115.ideal_chain import PhysicalState, build_rescaled_ideal_chain
from contingency115.kernels import ExactKernel
from contingency115.tables import ComputationBudgetExceeded, TableProblem
from contingency115.defect_chain import DefectBudget, DyadicDefectChain, integer_draw_tv


class Words:
    def __init__(self, *words):
        self.words, self.widths = iter(words), []

    def getrandbits(self, bits):
        self.widths.append(bits)
        return next(self.words)


def finite_row(chain, state):
    """Enumerate only used fair words, giving their exact probability masses."""
    law = defaultdict(F)
    channels = 1 << chain.channel_bits
    width = 1 << chain.refresh_bits
    for channel in range(channels):
        if channel == chain.h - 1:
            for receiver_word in range(width):
                for label_word in range(width):
                    result = chain.step(state, Words(channel, receiver_word, label_word))
                    law[result.state] += F(1, channels * width * width)
        else:
            result = chain.step(state, Words(channel))
            law[result.state] += F(1, channels)
    return dict(law)


def ideal_rows(chain, oracle):
    """Construct reviewed dyadic trace matrix from the independent physical graph."""
    defects = [state for state in oracle.states if not state.balanced]
    index = {state: i for i, state in enumerate(oracle.states)}
    groups = defaultdict(list)
    for state in defects:
        groups[chain.repair(state)].append(state)
    laws = []
    for state in defects:
        law = defaultdict(F)
        neighbors = [oracle.states[j] for j in oracle.neighbors[index[state]]
                     if not oracle.states[j].balanced]
        for target in neighbors:
            law[target] += chain.beta
        group = groups[chain.repair(state)]
        for target in group:
            law[target] += chain.beta / len(group)
        law[state] += 1 - chain.beta * (len(neighbors) + 1)
        laws.append(dict(law))
    return defects, laws


class DefectBackendTests(unittest.TestCase):
    def test_fixed_word_rank_exact_tv_including_zero_bits(self):
        for stop in range(1, 11):
            for bits in range(5):
                width = 1 << bits
                counts = Counter(stop * word // width for word in range(width))
                tv = sum(abs(F(counts[rank], width) - F(1, stop))
                         for rank in range(stop)) / 2
                self.assertEqual(tv, integer_draw_tv(stop, bits))
                self.assertLessEqual(tv, F(stop, 4 * width))

    def test_rectangular_finite_rows_and_ideal_symmetric_kernel(self):
        saw_stationary_drift = False
        for rows, columns, cutoff in [((2, 2), (2, 1, 1), 3), ((2, 1, 1), (2, 2), 3),
                                      ((2, 2), (2, 2), 3), ((1, 1, 1), (1, 1, 1), 2),
                                      ((1, 1, 1), (2, 1), 2), ((2, 1), (1, 1, 1), 2)]:
            problem = TableProblem(rows, columns)
            oracle = build_rescaled_ideal_chain(problem, U=cutoff, L=1)
            for bits in (0, 1, 2):
                chain = DyadicDefectChain(problem, U=cutoff, refresh_bits=bits)
                defects, ideal = ideal_rows(chain, oracle)
                matrix = tuple(tuple(row.get(target, F(0)) for target in defects) for row in ideal)
                kernel = ExactKernel(tuple(defects), matrix, (F(1, len(defects)),) * len(defects))
                self.assertTrue(kernel.is_stochastic())
                self.assertTrue(kernel.satisfies_detailed_balance())
                self.assertTrue(all(matrix[i][i] >= F(1, 2) for i in range(len(defects))))
                finite = []
                for state, target_law in zip(defects, ideal):
                    actual = finite_row(chain, state)
                    self.assertEqual(sum(actual.values()), 1)
                    self.assertTrue(set(actual) <= set(defects))
                    self.assertGreaterEqual(actual[state], F(1, 2))
                    tv = sum(abs(actual.get(target, F(0)) - target_law.get(target, F(0)))
                             for target in defects) / 2
                    support = sum(value > 0 for row in chain.repair(state) for value in row)
                    precise = chain.beta * min(F(1), integer_draw_tv(support, bits) +
                                               integer_draw_tv(chain.p - 1, bits))
                    self.assertLessEqual(tv, precise)
                    self.assertLessEqual(precise, chain.transition_tv_bound)
                    finite.append(actual)
                saw_stationary_drift |= any(sum(row.get(target, 0) for row in finite) != 1
                                           for target in defects)
        self.assertTrue(saw_stationary_drift)  # uniform stationarity really can fail

    def test_one_small_side_reaches_capacity_and_preserves_inverse_fiber(self):
        saw_x_boundary = saw_q_boundary = False
        for rows, columns in [((1, 1, 1), (2, 1)), ((2, 1), (1, 1, 1)),
                              ((1, 1, 1, 1), (3, 1)), ((3, 1), (1, 1, 1, 1))]:
            problem = TableProblem(rows, columns)
            chain = DyadicDefectChain(problem, U=2, refresh_bits=2)
            oracle = build_rescaled_ideal_chain(problem, U=2, L=1)
            self.assertTrue(oracle.all_small)
            self.assertEqual(set(oracle.completion_counts), {1})
            groups = defaultdict(set)
            for state in oracle.states:
                if not state.balanced:
                    chain.validate_state(state)
                    self.assertTrue(all(value <= 2 for value in state.row_view + state.column_view))
                    saw_x_boundary |= 2 in state.row_view
                    saw_q_boundary |= 2 in state.column_view
                    groups[chain.repair(state)].add(state)
            for table, fiber in groups.items():
                support = [i for i, value in enumerate(v for row in table for v in row) if value]
                generated = {chain.defect(table, receiver, rank) for receiver in support
                             for rank in range(chain.p - 1)}
                self.assertEqual(generated, fiber)
                self.assertEqual(len(generated), len(support) * (chain.p - 1))
        self.assertTrue(saw_x_boundary)
        self.assertTrue(saw_q_boundary)

    def test_inverse_crossing_rank_is_entire_fiber(self):
        problem = TableProblem((2, 2), (2, 1, 1))
        oracle = build_rescaled_ideal_chain(problem, U=3, L=1)
        chain = DyadicDefectChain(problem, U=3, refresh_bits=3)
        groups = defaultdict(set)
        for state in oracle.states:
            if not state.balanced:
                groups[chain.repair(state)].add(state)
        for table, fiber in groups.items():
            support = [i for i, value in enumerate(v for row in table for v in row) if value]
            generated = {chain.defect(table, receiver, rank) for receiver in support
                         for rank in range(chain.p - 1)}
            self.assertEqual(generated, fiber)
            self.assertEqual(len(generated), len(support) * (chain.p - 1))

    def test_word_order_work_counters_and_error_composition(self):
        chain = DyadicDefectChain(TableProblem((2, 2), (2, 1, 1)), U=3, refresh_bits=2)
        state = chain.defect(((2, 0, 0), (0, 1, 1)), 0, 0)
        rng = Words((1 << chain.channel_bits) - 1, chain.h - 1, 2, 3)
        result = chain.walk(state, steps=2, rng=rng)
        self.assertEqual(result.physical_steps, 2)
        self.assertEqual(result.refreshes, 1)
        self.assertEqual(result.fair_bits, 2 * chain.channel_bits + 4)
        self.assertEqual(rng.widths, [chain.channel_bits, chain.channel_bits, 2, 2])
        self.assertEqual(result.ideal_walk_tv_bound, 2 * chain.transition_tv_bound)
        zero = chain.walk(state, steps=0, rng=Words())
        self.assertEqual((zero.state, zero.physical_steps, zero.fair_bits), (state, 0, 0))

    def test_preflight_budget_failure_and_scope(self):
        problem = TableProblem((2, 2), (2, 1, 1))
        for budget in (DefectBudget(max_cells=1), DefectBudget(max_input_bits=1),
                       DefectBudget(max_fair_bits=1)):
            with self.assertRaises(ComputationBudgetExceeded):
                DyadicDefectChain(problem, U=3, refresh_bits=2, budget=budget)
        for budget in (DefectBudget(max_steps=1), DefectBudget(max_fair_bits=8)):
            chain = DyadicDefectChain(problem, U=3, refresh_bits=2, budget=budget)
            state = chain.defect(((2, 0, 0), (0, 1, 1)), 0, 0)
            rng = Words()
            with self.assertRaises(ComputationBudgetExceeded):
                chain.walk(state, steps=2, rng=rng)
            self.assertEqual(rng.widths, [])
        for problem, cutoff in [(TableProblem((2,), (1, 1)), 3),
                                (TableProblem((0, 2), (1, 1)), 3),
                                (TableProblem((2, 2), (2, 2)), 2),
                                (TableProblem((2, 2), (2, 2), structural_zeros=[(0, 0)]), 3)]:
            with self.assertRaises(ValueError):
                DyadicDefectChain(problem, U=cutoff, refresh_bits=2)

    def test_invalid_state_and_word_contracts(self):
        chain = DyadicDefectChain(TableProblem((2, 2), (2, 2)), U=3, refresh_bits=2)
        with self.assertRaises(ValueError):
            chain.validate_state(PhysicalState((1, 1, 1, 1), (1, 1, 1, 1)))
        state = chain.defect(((1, 1), (1, 1)), 0, 0)
        for word in (-1, True, 1 << chain.channel_bits):
            with self.assertRaises((TypeError, ValueError)):
                chain.step(state, Words(word))
        with self.assertRaises(ValueError):
            chain.defect(((2, 0), (0, 2)), 1, 0)

    def test_defect_terminal_stationary_law_and_fallback_composition(self):
        problem = TableProblem((2, 2), (2, 1, 1))
        oracle = build_rescaled_ideal_chain(problem, U=3, L=1)
        chain = DyadicDefectChain(problem, U=3, refresh_bits=2)
        defects, _ = ideal_rows(chain, oracle)
        ideal = defaultdict(F)
        finite = defaultdict(F)
        failure = F(0)
        bits = 1
        for state in defects:
            table = chain.repair(state)
            support = sum(value > 0 for row in table for value in row)
            ideal[table] += F(max(chain.m, chain.n), support * len(defects))
            # The terminal depends only on the repaired table. No mixing claim
            # is needed to enumerate this coin; delta=1 is an honest runtime input.
            for word in range(1 << bits):
                result = chain.sample(table, attempts=1, steps_per_attempt=0,
                                      terminal_bits=bits, endpoint_mixing_delta=1,
                                      rng=Words(word), use_fallback=False)
                if result.table is None:
                    failure += F(1, len(defects) * (1 << bits))
                else:
                    finite[table] += F(1, len(defects) * (1 << bits))
        self.assertEqual(set(ideal.values()), {F(15, len(defects))})  # defect c has no +1
        self.assertEqual(sum(finite.values()) + failure, 1)
        self.assertGreater(len(set(finite.values())), 1)
        tables = tuple(ideal)
        for attempts in (1, 3):
            law = {table: sum(finite[table] * failure ** r for r in range(attempts))
                   for table in tables}
            law[tables[0]] += failure ** attempts
            self.assertEqual(sum(law.values()), 1)
            tv = sum(abs(mass - F(1, len(tables))) for mass in law.values()) / 2
            # For independently stationary endpoints, mixing/transition terms
            # vanish: exact composition checks the remaining two allowances.
            self.assertLessEqual(tv, F(1, 4) ** attempts + F(attempts, 1 << bits))

    def test_sampler_resets_state_advances_words_and_counts_total_work(self):
        chain = DyadicDefectChain(TableProblem((2, 2), (2, 2)), U=3, refresh_bits=2)
        table = ((1, 1), (1, 1))
        initial = chain.defect(table, 0, 0)
        rng = Words(2, 1, 3, 0)
        result = chain.sample(table, attempts=3, steps_per_attempt=1, terminal_bits=1,
                              endpoint_mixing_delta=F(1, 100), rng=rng)
        self.assertEqual(result.endpoint, chain.step(initial, Words(3)).state)
        self.assertEqual(result.table, ((0, 2), (2, 0)))
        self.assertEqual((result.attempts, result.physical_steps, result.rejected_attempts), (2, 2, 1))
        self.assertEqual(result.refreshes, 0)
        self.assertEqual(result.fair_bits, 2 * (chain.channel_bits + 1))
        self.assertEqual(rng.widths, [chain.channel_bits, 1, chain.channel_bits, 1])
        self.assertFalse(result.exhausted)
        self.assertEqual(result.error.stationary_exhaustion, F(1, 2) ** 3)
        self.assertEqual(result.error.ideal_endpoint_mixing, F(3, 100))
        self.assertEqual(result.error.transition_rounding, 3 * chain.transition_tv_bound)
        self.assertEqual(result.error.terminal_rounding, F(3, 2))
        self.assertEqual(result.error.total_variation_bound, 1)

    def test_sampler_exhaustion_fallback_zero_bits_and_preflight(self):
        problem = TableProblem((2, 2), (2, 2))
        table = ((1, 1), (1, 1))
        chain = DyadicDefectChain(problem, U=3, refresh_bits=2)
        result = chain.sample(table, attempts=2, steps_per_attempt=0, terminal_bits=0,
                              endpoint_mixing_delta=1, rng=Words())
        self.assertTrue(result.exhausted)
        self.assertTrue(result.fallback_used)
        self.assertEqual(result.table, table)
        self.assertEqual((result.attempts, result.rejected_attempts, result.fair_bits), (2, 2, 0))
        no_output = chain.sample(table, attempts=2, steps_per_attempt=0, terminal_bits=0,
                                 endpoint_mixing_delta=1, rng=Words(), use_fallback=False)
        self.assertIsNone(no_output.table)
        self.assertTrue(no_output.exhausted)
        self.assertFalse(no_output.fallback_used)
        accepted = chain.sample(((2, 0), (0, 2)), attempts=2, steps_per_attempt=0,
                                terminal_bits=0, endpoint_mixing_delta=1, rng=Words())
        self.assertFalse(accepted.exhausted)
        self.assertEqual(accepted.attempts, 1)
        for budget in (DefectBudget(max_attempts=1), DefectBudget(max_steps=1),
                       DefectBudget(max_fair_bits=10)):
            limited = DyadicDefectChain(problem, U=3, refresh_bits=2, budget=budget)
            rng = Words()
            with self.assertRaises(ComputationBudgetExceeded):
                limited.sample(table, attempts=2, steps_per_attempt=1, terminal_bits=1,
                               endpoint_mixing_delta=1, rng=rng)
            self.assertEqual(rng.widths, [])
        with self.assertRaises(ValueError):
            chain.sample(((0, 0), (0, 0)), attempts=1, steps_per_attempt=1,
                         terminal_bits=1, endpoint_mixing_delta=1, rng=Words())
        for delta in (-1, F(11, 10), 0.1):
            with self.assertRaises((TypeError, ValueError)):
                chain.sample(table, attempts=1, steps_per_attempt=0, terminal_bits=1,
                             endpoint_mixing_delta=delta, rng=Words())


if __name__ == "__main__":
    unittest.main()
