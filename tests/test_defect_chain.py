"""Exact induced word laws and bounded direct-step checks on small rectangles."""

from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
import unittest
from unittest.mock import patch

from contingency115.ideal_chain import PhysicalState, build_rescaled_ideal_chain
from contingency115.kernels import ExactKernel
from contingency115.tables import ComputationBudgetExceeded, TableProblem
from contingency115.defect_chain import (
    DefectBudget, DyadicDefectChain, both_small_spaced_schedule, integer_draw_tv,
)


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

    def test_spaced_complete_word_law_keeps_rejected_state(self):
        """Compare all used words with an independent finite-kernel composition."""
        chain = DyadicDefectChain(TableProblem((2, 2), (2, 2)), U=3, refresh_bits=0)
        table = ((1, 1), (1, 1))
        initial = chain.defect(table, 0, 0)
        channels = 1 << chain.channel_bits
        expected, restarted = defaultdict(F), defaultdict(F)
        first = finite_row(chain, initial)
        for state, mass in first.items():
            repaired = chain.repair(state)
            accept = F((2 << 1) // sum(v > 0 for row in repaired for v in row), 2)
            expected[repaired] += mass * accept
            restarted[repaired] += mass * accept
            for law, output in ((finite_row(chain, state), expected), (first, restarted)):
                for target, probability in law.items():
                    result = chain.repair(target)
                    success = F((2 << 1) // sum(v > 0 for row in result for v in row), 2)
                    output[result] += mass * (1 - accept) * probability * success
                    output[table] += mass * (1 - accept) * probability * (1 - success)
        actual = {method: Counter() for method in ("hybrid", "resolvent")}
        gap = both_small_spaced_schedule(chain.problem, U=3, epsilon=F(1, 8)).inverse_gap_bound
        for ch1, coin1, ch2, coin2 in product(range(channels), range(2), range(channels), range(2)):
            for method in actual:
                result = chain.sample_spaced(
                    table, attempts=2, burnin_steps=1, spacing_steps=1, terminal_bits=1,
                    burnin_mixing_delta=1,
                    spacing_l2_contraction=1 if method == "hybrid" else 1 - F(1, gap),
                    bound_method=method, rng=Words(ch1, coin1, ch2, coin2))
                actual[method][result.table] += 1
                self.assertEqual(result.physical_steps, result.attempts)
                self.assertEqual(result.fair_bits, result.attempts * (chain.channel_bits + 1))
        self.assertEqual(sum(expected.values()), 1)
        for counts in actual.values():
            self.assertEqual({key: F(value, 4 * channels**2) for key, value in counts.items()}, dict(expected))
        self.assertEqual(actual["hybrid"], actual["resolvent"])
        self.assertNotEqual(expected, restarted)

    def test_spaced_error_budget_preflight_and_zero_spacing(self):
        problem = TableProblem((2, 2), (2, 2))
        table = ((1, 1), (1, 1))
        chain = DyadicDefectChain(problem, U=3, refresh_bits=2)
        rng = Words(1, 1, 1)
        result = chain.sample_spaced(
            table, attempts=3, burnin_steps=0, spacing_steps=0, terminal_bits=1,
            burnin_mixing_delta=F(1, 10), spacing_l2_contraction=F(1, 4), rng=rng)
        self.assertTrue(result.fallback_used)
        self.assertEqual(result.table, table)
        self.assertEqual(result.physical_steps, 0)
        self.assertEqual(rng.widths, [1, 1, 1])
        self.assertEqual(result.error.ideal_endpoint_mixing, F(1, 10) + F(2, 16))
        self.assertEqual(result.error.transition_rounding, 0)
        # This deliberately supplied contraction is only an input-contract test;
        # it is not a valid contraction certificate for zero spacing steps.
        for budget in (DefectBudget(max_attempts=1), DefectBudget(max_steps=3),
                       DefectBudget(max_fair_bits=10)):
            limited = DyadicDefectChain(problem, U=3, refresh_bits=2, budget=budget)
            rng = Words()
            with self.assertRaises(ComputationBudgetExceeded):
                limited.sample_spaced(table, attempts=2, burnin_steps=2, spacing_steps=2,
                    terminal_bits=1, burnin_mixing_delta=1, spacing_l2_contraction=1, rng=rng)
            self.assertEqual(rng.widths, [])
        for name in ("burnin_mixing_delta", "spacing_l2_contraction"):
            for invalid in (-1, F(11, 10), 0.1):
                kwargs = dict(burnin_mixing_delta=1, spacing_l2_contraction=1)
                kwargs[name] = invalid
                with self.assertRaises((TypeError, ValueError)):
                    chain.sample_spaced(table, attempts=1, burnin_steps=0, spacing_steps=0,
                                        terminal_bits=1, rng=Words(), **kwargs)

    def test_spaced_schedule_exact_error_allocations_and_scope(self):
        for problem in (TableProblem((2, 2), (2, 1, 1)),
                        TableProblem((2, 1, 1), (2, 2))):
            for epsilon in (F(1, 8), F(7, 8), F(1, 1000)):
                schedule = both_small_spaced_schedule(problem, U=3, epsilon=epsilon)
                chain = DyadicDefectChain(problem, U=3, refresh_bits=schedule.refresh_bits)
                a, b = min(problem.shape), max(problem.shape)
                support = min(chain.p, sum(problem.row_sums))
                exhaustion = (1 - F(b, support)) ** schedule.attempts
                mixing = schedule.burnin_mixing_delta + (schedule.attempts - 1) * schedule.spacing_l2_contraction / 4
                rounding = schedule.planned_steps * chain.transition_tv_bound
                terminal = F(schedule.attempts, 1 << schedule.terminal_bits)
                self.assertLessEqual(exhaustion, epsilon / 4)
                self.assertLessEqual(mixing, epsilon / 4)
                self.assertLessEqual(rounding, epsilon / 4)
                self.assertLessEqual(terminal, epsilon / 4)
                self.assertEqual(schedule.planned_steps,
                                 schedule.burnin_steps + (schedule.attempts - 1) * schedule.spacing_steps)
                self.assertEqual(schedule.planned_fair_bits,
                                 schedule.planned_steps * chain.max_bits_per_step + schedule.attempts * schedule.terminal_bits)
                self.assertEqual(schedule.burnin_mixing_delta,
                                 F(1, 2 << (schedule.attempts // a)))
        with self.assertRaises(ValueError):
            both_small_spaced_schedule(TableProblem((1, 1, 1), (2, 1)), U=2, epsilon=F(1, 8))
        for epsilon in (0, 1, 2):
            with self.assertRaises(ValueError):
                both_small_spaced_schedule(TableProblem((2, 2), (2, 2)), U=3, epsilon=epsilon)

    def test_resolvent_schedule_certificate_and_plan_dominance(self):
        saw_strict_gain = False
        for problem in (TableProblem((2, 2), (2, 2)),
                        TableProblem((2, 2), (2, 1, 1)),
                        TableProblem((2, 1, 1), (2, 2)),
                        TableProblem((2, 2), (1, 1, 1, 1))):
            for epsilon in (F(1, 8), F(7, 8), F(1, 1000)):
                old = both_small_spaced_schedule(problem, U=3, epsilon=epsilon)
                self.assertEqual(old, both_small_spaced_schedule(
                    problem, U=3, epsilon=epsilon, bound_method="hybrid"))
                new = both_small_spaced_schedule(
                    problem, U=3, epsilon=epsilon, bound_method="resolvent")
                self.assertEqual(new.bound_method, "resolvent")
                self.assertEqual(new.attempts, old.attempts)
                self.assertEqual(new.burnin_steps, old.burnin_steps)
                self.assertLessEqual(new.spacing_steps, old.spacing_steps)
                self.assertLessEqual(new.planned_steps, old.planned_steps)
                self.assertLessEqual(new.planned_fair_bits, old.planned_fair_bits)
                saw_strict_gain |= new.planned_steps < old.planned_steps
                chain = DyadicDefectChain(problem, U=3, refresh_bits=new.refresh_bits)
                success = F(max(problem.shape), min(chain.p, sum(problem.row_sums)))
                rho = new.spacing_l2_contraction
                failure = (1 - (1 - rho) * success) ** new.attempts
                mixing = new.burnin_mixing_delta + rho / (2 * (1 - rho) ** 2)
                rounding = new.planned_steps * chain.transition_tv_bound
                terminal = F(new.attempts, 1 << new.terminal_bits)
                for allowance in (failure, mixing, rounding, terminal):
                    self.assertLessEqual(allowance, epsilon / 4)
                self.assertLessEqual(failure + mixing + rounding + terminal, epsilon)
        self.assertTrue(saw_strict_gain)

    def test_resolvent_pairs_failure_bias_and_finite_word_allowances(self):
        problem = TableProblem((2, 2), (2, 2))
        table = ((1, 1), (1, 1))
        chain = DyadicDefectChain(problem, U=3, refresh_bits=2)
        gap = both_small_spaced_schedule(problem, U=3, epsilon=F(1, 8)).inverse_gap_bound
        rho = 1 - F(1, gap)  # valid ideal one-step contraction from the gap allowance
        hold = (1 << chain.channel_bits) - 1
        results = []
        for method in ("hybrid", "resolvent"):
            rng = Words(hold, hold, 1, hold, 1, hold, 1)
            result = chain.sample_spaced(
                table, attempts=3, burnin_steps=2, spacing_steps=1, terminal_bits=1,
                burnin_mixing_delta=1, spacing_l2_contraction=rho,
                bound_method=method, rng=rng)
            self.assertTrue(result.fallback_used)
            self.assertEqual(result.table, table)
            self.assertEqual(result.physical_steps, 4)
            self.assertEqual(rng.widths, [chain.channel_bits, chain.channel_bits, 1,
                                           chain.channel_bits, 1, chain.channel_bits, 1])
            self.assertEqual(result.error.transition_rounding, 4 * chain.transition_tv_bound)
            self.assertEqual(result.error.terminal_rounding, F(3, 2))
            results.append(result)
        self.assertEqual(results[0].error.stationary_exhaustion, F(1, 8))
        self.assertEqual(results[1].error.stationary_exhaustion, (1 - (1 - rho) / 2) ** 3)
        self.assertEqual(results[1].error.ideal_endpoint_mixing,
                         1 + rho / (2 * (1 - rho) ** 2))
        self.assertGreater(results[1].error.stationary_exhaustion,
                           results[0].error.stationary_exhaustion)

    def test_resolvent_contracts_and_budget_preflight_before_powers(self):
        problem = TableProblem((2, 2), (2, 2))
        table = ((1, 1), (1, 1))
        chain = DyadicDefectChain(problem, U=3, refresh_bits=2)
        for method, rho in (("resolvent", F(1)), ("unknown", F(1, 4)), (None, F(1, 4))):
            rng = Words()
            with self.assertRaises((TypeError, ValueError)):
                chain.sample_spaced(table, attempts=1, burnin_steps=0, spacing_steps=0,
                    terminal_bits=1, burnin_mixing_delta=1, spacing_l2_contraction=rho,
                    bound_method=method, rng=rng)
            self.assertEqual(rng.widths, [])
        for method in ("unknown", None):
            with self.assertRaises((TypeError, ValueError)):
                both_small_spaced_schedule(problem, U=3, epsilon=F(1, 8), bound_method=method)
        limited = DyadicDefectChain(problem, U=3, refresh_bits=2,
                                    budget=DefectBudget(max_attempts=1))
        rng = Words()
        with patch.object(F, "__pow__", side_effect=AssertionError("power before preflight")):
            with self.assertRaises(ComputationBudgetExceeded):
                limited.sample_spaced(table, attempts=10, burnin_steps=0, spacing_steps=0,
                    terminal_bits=1, burnin_mixing_delta=1, spacing_l2_contraction=F(1, 4),
                    bound_method="resolvent", rng=rng)
        self.assertEqual(rng.widths, [])


if __name__ == "__main__":
    unittest.main()
