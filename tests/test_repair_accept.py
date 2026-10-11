"""Exact terminal laws, actual walker reuse, and bounded execution semantics."""

from collections import Counter, defaultdict
from dataclasses import replace
from fractions import Fraction as F
import random
import unittest

from contingency115.ideal_chain import PhysicalState, build_rescaled_ideal_chain
from contingency115.repair_accept import RepairAcceptBudget, RepairAcceptRule
from contingency115.tables import ComputationBudgetExceeded, ExactTableSampler, TableProblem


class Words:
    def __init__(self, *words):
        self.words = iter(words)
        self.widths = []

    def getrandbits(self, bits):
        self.widths.append(bits)
        return next(self.words)


class RepairAcceptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.chain = build_rescaled_ideal_chain(TableProblem((2, 2), (2, 2)), U=3, L=1)
        cls.rule = RepairAcceptRule(cls.chain)
        cls.dense = cls.chain.states.index(PhysicalState((1, 1, 1, 1), (1, 1, 1, 1)))
        cls.sparse = cls.chain.states.index(PhysicalState((2, 0, 0, 2), (2, 0, 0, 2)))

    def test_repair_fibers_and_ideal_stationary_law(self):
        for rows, columns in [((2, 2), (2, 2)), ((2, 2), (2, 1, 1)),
                              ((1, 1, 1), (1, 1, 1)), ((2,), (1, 1))]:
            chain = build_rescaled_ideal_chain(TableProblem(rows, columns),
                                              U=max(rows + columns) + 1, L=1)
            rule = RepairAcceptRule(chain)
            observed = Counter(rule.repair(i) for i in range(len(chain.states)))
            tables = set(ExactTableSampler(chain.problem).tables())
            self.assertEqual(set(observed), tables)
            for table, count in observed.items():
                self.assertEqual(count, rule.fiber_size(table))
                self.assertLessEqual(rule.fiber_lower_bound, count)
                self.assertLessEqual(count, rule.fiber_upper_bound)
            law, rejected = rule.stationary_output_law()
            self.assertEqual(set(law.values()), {F(rule.fiber_lower_bound, len(chain.states))})
            success = 1 - rejected
            self.assertEqual(sum(law.values()), success)
            self.assertEqual({mass / success for mass in law.values()}, {F(1, len(tables))})
            self.assertGreaterEqual(success, 1 / rule.inverse_success_allowance)
            self.assertLessEqual(rule.inverse_success_allowance, min(chain.problem.shape))
        self.assertEqual(self.rule.stationary_output_law()[1], F(2, 9))

    def test_enumerated_fair_words_match_finite_law_and_rounding_error(self):
        ideal, _ = self.rule.stationary_output_law()
        for bits in range(5):
            law, rejected = self.rule.stationary_output_law(acceptance_bits=bits)
            observed = defaultdict(F)
            failures = F(0)
            for index, mass in enumerate(self.chain.stationary):
                accepted = 0
                for word in range(1 << bits):
                    rng = Words(word)
                    result = self.rule.terminal(index, acceptance_bits=bits, rng=rng)
                    self.assertEqual(rng.widths, [bits] if bits else [])
                    self.assertEqual(result.fair_bits, bits)
                    if result.table is not None:
                        observed[result.table] += mass / (1 << bits)
                        accepted += 1
                    else:
                        failures += mass / (1 << bits)
                ell = self.rule.fiber_size(self.rule.repair(index))
                difference = F(self.rule.fiber_lower_bound, ell) - F(accepted, 1 << bits)
                self.assertGreaterEqual(difference, 0)
                self.assertLess(difference, F(1, 1 << bits))
            self.assertEqual(dict(observed), {table: mass for table, mass in law.items() if mass})
            self.assertEqual(failures, rejected)
            self.assertLessEqual(sum(ideal.values()) - sum(law.values()), F(1, 1 << bits))
        finite, _ = self.rule.stationary_output_law(acceptance_bits=1)
        self.assertEqual(len(set(finite.values())), 2)  # rounding really can bias output

    def test_reuses_physical_step_including_hold_and_singleton_completion(self):
        # One representative per proposal slot plus all unused slots' hold mass.
        denominator = self.chain.beta.denominator
        counts = Counter()
        neighbors = self.chain.neighbors[self.dense]
        for slot in range(len(neighbors)):
            rng = Words(slot)
            result = self.rule.run(attempts=1, steps_per_attempt=1, acceptance_bits=0,
                                   start_index=self.dense, rng=rng)
            self.assertEqual(result.endpoint_state_index, neighbors[slot])
            self.assertEqual(rng.widths, [denominator.bit_length() - 1])
            counts[result.endpoint_state_index] += 1
        hold = self.rule.run(attempts=1, steps_per_attempt=1, acceptance_bits=0,
                             start_index=self.dense, rng=Words(len(neighbors)))
        self.assertEqual(hold.endpoint_state_index, self.dense)
        counts[self.dense] += denominator - len(neighbors)
        self.assertEqual(tuple(F(counts[i], denominator) for i in range(len(self.chain.states))),
                         self.chain.matrix[self.dense])

    def test_restarts_state_but_advances_random_stream_and_reports_work(self):
        rng = Words(0, 15, 1, 0)
        result = self.rule.run(attempts=3, steps_per_attempt=1, acceptance_bits=4,
                               start_index=self.dense, rng=rng)
        self.assertEqual(result.endpoint_state_index, self.chain.neighbors[self.dense][1])
        self.assertEqual((result.attempts, result.physical_steps, result.rejected_attempts), (2, 2, 1))
        walk_bits = self.chain.beta.denominator.bit_length() - 1
        self.assertEqual(rng.widths, [walk_bits, 4, walk_bits, 4])
        self.assertEqual(result.fair_bits, 2 * (walk_bits + 4))
        self.assertFalse(result.exhausted)
        self.assertFalse(result.fallback_used)

    def test_zero_bit_failure_and_feasible_fallback_are_explicit(self):
        rng = Words()
        result = self.rule.run(attempts=3, steps_per_attempt=0, acceptance_bits=0,
                               start_index=self.dense, rng=rng)
        self.assertTrue(result.exhausted)
        self.assertIsNone(result.table)
        self.assertEqual((result.attempts, result.rejected_attempts, result.physical_steps,
                          result.fair_bits), (3, 3, 0, 0))
        fallback = self.rule.repair(self.sparse)
        with_fallback = self.rule.run(attempts=3, steps_per_attempt=0, acceptance_bits=0,
                                      start_index=self.dense, fallback=fallback, rng=rng)
        self.assertEqual(with_fallback.table, fallback)
        self.assertTrue(with_fallback.fallback_used)
        self.assertTrue(with_fallback.exhausted)
        accepted = self.rule.run(attempts=3, steps_per_attempt=0, acceptance_bits=0,
                                 start_index=self.sparse, rng=rng)
        self.assertEqual(accepted.attempts, 1)
        self.assertFalse(accepted.exhausted)
        self.assertEqual(rng.widths, [])

    def test_exact_first_success_fallback_law_respects_error_allowance(self):
        tables = tuple(self.rule.stationary_output_law()[0])
        for bits in (0, 1, 4):
            law, failure = self.rule.stationary_output_law(acceptance_bits=bits)
            for attempts in (1, 3):
                # Independently compose the same stationary attempt law.
                result = {table: sum(law[table] * failure ** r for r in range(attempts))
                          for table in tables}
                result[tables[0]] += failure ** attempts
                self.assertEqual(sum(result.values()), 1)
                tv = sum(abs(mass - F(1, len(tables))) for mass in result.values()) / 2
                bound = self.rule.error_bound(attempts=attempts, acceptance_bits=bits, endpoint_tv=0)
                self.assertEqual(bound.stationary_exhaustion, F(6, 13) ** attempts)
                self.assertEqual(bound.acceptance_rounding, F(attempts, 1 << bits))
                self.assertLessEqual(tv, bound.total_variation_bound)
        bound = self.rule.error_bound(attempts=3, acceptance_bits=4, endpoint_tv=F(1, 100))
        self.assertEqual(bound.endpoint_coupling, F(3, 100))

    def test_budget_rejection_and_bad_fallback_precede_any_rng_use(self):
        for budget in (RepairAcceptBudget(max_attempts=1),
                       RepairAcceptBudget(max_physical_steps=1),
                       RepairAcceptBudget(max_fair_bits=1)):
            rng = Words()
            with self.assertRaises(ComputationBudgetExceeded):
                self.rule.run(attempts=2, steps_per_attempt=1, acceptance_bits=4,
                              rng=rng, budget=budget)
            self.assertEqual(rng.widths, [])
        rng = Words()
        with self.assertRaises(ValueError):
            self.rule.run(attempts=1, steps_per_attempt=1, acceptance_bits=4,
                          rng=rng, fallback=((0, 0), (0, 0)))
        self.assertEqual(rng.widths, [])

    def test_seed_reproducibility_and_rng_exclusion(self):
        args = dict(attempts=4, steps_per_attempt=3, acceptance_bits=5, start_index=self.dense)
        self.assertEqual(self.rule.run(**args, seed=123), self.rule.run(**args, seed=123))
        self.assertEqual(self.rule.run(**args, seed=123), self.rule.run(**args, rng=random.Random(123)))
        with self.assertRaises(ValueError):
            self.rule.run(**args, seed=123, rng=Words())

    def test_scope_and_input_contracts(self):
        # TableProblem forbids empty shapes on construction; verify the wrapper
        # independently rejects that vacuous scope when given a replaced chain.
        empty = object.__new__(TableProblem)
        object.__setattr__(empty, "row_sums", ())
        object.__setattr__(empty, "column_sums", ())
        object.__setattr__(empty, "lower_bounds", ())
        object.__setattr__(empty, "upper_bounds", ())
        with self.assertRaisesRegex(ValueError, "at least one row and one column"):
            RepairAcceptRule(replace(self.chain, problem=empty))
        for rows, columns, cutoff in [((0, 1), (1,), 2), ((2,), (2,), 2)]:
            chain = build_rescaled_ideal_chain(TableProblem(rows, columns), U=cutoff, L=1)
            with self.assertRaises(ValueError):
                RepairAcceptRule(chain)
        for problem in (TableProblem((2, 2), (2, 2), structural_zeros=[(0, 0)]),
                        TableProblem((2, 2), (2, 2), lower_bounds=((1, 0), (0, 0)))):
            with self.assertRaises(ValueError):
                RepairAcceptRule(replace(self.chain, problem=problem))
        for chain in (replace(self.chain, stationary=(F(1),) * len(self.chain.states)),
                      replace(self.chain, completions=((((), ()),),) * len(self.chain.states))):
            with self.assertRaises(ValueError):
                RepairAcceptRule(chain)
        for bits in (-1, True, 1.5):
            with self.assertRaises((ValueError, TypeError)):
                self.rule.terminal(self.dense, acceptance_bits=bits, rng=Words())
        for word in (-1, True, 16):
            with self.assertRaises((ValueError, TypeError)):
                self.rule.terminal(self.dense, acceptance_bits=4, rng=Words(word))
        with self.assertRaises(IndexError):
            self.rule.repair(len(self.chain.states))
        with self.assertRaises(ValueError):
            self.rule.error_bound(attempts=1, acceptance_bits=1, endpoint_tv=F(11, 10))
        with self.assertRaises(TypeError):
            self.rule.error_bound(attempts=1, acceptance_bits=1, endpoint_tv=0.1)


if __name__ == "__main__":
    unittest.main()
