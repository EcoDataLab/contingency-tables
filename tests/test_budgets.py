"""Independent exact-arithmetic checks for conditional schedule certificates."""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import factorial
import unittest

from contingency115.budgets import (
    LN2_UPPER,
    ceil_fraction,
    ceil_log2,
    counting_bin_gap_bound,
    dense_schedule,
    domination_accuracy_bits,
    dyadic_denominator_budget,
    dyadic_offset_bits,
    dyadic_offset_tv,
    exact_correction_schedule,
    inner_counting_schedule,
    mixing_steps,
    outer_schedule,
    rare_branch_gate,
    residual_weights,
    sampling_dense_gap_bound,
    sampling_dense_mass_bound,
    sampling_small_gap_bound,
    table_count_upper_bound,
)


def two_power(exponent):
    return F(2**exponent) if exponent >= 0 else F(1, 2**-exponent)


def compositions(total, length):
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, length - 1):
                yield (first, *rest)


def enumerate_count(rows, columns):
    if not rows:
        return int(all(value == 0 for value in columns))
    return sum(
        enumerate_count(rows[1:], tuple(c - x for c, x in zip(columns, row)))
        for row in compositions(rows[0], len(columns))
        if all(x <= c for c, x in zip(columns, row))
    )


class ExactArithmeticTests(unittest.TestCase):
    def test_logarithms_and_ceilings_without_float(self):
        values = [F(p, q) for p in range(1, 71) for q in range(1, 51)]
        values += [F((1 << 3000) + delta, (1 << 201) + 7) for delta in (-1, 0, 1)]
        for value in values:
            bits = ceil_log2(value)
            self.assertLess(two_power(bits - 1), value)
            self.assertLessEqual(value, two_power(bits))
            ceiling = ceil_fraction(value)
            self.assertLess(ceiling - 1, value)
            self.assertGreaterEqual(ceiling, value)
        self.assertGreater(sum(LN2_UPPER**j / factorial(j) for j in range(5)), 2)

    def test_reject_inexact_or_out_of_domain_inputs(self):
        for call in (
            lambda: ceil_log2(0), lambda: ceil_log2(-1),
            lambda: ceil_log2(0.5), lambda: outer_schedule(13, 20, 1),
            lambda: outer_schedule(14, 13, 1), lambda: outer_schedule(14, 20, 0),
            lambda: mixing_steps(F(1, 2), 1, 1), lambda: mixing_steps(1, -1, 1),
            lambda: mixing_steps(1, 1, 0), lambda: dyadic_offset_bits(0, F(1, 2)),
            lambda: dyadic_offset_bits(5, 0), lambda: table_count_upper_bound([1], [2]),
            lambda: table_count_upper_bound([], [0]),
            lambda: inner_counting_schedule(2, 16, 4, F(1, 4), F(1, 10)),
            lambda: inner_counting_schedule(2, 16, 4, F(1, 10), 0.01),
            lambda: inner_counting_schedule(2, 16, 4, F(1, 10), F(1, 10), concentration="invalid"),
            lambda: inner_counting_schedule(2, 16, 4, F(1, 10), F(1, 10), allocation="invalid"),
        ):
            with self.assertRaises((TypeError, ValueError)):
                call()


class SamplingBudgetTests(unittest.TestCase):
    def test_outer_three_independent_error_certificates(self):
        for d, extra_b, k in product((14, 19, 100), (0, 90), (1, 20, 1000)):
            b = d + extra_b
            for gap in (F(17, 3), F(sampling_small_gap_bound(d))):
                schedule = outer_schedule(d, b, k, inverse_gap_bound=gap)
                j, t, h = schedule.trials, schedule.steps_per_trial, schedule.dense_accuracy_bits
                # exp(-J/sden) <= 2^(-k-2), witnessed before transcendental evaluation.
                self.assertGreaterEqual(F(j, 2 * (1 + d*d)), LN2_UPPER * (k + 2))
                # TV <= .5 * 2^(db) * exp(-t/K). Integer lower exponent
                # gives an exact dyadic certificate after union over J trials.
                dyadic_decay = (F(t) / (gap * LN2_UPPER)).numerator // (F(t) / (gap * LN2_UPPER)).denominator
                self.assertLessEqual(j, 1 << (dyadic_decay - d*b - k - 1))
                self.assertLessEqual(j * (t + 1), 1 << (h - k - 2))
                # At most 3/4 of the requested total error is allocated.
                self.assertLess(F(3, 4), 1)

    def test_dense_failure_uses_exact_survival_probability(self):
        for d, h in product((14, 19, 40), (1, 20, 200)):
            schedule = dense_schedule(d, h)
            self.assertLessEqual(F(63, 64) ** schedule.trials, two_power(-h - 2))
            self.assertLessEqual(
                schedule.trials * (1 + d), 1 << (schedule.draw_error_bits - h - 2)
            )
            required = schedule.log2_inverse_min_mass_bound / 2 + schedule.draw_error_bits - 1
            self.assertGreaterEqual(F(schedule.steps_per_trial) / schedule.inverse_gap_bound, LN2_UPPER * required)
            self.assertLess(F(schedule.steps_per_trial - 1) / schedule.inverse_gap_bound, LN2_UPPER * required)

    def test_generic_mass_and_gap_inputs(self):
        d, a, b = 19, 16 * 19**2, 16 * 19**3
        mass = sampling_dense_mass_bound(d, a, b)
        # Independent integer exponent check for the min-mass allowance.
        self.assertLessEqual((4*b)**d, 1 << (mass - 4*a*d))
        schedule = dense_schedule(d, 31, inverse_gap_bound=F(12345, 7), log2_inverse_min_mass_bound=F(123, 2))
        self.assertEqual(schedule.inverse_gap_bound, F(12345, 7))
        self.assertEqual(schedule.log2_inverse_min_mass_bound, F(123, 2))
        self.assertEqual(
            F(sampling_dense_gap_bound(d, sharp_constant=False), sampling_dense_gap_bound(d)),
            F(100000, 1536)**2,
        )

    def test_updated_denominator_allowance(self):
        outer = outer_schedule(14, 30, 3, inverse_gap_bound=2)
        dense = dense_schedule(14, outer.dense_accuracy_bits, inverse_gap_bound=3, log2_inverse_min_mass_bound=4)
        result = dyadic_denominator_budget(outer, dense, acceptance_exponent_bound=17)
        self.assertGreaterEqual(1 << (result.bin_transition_bits - 17), 8*14)
        self.assertEqual(result.dense_call_bits, dense.trials * result.dense_trial_bits)
        self.assertEqual(result.outer_call_bits, outer.trials * result.outer_trial_bits)
        for width in (1, 2, 3, 123, 2**30 - 1, 2**30):
            bits = dyadic_offset_bits(width, two_power(-dense.draw_error_bits))
            self.assertLessEqual(bits, result.scalar_offset_bits)
        with self.assertRaises(ValueError):
            dyadic_denominator_budget(outer, dense_schedule(14, 1))

    def test_offset_formula_against_enumerated_actual_law(self):
        for width, bits in product(range(1, 31), range(9)):
            outcomes = 1 << bits
            counts = Counter(width * draw // outcomes for draw in range(outcomes))
            exact_tv = sum(abs(F(counts[value], outcomes) - F(1, width)) for value in range(width)) / 2
            self.assertEqual(dyadic_offset_tv(width, bits), exact_tv)
        for width, tolerance in product(range(1, 101), (F(1, 2), F(1, 17), F(1, 1024))):
            bits = dyadic_offset_bits(width, tolerance)
            self.assertLessEqual(dyadic_offset_tv(width, bits), tolerance)
        self.assertEqual(dyadic_offset_bits(1024, F(1, 10**20)), 10)


class CorrectionTests(unittest.TestCase):
    def test_sharp_integer_domination_threshold(self):
        for count, gate in product(range(1, 201), range(1, 25)):
            bits = domination_accuracy_bits(count, gate)
            required = count * ((1 << gate) - 1)
            self.assertLessEqual(required, 1 << bits)
            if bits:
                self.assertLess(1 << (bits - 1), required)
        # Does not allocate 2**gate when the gate index itself is enormous.
        self.assertEqual(domination_accuracy_bits(7, 10**30), 10**30 + 3)

    def test_count_bound_against_independent_enumeration(self):
        cases = (
            ((3, 3), (3, 3)), ((0, 0), (0, 0)), ((6,), (1, 2, 3)),
            ((0, 3, 2), (1, 2, 2)), ((2, 2, 2), (1, 2, 3)),
            ((3, 1, 1), (1, 1, 1, 2)), ((4, 4), (3, 3, 2)),
        )
        for rows, columns in cases:
            bound = table_count_upper_bound(rows, columns)
            self.assertGreaterEqual(bound, enumerate_count(rows, columns))
            self.assertEqual(bound, table_count_upper_bound(columns, rows))
        self.assertEqual(table_count_upper_bound((3, 3), (3, 3)), 4)

    def test_cost_and_domination_are_distinct(self):
        for d, b, exponent, slack in product((14, 19), (104, 512), (10, 500), (0, 1, 7)):
            schedule = exact_correction_schedule(d, b, rare_cost_exponent=exponent, cost_slack_bits=slack)
            self.assertEqual(exponent*d*b - schedule.gate_bits, -slack)
            self.assertEqual(schedule.accuracy_bits - schedule.gate_bits, d*b)
            tighter = exact_correction_schedule(d, b, rare_cost_exponent=exponent, count_upper_bound=4, cost_slack_bits=slack)
            self.assertEqual(tighter.accuracy_bits, tighter.gate_bits + 2)

    def test_residuals_and_mixture_on_all_small_dyadic_laws(self):
        passed = rejected = 0
        for count, r, gate in product(range(2, 5), range(1, 5), range(1, 4)):
            denominator = 1 << r
            delta = F(1, 1 << gate)
            for numerators in compositions(denominator, count):
                dominated = all((1-delta)*F(value, denominator) <= F(1, count) for value in numerators)
                if not dominated:
                    with self.assertRaises(ValueError):
                        residual_weights(numerators, r, gate)
                    rejected += 1
                    continue
                weights = residual_weights(numerators, r, gate)
                self.assertEqual(sum(weights), count*denominator)
                for value, weight in zip(numerators, weights):
                    self.assertEqual((1-delta)*F(value, denominator) + delta*F(weight, count*denominator), F(1, count))
                passed += 1
        self.assertGreater(passed, 100)
        self.assertGreater(rejected, 100)
        with self.assertRaises(ValueError):
            residual_weights((1, 1), 3, 2)

    def test_gate_law_and_expected_reads_exhaustively(self):
        for gate in range(1, 10):
            rare_count = total_reads = 0
            for bits in product((0, 1), repeat=gate):
                stream = iter(bits)
                rare, reads = rare_branch_gate(lambda: next(stream), gate)
                rare_count += rare
                total_reads += reads
                self.assertEqual(rare, not any(bits))
                self.assertEqual(reads, next((i + 1 for i, bit in enumerate(bits) if bit), gate))
            self.assertEqual(rare_count, 1)
            self.assertEqual(F(total_reads, 1 << gate), 2 - two_power(1-gate))
        with self.assertRaises(ValueError):
            rare_branch_gate(lambda: 2, 1)


class CountingBudgetTests(unittest.TestCase):
    def test_bernstein_variance_bound_is_attained_by_an_endpoint_law(self):
        a, b = F(1, 8), F(4)
        for high_mass in [F(j, 100) for j in range(101)] + [F(1, 33)]:
            mean = (1-high_mass)*a + high_mass*b
            variance = (1-high_mass)*(a-mean)**2 + high_mass*(b-mean)**2
            self.assertLessEqual(variance/mean**2, F(961, 128))
            if high_mass == F(1, 33):
                self.assertEqual(variance/mean**2, F(961, 128))
        # The mgf series estimate's factorial inequality follows by induction.
        for j in range(2, 50):
            self.assertGreaterEqual(factorial(j), 2*3**(j-2))

    def test_concentration_coupling_and_mixing_allocations(self):
        for height, xi, theta in product((0, 1, 17, 10**4), (F(1, 8), F(1, 1000)), (F(1, 8), F(1, 10**9))):
            for method in ("hoeffding", "bernstein"):
                s = inner_counting_schedule(7, 1001, height, xi, theta, concentration=method)
                exponent = s.samples_per_average * s.sigma**2 / s.concentration_denominator
                self.assertGreaterEqual(exponent, LN2_UPPER*s.average_tail_bits)
                ratio_exponent = s.ratio_samples_per_average * s.sigma**2 / s.ratio_concentration_denominator
                self.assertGreaterEqual(ratio_exponent, LN2_UPPER*s.average_tail_bits)
                self.assertEqual(s.total_draw_bound, height*s.ratio_samples_per_average + 8*s.correction_samples)
                self.assertLessEqual(2*(height+1)*two_power(-s.average_tail_bits), theta/4)
                self.assertLessEqual(s.total_draw_bound*two_power(-s.draw_error_bits), theta/8)
                mass = height + 7*ceil_log2(1001)
                self.assertGreaterEqual(F(s.steps_per_bin_sample)/s.inverse_gap_bound, LN2_UPPER*(F(mass, 2)+s.draw_error_bits-1))
                if method == "bernstein":
                    self.assertLess(s.concentration_denominator, 16)
                    review_samples = ceil_fraction(1024 * s.average_tail_bits / s.sigma**2)
                    self.assertLess(64*s.samples_per_average, review_samples)

    def test_common_allocation_remains_available(self):
        common = inner_counting_schedule(7, 1001, 100, F(1, 10), F(1, 1000), allocation="common")
        separate = inner_counting_schedule(7, 1001, 100, F(1, 10), F(1, 1000))
        self.assertEqual(common.ratio_samples_per_average, common.correction_samples)
        self.assertEqual(common.correction_samples, separate.correction_samples)
        self.assertGreater(common.total_draw_bound, separate.total_draw_bound)

    def test_extracted_counting_gap_constant(self):
        self.assertEqual(
            F(counting_bin_gap_bound(19, 1000, sharp_constant=False), counting_bin_gap_bound(19, 1000)),
            F(10000, 1024)**2,
        )


if __name__ == "__main__":
    unittest.main()
