"""Finite-law and exact budget checks for independent thinned oracle blocks."""

from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import comb
import unittest

from contingency115.block_budgets import (
    independent_oracle_work,
    inner_block_schedule,
    majority_failure_bound,
    median_block_count,
    positive_rational_median,
    quarter_majority_failure,
    work_difference,
)
from contingency115.budgets import LN2_UPPER, ceil_fraction


def matrix_power(matrix, exponent):
    size = len(matrix)
    result = [[F(i == j) for j in range(size)] for i in range(size)]
    for _ in range(exponent):
        result = [[sum(result[i][k]*matrix[k][j] for k in range(size))
                   for j in range(size)] for i in range(size)]
    return result


def block_mean_law(kernel, stationary, observations, count):
    """Propagate exact state and sum laws, including fresh conditional noise."""
    law = defaultdict(F)
    for state, mass in enumerate(stationary):
        for value, conditional_mass in observations[state]:
            law[state, value] += mass*conditional_mass
    for _ in range(count-1):
        updated = defaultdict(F)
        for (old_state, total), mass in law.items():
            for state, transition_mass in enumerate(kernel[old_state]):
                for value, conditional_mass in observations[state]:
                    updated[state, total+value] += mass*transition_mass*conditional_mass
        law = updated
    averages = defaultdict(F)
    for (_, total), mass in law.items():
        averages[total/count] += mass
    return dict(averages)


def law_moments(law):
    mean = sum(value*mass for value, mass in law.items())
    return mean, sum((value-mean)**2*mass for value, mass in law.items())


def binomial_tail(count, probability, threshold):
    return sum(F(comb(count, successes))*probability**successes*(1-probability)**(count-successes)
               for successes in range(threshold, count+1))


class BlockBudgetTests(unittest.TestCase):
    def test_exact_chebyshev_median_and_coupling_allocations(self):
        for height, step, xi, theta, lag_bits in product(
            (1, 10, 1000), (0, 1), (F(1, 1000), F(249999, 10**6)),
            (F(1, 10), F(1, 10**9)), (1, 2, 4),
        ):
            s = inner_block_schedule(7, 1001, height, xi, theta, annealing_step=step, lag_error_bits=lag_bits)
            sigma = s.reference.sigma
            self.assertGreaterEqual(F(s.observation_spacing)/s.reference.inverse_gap_bound, LN2_UPPER*lag_bits)
            self.assertEqual(s.variance_inflation_bound, F(2**lag_bits+1, 2**lag_bits-1))
            for variance, observations in (
                (s.ratio_relative_variance_bound, s.ratio_observations_per_block),
                (s.correction_relative_variance_bound, s.correction_observations_per_block),
            ):
                self.assertLessEqual(s.variance_inflation_bound*variance/(observations*sigma**2), s.block_failure_bound)
            self.assertEqual(s.blocks_per_average % 2, 1)
            self.assertLessEqual(s.median_failure_bound, F(1, 2**s.median_tail_bits))
            self.assertLessEqual(F(step+1, 2**s.median_tail_bits), theta/4)
            self.assertLessEqual(F(s.total_coupled_draw_bound, 2**s.draw_error_bits), theta/8)
            mass = s.reference.log2_inverse_min_mass_bound
            self.assertGreaterEqual(F(s.burn_in_steps)/s.reference.inverse_gap_bound,
                                    LN2_UPPER*(F(mass, 2)+s.draw_error_bits-1))
            self.assertEqual(s.total_blocks, (step+1)*s.blocks_per_average)
            self.assertEqual(s.total_coupled_draw_bound, s.total_blocks+s.work.scalar_offset_draws)
            self.assertEqual(s.work.ratio_evaluations, step*s.blocks_per_average*s.ratio_observations_per_block)
            self.assertEqual(s.work.correction_evaluations, s.blocks_per_average*s.correction_observations_per_block)
            observed = s.work.ratio_evaluations+s.work.correction_evaluations
            self.assertEqual(s.work.bin_transitions, s.total_blocks*s.burn_in_steps+(observed-s.total_blocks)*s.observation_spacing)

    def test_exact_lag_bounds_for_two_state_chains(self):
        for crossing, lag_bits in product((F(1, 2), F(1, 4), F(1, 8), F(1, 32)), (1, 2, 4)):
            inverse_gap = 1/(2*crossing)
            s = inner_block_schedule(2, 16, 1, F(1, 8), F(1, 10), inverse_gap_bound=inverse_gap, lag_error_bits=lag_bits)
            eigenvalue = 1-2*crossing
            self.assertLessEqual(eigenvalue**s.observation_spacing, F(1, 2**lag_bits))

    def test_exact_majority_tail_and_minimal_odd_count(self):
        for error_bits in (1, 2, 3, 5, 10, 29, 50, 100):
            blocks = median_block_count(error_bits)
            self.assertLessEqual(blocks, 6*error_bits-5)
            self.assertLessEqual(quarter_majority_failure(blocks), F(1, 2**error_bits))
            for smaller in range(1, blocks, 2):
                self.assertGreater(quarter_majority_failure(smaller), F(1, 2**error_bits))
            conservative = median_block_count(error_bits, policy="hoeffding")
            self.assertGreaterEqual(F(conservative, 8), LN2_UPPER*error_bits)
            self.assertLessEqual(blocks, conservative)
        for blocks in range(1, 16, 2):
            tail = binomial_tail(blocks, F(1, 4), blocks//2+1)
            self.assertEqual(quarter_majority_failure(blocks), tail)
            self.assertLessEqual(tail, F(1, 2)*F(3, 4)**(blocks//2))

    def test_exact_general_failure_targets_and_eighth_search_cap(self):
        for p, error_bits in product((F(1, 8), F(1, 16), F(1, 1000), F(2, 9)), (1, 2, 3, 10, 29, 50)):
            blocks = median_block_count(error_bits, failure_bound=p)
            target = F(1, 2**error_bits)
            self.assertLessEqual(majority_failure_bound(blocks, p), target)
            if blocks > 1:
                self.assertGreater(majority_failure_bound(blocks-2, p), target)
            cap = max(1, 2*error_bits-3) if p <= F(1, 8) else 6*error_bits-5
            self.assertLessEqual(blocks, cap)
            conservative = median_block_count(error_bits, failure_bound=p, policy="hoeffding")
            self.assertGreaterEqual(2*conservative*(F(1, 2)-p)**2, LN2_UPPER*error_bits)
            self.assertLessEqual(blocks, conservative)
            for count in range(1, 16, 2):
                tail = binomial_tail(count, p, count//2+1)
                self.assertEqual(majority_failure_bound(count, p), tail)
                self.assertLessEqual(tail, quarter_majority_failure(count))
                if p <= F(1, 8):
                    self.assertLessEqual(tail, F(1, 4)*F(7, 16)**(count//2))

    def test_eighth_policy_reduces_total_work_against_quarter_on_reference_case(self):
        eighth = inner_block_schedule(19, 1000, 100, F(1, 1000), F(1, 10**6))
        quarter = inner_block_schedule(19, 1000, 100, F(1, 1000), F(1, 10**6), block_failure_target=F(1, 4))
        self.assertEqual(eighth.block_failure_bound, F(1, 8))
        self.assertGreater(eighth.correction_observations_per_block, quarter.correction_observations_per_block)
        self.assertLess(eighth.blocks_per_average, quarter.blocks_per_average)
        for name in eighth.work.__dataclass_fields__:
            self.assertLess(getattr(eighth.work, name), getattr(quarter.work, name))
        # The edge target p=1/4 and a much stricter rational are both supported.
        for p in (F(1, 4), F(1, 1000)):
            s = inner_block_schedule(1, 2, 1, F(1, 5), F(1, 10), block_failure_target=p)
            bound = s.variance_inflation_bound*s.ratio_relative_variance_bound
            self.assertLessEqual(bound/(s.ratio_observations_per_block*s.reference.sigma**2), p)

    def test_stationary_variance_against_full_finite_block_laws(self):
        stationary = [F(1, 2), F(1, 2)]
        deterministic = [[(F(1), F(1))], [(F(3), F(1))]]
        noisy = [[(F(1), F(1, 2)), (F(2), F(1, 2))],
                 [(F(2), F(1, 2)), (F(4), F(1, 2))]]
        for crossing, lag_bits in product((F(1, 2), F(1, 4), F(1, 8)), (1, 2)):
            inverse_gap = 1/(2*crossing)
            spacing = ceil_fraction(LN2_UPPER*inverse_gap*lag_bits)
            kernel = matrix_power([[1-crossing, crossing], [crossing, 1-crossing]], spacing)
            inflation = F(2**lag_bits+1, 2**lag_bits-1)
            for observations in (deterministic, noisy):
                one_law = block_mean_law(kernel, stationary, observations, 1)
                mean, variance = law_moments(one_law)
                for count in (1, 2, 5, 8):
                    law = block_mean_law(kernel, stationary, observations, count)
                    actual_mean, actual_variance = law_moments(law)
                    self.assertEqual(sum(law.values()), 1)
                    self.assertEqual(actual_mean, mean)
                    self.assertLessEqual(actual_variance, inflation*variance/count)

    def test_finite_block_tails_and_independent_median_distribution(self):
        crossing = F(1, 8)
        kernel = matrix_power([[1-crossing, crossing], [crossing, 1-crossing]], 3)
        observations = [[(F(1), F(1))], [(F(2), F(1))]]
        # sigma=1/4 here tests the general stationary-block lemma; the product
        # schedule itself has its stricter sigma<1/10 requirement.
        sigma, mean, count = F(1, 4), F(3, 2), 24
        law = block_mean_law(kernel, [F(1, 2)]*2, observations, count)
        below = sum(mass for value, mass in law.items() if value < (1-sigma)*mean)
        above = sum(mass for value, mass in law.items() if value > (1+sigma)*mean)
        self.assertLessEqual(below+above, F(1, 4))
        for blocks in (3, 9, 29):
            majority = blocks//2+1
            exact_median_failure = binomial_tail(blocks, below, majority)+binomial_tail(blocks, above, majority)
            bad_count_bound = binomial_tail(blocks, below+above, majority)
            self.assertLessEqual(exact_median_failure, bad_count_bound)
            self.assertLessEqual(bad_count_bound, binomial_tail(blocks, F(1, 4), majority))
        self.assertLessEqual(binomial_tail(29, F(1, 4), 15), F(1, 32))

    def test_independence_negative_controls(self):
        # One offset bit reused through a block leaves variance unchanged,
        # violating the 3*Var(X)/N bound once N>3.
        shared_noise_variance = F(1, 4)
        self.assertGreater(shared_noise_variance, 3*shared_noise_variance/8)
        # Reusing a single failure across every block prevents amplification.
        shared_failure = F(1, 4)
        independent_majority_failure = binomial_tail(29, F(1, 4), 15)
        self.assertGreater(shared_failure, F(1, 32))
        self.assertLess(independent_majority_failure, F(1, 32))
        # Even independently distributed offset bits can break the covariance
        # identity if an offset reuses the next transition's randomness.
        pairs = [(F(1+a+b), F(1+b+c)) for a, b, c in product((0, 1), repeat=3)]
        mean0 = sum(x for x, _ in pairs)/8
        mean1 = sum(y for _, y in pairs)/8
        covariance = sum((x-mean0)*(y-mean1) for x, y in pairs)/8
        self.assertEqual(covariance, F(1, 4))
        # The iid bin kernel has zero lag covariance for every function of bin.
        self.assertGreater(covariance, 0)

    def test_median_law_monotonicity_and_rounding_with_order_changes(self):
        values = (F(1), F(1001, 1000), F(1002, 1000), F(1003, 1000), F(2))
        sigma = F(1, 10)
        target = positive_rational_median(values)
        for signs in product((-1, 1), repeat=len(values)):
            perturbed = tuple(value*(1+sign*sigma) for value, sign in zip(values, signs))
            median = positive_rational_median(perturbed)
            self.assertGreaterEqual(median, (1-sigma)*target)
            self.assertLessEqual(median, (1+sigma)*target)
            self.assertGreaterEqual(median, min(perturbed))
            self.assertLessEqual(median, max(perturbed))
        # The exact median must not be described as an unbiased mean estimate.
        # For Bernoulli mass1/4 at2, the median of3 has upper mass5/32.
        self.assertNotEqual(1+binomial_tail(3, F(1, 4), 2), F(5, 4))

    def test_work_accounting_tracks_evaluation_tradeoff(self):
        s = inner_block_schedule(19, 1000, 100, F(1, 1000), F(1, 10**6))
        independent = independent_oracle_work(s.reference)
        changes = work_difference(s.work, independent)
        self.assertLess(changes["bin_transitions"], 0)
        self.assertGreater(changes["correction_evaluations"], 0)
        self.assertGreater(changes["ratio_evaluations"], 0)
        self.assertGreater(changes["scalar_offset_draws"], 0)
        wider = inner_block_schedule(19, 1000, 100, F(1, 1000), F(1, 10**6), lag_error_bits=4)
        self.assertLess(wider.work.correction_evaluations, s.work.correction_evaluations)
        self.assertGreater(wider.work.bin_transitions, s.work.bin_transitions)

    def test_blocks_can_regress_when_burn_in_is_cheap(self):
        s = inner_block_schedule(1, 2, 1, F(249, 1000), F(1, 5), inverse_gap_bound=F(2))
        independent = independent_oracle_work(s.reference)
        self.assertGreater(s.work.bin_transitions, independent.bin_transitions)
        self.assertGreater(s.work.correction_evaluations, independent.correction_evaluations)
        self.assertGreater(s.work.scalar_offset_draws, independent.scalar_offset_draws)

    def test_input_validation_and_generic_support(self):
        for call in (
            lambda: inner_block_schedule(2, 16, 1, F(1, 8), F(1, 10), lag_error_bits=0),
            lambda: inner_block_schedule(2, 16, 1, F(1, 8), F(1, 10), lag_error_bits=True),
            lambda: inner_block_schedule(2, 16, 1, F(1, 8), F(1, 10), block_failure_target=F(1, 3)),
            lambda: inner_block_schedule(2, 16, 1, F(1, 8), F(1, 10), block_failure_target=0),
            lambda: inner_block_schedule(2, 16, 1, F(1, 8), F(1, 10), block_failure_target=0.125),
            lambda: positive_rational_median([]), lambda: positive_rational_median([1, 2]),
            lambda: positive_rational_median([0]), lambda: positive_rational_median([0.5]),
            lambda: quarter_majority_failure(2), lambda: median_block_count(0),
            lambda: median_block_count(5, policy="unknown"),
            lambda: median_block_count(5, failure_bound=True),
            lambda: majority_failure_bound(3, F(-1, 8)),
        ):
            with self.assertRaises((ValueError, TypeError)):
                call()
        narrow = inner_block_schedule(2, 16, 1, F(1, 8), F(1, 10), correction_support=(F(1), F(101, 100)))
        self.assertLess(narrow.correction_observations_per_block, narrow.ratio_observations_per_block)
        self.assertEqual(narrow.reference.correction_support_policy, "caller_supplied")

    def test_zero_height_and_one_observation_boundaries(self):
        # The utility is algebraically defined at H=j=0; a physical oracle
        # should instead return the known exact h0 without dividing by H.
        s = inner_block_schedule(1, 1, 0, F(249999, 10**6), F(1, 5),
                                 correction_support=(F(1), 1+F(1, 10**12)))
        self.assertEqual(s.reference.annealing_step, 0)
        self.assertEqual(s.work.ratio_evaluations, 0)
        self.assertEqual(s.correction_observations_per_block, 1)
        self.assertEqual(s.work.bin_transitions, s.total_blocks*s.burn_in_steps)
        self.assertEqual(s.total_blocks, s.blocks_per_average)
        self.assertLess(s.reference.sigma, F(1, 10))


if __name__ == "__main__":
    unittest.main()
