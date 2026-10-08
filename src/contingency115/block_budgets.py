"""Conditional thinned-block budgets for the #115 bounded-counting bin oracle.

These utilities allocate work and compute exact rational medians. They are not
an implementation of the bin chain or a modified compiled counting theorem.
Transitions within a block must be the exact, fixed, lazy reversible bin kernel.
Independent fresh blocks and fresh conditional offsets are essential hypotheses.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb
from typing import Literal, Sequence

from .budgets import (
    LN2_UPPER,
    InnerCountingSchedule,
    ceil_fraction,
    ceil_log2,
    inner_counting_schedule,
    mixing_steps,
)


@dataclass(frozen=True)
class OracleWorkCounts:
    bin_transitions: int
    ratio_evaluations: int
    correction_evaluations: int
    scalar_offset_draws: int
    rational_accumulations: int
    mean_divisions: int
    median_comparison_bound: int


@dataclass(frozen=True)
class InnerBlockSchedule:
    reference: InnerCountingSchedule
    lag_error_bits: int
    observation_spacing: int
    variance_inflation_bound: Fraction
    ratio_relative_variance_bound: Fraction
    correction_relative_variance_bound: Fraction
    ratio_observations_per_block: int
    correction_observations_per_block: int
    block_failure_bound: Fraction
    median_policy: str
    median_tail_bits: int
    blocks_per_average: int
    median_failure_bound: Fraction
    total_blocks: int
    total_coupled_draw_bound: int
    draw_error_bits: int
    burn_in_steps: int
    work: OracleWorkCounts


def independent_oracle_work(schedule: InnerCountingSchedule) -> OracleWorkCounts:
    """Work allowances for the independent-walk reference at its actual j."""
    ratios = schedule.annealing_step * schedule.ratio_samples_per_average
    corrections = schedule.correction_samples
    observations = ratios + corrections
    return OracleWorkCounts(
        observations * schedule.steps_per_bin_sample,
        ratios,
        corrections,
        schedule.dimension * corrections,
        observations,
        schedule.annealing_step + 1,
        0,
    )


def _validate_failure_bound(value: int | Fraction) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise TypeError("failure_bound must be an exact rational")
    value = Fraction(value)
    if not 0 < value <= Fraction(1, 4):
        raise ValueError("failure_bound must be in (0, 1/4]")
    return value


def majority_failure_bound(blocks: int, failure_bound: int | Fraction) -> Fraction:
    """Exact binomial majority tail for independent block failures <=p<=1/4."""
    if isinstance(blocks, bool) or not isinstance(blocks, int) or blocks < 1 or blocks % 2 == 0:
        raise ValueError("blocks must be a positive odd integer")
    p = _validate_failure_bound(failure_bound)
    x, y = p.numerator, p.denominator
    numerator = sum(comb(blocks, failures) * x**failures * (y-x)**(blocks-failures)
                    for failures in range(blocks//2+1, blocks+1))
    return Fraction(numerator, y**blocks)


def quarter_majority_failure(blocks: int) -> Fraction:
    """Compatibility wrapper for the independent failure bound p=1/4."""
    return majority_failure_bound(blocks, Fraction(1, 4))


def median_block_count(
    error_bits: int,
    *,
    failure_bound: int | Fraction = Fraction(1, 4),
    policy: Literal["exact_binomial", "hoeffding"] = "exact_binomial",
) -> int:
    """Odd block count with majority failure <=2**(-error_bits).

    Exact search is bounded by 6*error_bits-5 for p<=1/4. For B=2m+1,
    Markov on 3**failures gives .5*(3/4)**m. For p<=1/8, Markov on
    7**failures gives .25*(7/16)**m, reducing the cap to max(1,2L-3).
    The search has polynomial bit cost in error_bits and the bit length of p,
    with no real log. It finds the least odd B for this independent failure law.
    """
    if isinstance(error_bits, bool) or not isinstance(error_bits, int) or error_bits < 1:
        raise ValueError("error_bits must be a positive integer")
    p = _validate_failure_bound(failure_bound)
    if policy == "hoeffding":
        blocks = ceil_fraction(LN2_UPPER*error_bits / (2*(Fraction(1, 2)-p)**2))
        return blocks if blocks % 2 else blocks+1
    if policy != "exact_binomial":
        raise ValueError("policy must be 'exact_binomial' or 'hoeffding'")
    target = Fraction(1, 1 << error_bits)
    cap = max(1, 2*error_bits-3) if p <= Fraction(1, 8) else 6*error_bits-5
    for blocks in range(1, cap+1, 2):
        if majority_failure_bound(blocks, p) <= target:
            return blocks
    raise ArithmeticError("proved finite majority-tail search bound was exceeded")


def inner_block_schedule(
    d: int,
    bin_scale: int,
    annealing_height: int,
    relative_accuracy: int | Fraction,
    failure_probability: int | Fraction,
    *,
    sigma_policy: Literal["source", "product"] = "product",
    correction_support: Literal["published", "source_lipschitz"] | tuple[int | Fraction, int | Fraction] = "source_lipschitz",
    annealing_step: int | None = None,
    inverse_gap_bound: int | Fraction | None = None,
    lag_error_bits: int = 1,
    block_failure_target: int | Fraction = Fraction(1, 8),
    median_policy: Literal["exact_binomial", "hoeffding"] = "exact_binomial",
) -> InnerBlockSchedule:
    """Allocate independent thinned blocks and take a median for each factor.

    The inherited chain, support, product and rounding hypotheses are those of
    inner_counting_schedule. Additionally, each block is an independent run;
    exact transitions use its fixed ideal bin kernel, and offset randomness is
    fresh conditional on the current bin and independent of future transition
    randomness. An approximate or noisy transition
    must not be substituted without charging its whole-trajectory error.

    In a stationary block, spacing ceil((7/10)*K*r) bounds lag correlation
    by 2**(-r). Relative variance of a block mean is bounded by
    ((2**r+1)/(2**r-1))*v/N. Chebyshev makes block failure <=p, where
    block_failure_target=p is exact and in (0,1/4], defaulting to 1/8;
    a bounded odd number of independent blocks gives a high-confidence median.
    The default count uses the exact worst-case binomial majority tail; the
    conservative Hoeffding count remains selectable for comparison.
    Larger lag_error_bits trades more transitions for fewer costly evaluations.
    """
    if isinstance(lag_error_bits, bool) or not isinstance(lag_error_bits, int) or lag_error_bits < 1:
        raise ValueError("lag_error_bits must be a positive integer")
    block_failure = _validate_failure_bound(block_failure_target)
    reference = inner_counting_schedule(
        d, bin_scale, annealing_height, relative_accuracy, failure_probability,
        sigma_policy=sigma_policy, correction_support=correction_support,
        annealing_step=annealing_step, inverse_gap_bound=inverse_gap_bound,
    )
    j, sigma, theta = reference.annealing_step, reference.sigma, reference.failure_probability
    gap = reference.inverse_gap_bound
    spacing = ceil_fraction(LN2_UPPER * gap * lag_error_bits)
    lag_denominator = 1 << lag_error_bits
    inflation = Fraction(lag_denominator + 1, lag_denominator - 1)
    ratio_variance = Fraction(1, 8)
    lower, upper = reference.correction_lower_bound, reference.correction_upper_bound
    correction_variance = (upper - lower)**2 / (4 * lower * upper)
    ratio_count = ceil_fraction(inflation * ratio_variance / (block_failure * sigma**2))
    correction_count = ceil_fraction(inflation * correction_variance / (block_failure * sigma**2))
    tail_bits = ceil_log2(4 * (j + 1) / theta)
    blocks = median_block_count(tail_bits, failure_bound=block_failure, policy=median_policy)
    total_blocks = (j + 1) * blocks
    ratios = j * blocks * ratio_count
    corrections = blocks * correction_count
    offsets = d * corrections
    # Only the initial state of each block is coupled to stationarity.
    # Exact subsequent transitions need no per-step approximation allowance.
    coupled_draws = total_blocks + offsets
    draw_bits = ceil_log2(8 * coupled_draws / theta)
    burn_in = mixing_steps(gap, reference.log2_inverse_min_mass_bound, draw_bits)
    post_burn_transitions = blocks * (j * (ratio_count - 1) + correction_count - 1) * spacing
    work = OracleWorkCounts(
        total_blocks * burn_in + post_burn_transitions,
        ratios,
        corrections,
        offsets,
        ratios + corrections,
        total_blocks,
        (j + 1) * blocks * (blocks - 1) // 2,
    )
    return InnerBlockSchedule(
        reference, lag_error_bits, spacing, inflation, ratio_variance,
        correction_variance, ratio_count, correction_count, block_failure,
        median_policy, tail_bits, blocks, majority_failure_bound(blocks, block_failure), total_blocks,
        coupled_draws, draw_bits, burn_in, work,
    )


def positive_rational_median(values: Sequence[int | Fraction]) -> Fraction:
    """Exact middle order statistic of an odd positive rational sequence.

    Explicit insertion uses at most B*(B-1)/2 rational comparisons, with
    bounded work even on a statistical failure event. Positivity and interval
    containment are unconditional. Does not claim the median is unbiased.
    """
    if not values or len(values) % 2 == 0:
        raise ValueError("median requires a nonempty odd number of values")
    ordered: list[Fraction] = []
    for value in values:
        if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
            raise TypeError("median values must be exact rationals")
        value = Fraction(value)
        if value <= 0:
            raise ValueError("median values must be positive")
        index = len(ordered)
        while index > 0 and ordered[index - 1] > value:
            index -= 1
        ordered.insert(index, value)
    return ordered[len(ordered) // 2]


def work_difference(block: OracleWorkCounts, independent: OracleWorkCounts) -> dict[str, int]:
    """Per-category change; operation categories must not be conflated with time."""
    return {
        name: getattr(block, name) - getattr(independent, name)
        for name in OracleWorkCounts.__dataclass_fields__
    }
