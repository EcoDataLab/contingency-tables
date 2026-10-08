"""Exact schedule arithmetic for conditional improvements to OpenAI result #115.

This module computes *budgets*, not samples or a counting estimate.  A caller
must supply a proved inverse-gap bound for its actual lazy reversible chain.
The source-derived defaults refer to the pinned manuscript's original scales.
No function certifies a modified chain, a compiled machine, or a tabulated law.
All decisions use integers and Fraction; no floating-point logarithms occur.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb, prod
from typing import Callable, Literal, Sequence


# exp(7/10) > sum_{j=0}^4 (7/10)^j/j! > 2, so ln(2) < 7/10.
LN2_UPPER = Fraction(7, 10)


def _integer(name: str, value: int, minimum: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")
    return value


def _rational(name: str, value: int | Fraction) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise TypeError(f"{name} must be an int or Fraction, not a float")
    return Fraction(value)


def ceil_fraction(value: int | Fraction) -> int:
    value = _rational("value", value)
    return -(-value.numerator // value.denominator)


def ceil_log2(value: int | Fraction) -> int:
    """Smallest integer n with value <= 2**n, including negative answers."""
    value = _rational("value", value)
    if value <= 0:
        raise ValueError("value must be positive")
    p, q = value.numerator, value.denominator
    exponent = p.bit_length() - q.bit_length()
    below = p <= (q << exponent) if exponent >= 0 else (p << -exponent) <= q
    return exponent if below else exponent + 1


def mixing_steps(
    inverse_gap_bound: int | Fraction,
    log2_inverse_min_mass_bound: int | Fraction,
    error_bits: int,
) -> int:
    """Steps for TV <= 2**(-error_bits), conditional on the named bounds.

    Uses TV <= .5 * sqrt(pi_min**(-1)-1) * exp(-t/K).  The chain
    must be finite, lazy, and reversible, and K must be at least one.
    A singleton may be handled deterministically instead of calling this.
    """
    gap = _rational("inverse_gap_bound", inverse_gap_bound)
    mass = _rational("log2_inverse_min_mass_bound", log2_inverse_min_mass_bound)
    _integer("error_bits", error_bits, 1)
    if gap < 1 or mass < 0:
        raise ValueError("inverse gap must be >= 1 and mass bound must be >= 0")
    exponent = max(Fraction(0), mass / 2 + error_bits - 1)
    return ceil_fraction(gap * LN2_UPPER * exponent)


def sampling_small_gap_bound(d: int, small_width: int | None = None) -> int:
    """Published explicit K6, with optional *conditional* width substitution.

    The original theorem has d >= 14 and U=d**20.  A different small_width
    requires its own proof of every scale-dependent hypothesis.
    """
    _integer("d", d, 14)
    u = d**20 if small_width is None else _integer("small_width", small_width, 1)
    return 128 * d**2 * ((1 + 2 * d**2) * 4 * d**2 * (u + 1) ** 6 + 2)


def sampling_dense_gap_bound(
    d: int, bin_scale: int | None = None, *, sharp_constant: bool = True
) -> int:
    """K from manuscript dense conductance; new bin scales are conditional.

    The proof gives ln(2)/(1024*d**2*(4*B)) before its displayed 1e5
    relaxation.  ln(2) >= 2/3 yields the integer constant 1536.
    """
    _integer("d", d, 14)
    b = d**8 if bin_scale is None else _integer("bin_scale", bin_scale, 1)
    constant = 1536 if sharp_constant else 100_000
    return 2 * (constant * d**2 * (4 * b)) ** 2


def sampling_dense_mass_bound(d: int, penalty: int, bin_scale: int) -> int:
    """Conditional log2(pi_min**-1) allowance from the manuscript weights."""
    _integer("d", d, 1)
    _integer("penalty", penalty, 1)
    _integer("bin_scale", bin_scale, 1)
    return 4 * penalty * d + d * ceil_log2(4 * bin_scale)


@dataclass(frozen=True)
class OuterSchedule:
    dimension: int
    binary_length: int
    accuracy_bits: int
    inverse_gap_bound: Fraction
    trials: int
    steps_per_trial: int
    dense_accuracy_bits: int
    trial_mixing_bits: int


def outer_schedule(
    d: int, b: int, k: int, *, inverse_gap_bound: int | Fraction | None = None
) -> OuterSchedule:
    """Three outer error terms are each <= 2**(-k-2).

    Requires success >= 1/(2*(1+d*d)), pi_min >= 2**(-2*d*b),
    independent trials, fresh completion randomness, and feasible fallback.
    """
    _integer("d", d, 14)
    _integer("b", b, d)
    _integer("k", k, 1)
    gap = _rational(
        "inverse_gap_bound",
        sampling_small_gap_bound(d) if inverse_gap_bound is None else inverse_gap_bound,
    )
    trials = ceil_fraction(LN2_UPPER * 2 * (1 + d**2) * (k + 2))
    mixing_bits = k + 2 + ceil_log2(trials)
    steps = mixing_steps(gap, 2 * d * b, mixing_bits)
    precision = k + 2 + ceil_log2(trials * (steps + 1))
    return OuterSchedule(d, b, k, gap, trials, steps, precision, mixing_bits)


@dataclass(frozen=True)
class DenseSchedule:
    dimension: int
    accuracy_bits: int
    inverse_gap_bound: Fraction
    log2_inverse_min_mass_bound: Fraction
    trials: int
    steps_per_trial: int
    draw_error_bits: int


def dense_schedule(
    d: int,
    h: int,
    *,
    inverse_gap_bound: int | Fraction | None = None,
    log2_inverse_min_mass_bound: int | Fraction | None = None,
) -> DenseSchedule:
    """Dense failure and total coupled-draw error are each <= 2**(-h-2).

    Requires ideal success >= 1/64 and at most d scalar offsets per trial.
    Defaults use original A=d**4, B=d**8 and extracted conductance constants.
    """
    _integer("d", d, 14)
    _integer("h", h, 1)
    gap = _rational(
        "inverse_gap_bound",
        sampling_dense_gap_bound(d) if inverse_gap_bound is None else inverse_gap_bound,
    )
    mass = _rational(
        "log2_inverse_min_mass_bound",
        sampling_dense_mass_bound(d, d**4, d**8)
        if log2_inverse_min_mass_bound is None
        else log2_inverse_min_mass_bound,
    )
    trials = ceil_fraction(64 * LN2_UPPER * (h + 2))
    draw_bits = h + 2 + ceil_log2(trials * (1 + d))
    return DenseSchedule(d, h, gap, mass, trials, mixing_steps(gap, mass, draw_bits), draw_bits)


def dyadic_offset_bits(width: int, tolerance: int | Fraction) -> int:
    """Sufficient bits for floor(width*U/2**bits) within the given TV error.

    The exact TV is r*(width-r)/(width*2**bits), r=2**bits mod width.
    Thus width/(4*2**bits) suffices, saving up to two bits against the
    manuscript's width/2**bits bound.  Power-of-two widths admit exact draws.
    """
    _integer("width", width, 1)
    tolerance = _rational("tolerance", tolerance)
    if not 0 < tolerance < 1:
        raise ValueError("tolerance must lie strictly between zero and one")
    bits = max(0, ceil_log2(Fraction(width, 4) / tolerance))
    if width & (width - 1) == 0:
        bits = min(bits, width.bit_length() - 1)
    return bits


def dyadic_offset_tv(width: int, bits: int) -> Fraction:
    """Exact finite-law discrepancy; intended for modest verification cases."""
    _integer("width", width, 1)
    _integer("bits", bits)
    outcomes = 1 << bits
    remainder = outcomes % width
    return Fraction(remainder * (width - remainder), width * outcomes)


@dataclass(frozen=True)
class DyadicDenominatorBudget:
    bin_transition_bits: int
    scalar_offset_bits: int
    dense_trial_bits: int
    dense_call_bits: int
    outer_trial_bits: int
    outer_call_bits: int


def dyadic_denominator_budget(
    outer: OuterSchedule,
    dense: DenseSchedule,
    *,
    acceptance_exponent_bound: int | None = None,
) -> DyadicDenominatorBudget:
    """Updated common denominator allowance, conditional on law propagation.

    Assumes scalar widths <= 2**b and floor-map offsets chosen by
    dyadic_offset_bits. Adjacent original bin exponents differ by at most
    one, because p is (d/B)-Lipschitz and Ad/B=d**(-3)<=1. Different scales
    must supply their own bound unless they also prove Ad/B<=1.
    This computes an allowance, not the actual output numerators.
    """
    if outer.dimension != dense.dimension or outer.dense_accuracy_bits != dense.accuracy_bits:
        raise ValueError("dense schedule must serve the specified outer schedule")
    d = outer.dimension
    exponent = 1 if acceptance_exponent_bound is None else _integer(
        "acceptance_exponent_bound", acceptance_exponent_bound
    )
    transition = ceil_log2(8 * d) + exponent
    offset = max(0, outer.binary_length + dense.draw_error_bits - 2)
    dense_trial = dense.steps_per_trial * transition + d * offset
    dense_call = dense.trials * dense_trial
    outer_trial = outer.steps_per_trial * (dense_call + ceil_log2(32 * d**2)) + dense_call
    return DyadicDenominatorBudget(
        transition, offset, dense_trial, dense_call, outer_trial, outer.trials * outer_trial
    )


def table_count_upper_bound(rows: Sequence[int], columns: Sequence[int]) -> int:
    """Elementary integer upper bound for ordinary nonnegative tables.

    Combines row/column weak compositions and an injective free-cell display.
    Equal totals and nonnegative integer margins are required.  This also
    upper-bounds a capped subfiber, but is not a bounded-fiber feasibility test.
    """
    if not rows or not columns:
        raise ValueError("use nonempty row and column margin sequences")
    for value in (*rows, *columns):
        _integer("margin", value)
    if sum(rows) != sum(columns):
        raise ValueError("row and column totals must agree")
    m, n = len(rows), len(columns)
    row_bound = prod(comb(value + n - 1, n - 1) for value in rows)
    column_bound = prod(comb(value + m - 1, m - 1) for value in columns)
    widths = [[min(row, column) + 1 for column in columns] for row in rows]
    total_box = prod(prod(row) for row in widths)
    row_products = [prod(row) for row in widths]
    column_products = [prod(widths[i][j] for i in range(m)) for j in range(n)]
    # All entries outside any chosen row and column determine the rest.
    free_bound = min(
        total_box * widths[i][j] // (row_products[i] * column_products[j])
        for i in range(m)
        for j in range(n)
    )
    return min(row_bound, column_bound, free_bound)


def domination_accuracy_bits(count_upper_bound: int, gate_bits: int) -> int:
    """Least nonnegative k with M_bound*(2**D-1) <= 2**k.

    This is the sharp integer criterion furnished by the additive TV bound,
    eta <= delta/(M_bound*(1-delta)).  Avoids constructing 2**D.
    A known singleton can instead be returned deterministically.
    """
    _integer("count_upper_bound", count_upper_bound, 1)
    _integer("gate_bits", gate_bits, 1)
    if gate_bits == 1:
        return ceil_log2(count_upper_bound)
    floor_log = count_upper_bound.bit_length() - 1
    # Is M*(2**D-1) <= 2**(floor_log+D)?
    excess = count_upper_bound - (1 << floor_log)
    return floor_log + gate_bits + int(excess > (count_upper_bound >> gate_bits))


@dataclass(frozen=True)
class ExactCorrectionSchedule:
    dimension: int
    binary_length: int
    rare_cost_exponent: int
    gate_bits: int
    accuracy_bits: int
    cost_slack_bits: int
    count_upper_bound: int | None


def exact_correction_schedule(
    d: int,
    b: int,
    *,
    rare_cost_exponent: int = 500,
    count_upper_bound: int | None = None,
    cost_slack_bits: int = 0,
) -> ExactCorrectionSchedule:
    """Separate domination and rare-cost precision, using a certified cost.

    Conditional cost must be <= 2**(a*d*b)*poly(d,b,k).  D=a*d*b+s
    then leaves multiplier 2**(-s) in expectation; s=0 already suffices.
    The original manuscript certifies a=500 for its original program.
    A revised sampler still needs a revised law and machine-cost proof.
    """
    _integer("d", d, 14)
    _integer("b", b, d)
    _integer("rare_cost_exponent", rare_cost_exponent, 1)
    _integer("cost_slack_bits", cost_slack_bits)
    gate = rare_cost_exponent * d * b + cost_slack_bits
    precision = (
        gate + d * b
        if count_upper_bound is None
        else domination_accuracy_bits(count_upper_bound, gate)
    )
    return ExactCorrectionSchedule(
        d, b, rare_cost_exponent, gate, max(1, precision), cost_slack_bits, count_upper_bound
    )


def rare_branch_gate(next_bit: Callable[[], int], gate_bits: int) -> tuple[bool, int]:
    """Read until the first one, or D zeroes; return (rare_branch, bits_read).

    Requires independent fair next_bit draws.  It reads fewer than two bits
    in expectation; the worst case still reads D.  Subsequent sampler draws
    must use fresh independent bits, not replay already inspected bits.
    """
    _integer("gate_bits", gate_bits, 1)
    for reads in range(1, gate_bits + 1):
        bit = next_bit()
        if bit not in (0, 1):
            raise ValueError("next_bit must return zero or one")
        if bit:
            return False, reads
    return True, gate_bits


def residual_weights(numerators: Sequence[int], denominator_bits: int, gate_bits: int) -> tuple[int, ...]:
    """Residual weights for an actual dyadic law on the COMPLETE target fiber.

    Verifies normalization and nonnegative residuals.  Does not obtain or
    certify the actual sampler law; callers must tabulate that separately.
    Include every feasible target, including zero-probability outcomes.
    Omitting one changes the uniform target and invalidates exactness.
    """
    _integer("denominator_bits", denominator_bits)
    _integer("gate_bits", gate_bits, 1)
    if not numerators:
        raise ValueError("law must have nonempty support")
    for value in numerators:
        _integer("numerator", value)
    denominator = 1 << denominator_bits
    if sum(numerators) != denominator:
        raise ValueError("dyadic numerators must sum to the denominator")
    count = len(numerators)
    weights = tuple(
        (denominator << gate_bits) - count * ((1 << gate_bits) - 1) * value
        for value in numerators
    )
    if min(weights) < 0:
        raise ValueError("ordinary law is not pointwise dominated at this gate probability")
    return weights


def counting_bin_gap_bound(d: int, bin_scale: int, *, sharp_constant: bool = True) -> int:
    """Conditional K from bounded paper's conductance proof (1024 vs 10000)."""
    _integer("d", d, 1)
    _integer("bin_scale", bin_scale, 1)
    constant = 1024 if sharp_constant else 10_000
    return 2 * (constant * d**2 * bin_scale) ** 2


@dataclass(frozen=True)
class InnerCountingSchedule:
    dimension: int
    bin_scale: int
    annealing_height: int
    relative_accuracy: Fraction
    failure_probability: Fraction
    sigma: Fraction
    concentration: str
    allocation: str
    concentration_denominator: Fraction
    ratio_concentration_denominator: Fraction
    average_tail_bits: int
    ratio_samples_per_average: int
    correction_samples: int
    total_draw_bound: int
    draw_error_bits: int
    inverse_gap_bound: Fraction
    steps_per_bin_sample: int

    @property
    def samples_per_average(self) -> int:
        """Common sufficient maximum; range-specific ratio counts may be less."""
        return self.correction_samples


def inner_counting_schedule(
    d: int,
    bin_scale: int,
    annealing_height: int,
    relative_accuracy: int | Fraction,
    failure_probability: int | Fraction,
    *,
    concentration: Literal["hoeffding", "bernstein"] = "bernstein",
    allocation: Literal["common", "by_range"] = "by_range",
    inverse_gap_bound: int | Fraction | None = None,
) -> InnerCountingSchedule:
    """Independent inner-oracle averages; not an outer-trajectory guarantee.

    Requires ideal observables in [1/8,4] (ratios in [1/2,1]), fresh
    independent samples, <= H+1 averages, the original coupling/rounding,
    and pi_min**-1 <= 2**H * B**d for each bin chain. By default, the
    narrower ratio range receives fewer samples. Only correction samples
    need offsets; Q=H*N_ratio+(d+1)*N_correction bounds all draws.
    """
    _integer("d", d, 1)
    _integer("bin_scale", bin_scale, 1)
    _integer("annealing_height", annealing_height)
    xi = _rational("relative_accuracy", relative_accuracy)
    theta = _rational("failure_probability", failure_probability)
    if not (0 < xi < Fraction(1, 4) and 0 < theta < Fraction(1, 4)):
        raise ValueError("accuracy and failure probability must lie in (0, 1/4)")
    height = annealing_height
    sigma = xi / (50 * (height + 1))
    if concentration == "hoeffding":
        denominator = Fraction(961, 2)
        ratio_denominator = Fraction(1, 2)
    elif concentration == "bernstein":
        denominator = Fraction(961, 64) + Fraction(62, 3) * sigma
        ratio_denominator = Fraction(1, 4) + Fraction(2, 3) * sigma
    else:
        raise ValueError("concentration must be 'hoeffding' or 'bernstein'")
    average_bits = ceil_log2(8 * (height + 1) / theta)
    samples = ceil_fraction(LN2_UPPER * denominator * average_bits / sigma**2)
    if allocation == "common":
        ratio_samples = samples
    elif allocation == "by_range":
        ratio_samples = ceil_fraction(LN2_UPPER * ratio_denominator * average_bits / sigma**2)
    else:
        raise ValueError("allocation must be 'common' or 'by_range'")
    draws = height * ratio_samples + (d + 1) * samples
    draw_bits = ceil_log2(8 * draws / theta)
    gap = _rational(
        "inverse_gap_bound",
        counting_bin_gap_bound(d, bin_scale) if inverse_gap_bound is None else inverse_gap_bound,
    )
    mass_bits = height + d * ceil_log2(bin_scale)
    steps = mixing_steps(gap, mass_bits, draw_bits)
    return InnerCountingSchedule(
        d, bin_scale, height, xi, theta, sigma, concentration, allocation, denominator,
        ratio_denominator, average_bits, ratio_samples, samples, draws, draw_bits, gap, steps,
    )
