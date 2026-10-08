"""Arithmetic bounds for sequential padding of ordinary uniform tables.

These are conditional count/probability bounds, not a sampler. Every padded
cell must have both ORIGINAL incident margins at least minimum_margin. The
argument does not extend unchanged to cell bounds or nonuniform weights.
"""

from dataclasses import dataclass
from fractions import Fraction

from .scales import SamplingScales, proposed_scales, shape_aware_scales
from .tables import _integer


def growth_envelope(rate: int | Fraction) -> Fraction:
    """Bound (1+x)^q when x>=0 and 0<=q*x=rate<3.

    E(t) = (t^2+4t+6)/(6-2t). Its exact recurrence satisfies
    E(t+x)>=(1+x)E(t) whenever t,x>=0 and t+x<3, so induction
    gives the power bound without evaluating an enormous integer power.
    """
    if isinstance(rate, bool) or not isinstance(rate, (int, Fraction)):
        raise TypeError("rate must be an integer or Fraction")
    t = Fraction(rate)
    if not 0 <= t < 3:
        raise ValueError("the rational envelope requires 0 <= rate < 3")
    return (t*t + 4*t + 6) / (6 - 2*t)


@dataclass(frozen=True)
class PaddingGrowthBound:
    unit_increments: int
    donor_pairs: int
    minimum_margin: int
    rate: Fraction
    count_growth_upper_bound: Fraction
    acceptance_lower_bound: Fraction


def sequential_padding_bound(unit_increments: int, donor_pairs: int,
                             minimum_margin: int) -> PaddingGrowthBound:
    """Return the conditional enlarged-count ratio and success bound.

    Each unit addition has count ratio <=1+e/(U+1), where e is the donor
    pair count and U the original incident-margin lower bound. Telescoping
    q additions bounds the total ratio by E(q*e/(U+1)). The acceptance
    interpretation requires a nonempty ordinary fiber. Zero increments
    or zero donors give exactly one. Rates >=3 are rejected explicitly;
    that is a limit of this envelope, not evidence of infeasibility.
    """
    q = _integer(unit_increments, "unit_increments")
    e = _integer(donor_pairs, "donor_pairs")
    U = _integer(minimum_margin, "minimum_margin")
    rate = Fraction(q*e, U+1)
    growth = growth_envelope(rate)
    return PaddingGrowthBound(q, e, U, rate, growth, 1/growth)


def sequential_scales(d: int) -> SamplingScales:
    """Use U=47d^5; g,e<=d and L=32d^3 give rate<=32/47.

    E(32/47)=10147/5123<2, hence successful unpadding exceeds one half.
    Remaining dense and transport interfaces retain their separate proof
    obligations. This changes a constant, not the conditional exponent25.
    """
    s = proposed_scales(d)
    return SamplingScales(d, s.A, s.B, s.L, 47*d**5)


def sequential_shape_scales(rows: int, columns: int) -> SamplingScales:
    """Use full dimensions to avoid circular threshold selection.

    With g=mn, e=(m-1)(n-1), choose U=max(2L,47d^3*g*e-1).
    Then q*e/(U+1)<=32/47 for q<=gL. Singleton dimensions
    have e=0 and use U=2L; their fiber is deterministic.
    """
    s = shape_aware_scales(rows, columns)
    e = (rows-1)*(columns-1)
    U = max(2*s.L, 47*s.d**3*rows*columns*e-1)
    return SamplingScales(s.d, s.A, s.B, s.L, U)
