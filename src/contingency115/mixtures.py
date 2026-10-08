"""Exact finite-instance certificates for input-fixed reversible mixtures.

This module checks rational matrices; it neither enumerates a table fiber nor
claims a polynomial-time sampler. ``gap`` means the Poincare (algebraic) gap.
For mixtures of conditional heat baths, each component is a positive
semidefinite projection in L2(pi), so this also controls absolute relaxation.
For arbitrary reversible matrices, a negative eigenvalue can control mixing
instead and is not bounded by these certificates.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import lcm
from typing import Sequence

from .kernels import ExactKernel
from .tables import ComputationBudgetExceeded


def _fraction(value: int | Fraction, name: str) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise TypeError(f"{name} must be an integer or Fraction")
    return Fraction(value)


def _state_cap(size: int, max_states: int) -> None:
    if isinstance(max_states, bool) or not isinstance(max_states, int) or max_states < 1:
        raise ValueError("max_states must be a positive integer")
    if size > max_states:
        raise ComputationBudgetExceeded("exact certificate exceeded max_states")


def _validated(kernel: ExactKernel, max_states: int) -> tuple[Fraction, ...]:
    size = len(kernel.states)
    _state_cap(size, max_states)
    if not size or len(set(kernel.states)) != size:
        raise ValueError("kernel states must be nonempty and distinct")
    if len(kernel.matrix) != size or any(len(row) != size for row in kernel.matrix):
        raise ValueError("kernel matrix must have one row and column per state")
    if len(kernel.stationary) != size:
        raise ValueError("stationary law must have one entry per state")
    pi = tuple(_fraction(p, "stationary mass") for p in kernel.stationary)
    if any(p < 0 for p in pi) or sum(pi) != 1:
        raise ValueError("stationary masses must be nonnegative and sum to one")
    for row in kernel.matrix:
        rational = tuple(_fraction(p, "transition probability") for p in row)
        if any(p < 0 for p in rational) or sum(rational) != 1:
            raise ValueError("transition rows must be nonnegative and sum to one")
    if not kernel.satisfies_detailed_balance():
        raise ValueError("kernel must satisfy exact detailed balance")
    return pi


def _probabilities(values: Sequence[int | Fraction], size: int) -> tuple[Fraction, ...]:
    result = tuple(_fraction(value, "mixture probability") for value in values)
    if len(result) != size or not result or any(value < 0 for value in result) or sum(result) != 1:
        raise ValueError("mixture probabilities must be nonnegative, have the required length, and sum to one")
    return result


def _family(kernels: Sequence[ExactKernel], max_states: int) -> tuple[ExactKernel, ...]:
    result = tuple(kernels)
    if not result:
        raise ValueError("a mixture needs at least one kernel")
    first = result[0]
    for kernel in result:
        _validated(kernel, max_states)
        if kernel.states != first.states or kernel.stationary != first.stationary:
            raise ValueError("all kernels need the same state order and stationary law")
    return result


def fixed_mixture(kernels: Sequence[ExactKernel], probabilities: Sequence[int | Fraction],
                  *, max_states: int = 128) -> ExactKernel:
    """Combine exactly checked kernels using state-independent probabilities."""
    family = _family(kernels, max_states)
    choices = _probabilities(probabilities, len(family))
    size = len(family[0].states)
    matrix = tuple(tuple(sum((choice * kernel.matrix[i][j]
                             for choice, kernel in zip(choices, family)), Fraction(0))
                         for j in range(size)) for i in range(size))
    return ExactKernel(family[0].states, matrix, family[0].stationary)


@dataclass(frozen=True)
class PSDCheck:
    """Result of exact symmetric fraction-free elimination.

    Positive pivots have the same signs as LDL pivots. A zero pivot is accepted
    only when its remaining row vanishes. The returned counters are a receipt;
    the rational input matrix is the replayable certificate.
    """

    is_psd: bool
    dimension: int
    positive_pivots: int
    zero_pivots: int
    failure_index: int | None
    maximum_stored_entry_bits: int


def check_psd(matrix: Sequence[Sequence[int | Fraction]], *, max_states: int = 128) -> PSDCheck:
    """Decide positive semidefiniteness over the rationals, without floats.

    Clear all denominators by one positive multiplier and use the symmetric
    Bareiss recurrence. Exact division is asserted at every step. The state cap
    bounds matrix dimension, not integer bit lengths, wall time, or memory.
    """
    size = len(matrix)
    _state_cap(size, max_states)
    if any(len(row) != size for row in matrix):
        raise ValueError("PSD input must be square")
    rational = [[_fraction(value, "matrix entry") for value in row] for row in matrix]
    if any(rational[i][j] != rational[j][i] for i in range(size) for j in range(i)):
        raise ValueError("PSD input must be exactly symmetric")
    denominator = lcm(*(value.denominator for row in rational for value in row))
    work = [[value.numerator * (denominator // value.denominator) for value in row]
            for row in rational]
    max_bits = max((abs(value).bit_length() for row in work for value in row), default=0)
    previous, positive, zero = 1, 0, 0
    for k in range(size):
        pivot = work[k][k]
        if pivot < 0 or (pivot == 0 and any(work[k][j] for j in range(k + 1, size))):
            return PSDCheck(False, size, positive, zero, k, max_bits)
        if pivot == 0:
            zero += 1
            continue
        positive += 1
        for i in range(k + 1, size):
            for j in range(i, size):
                numerator = pivot * work[i][j] - work[i][k] * work[k][j]
                quotient, remainder = divmod(numerator, previous)
                if remainder:
                    raise ArithmeticError("fraction-free PSD elimination was not exact")
                work[i][j] = work[j][i] = quotient
                max_bits = max(max_bits, abs(quotient).bit_length())
        for i in range(k + 1, size):
            work[i][k] = work[k][i] = 0
        previous = pivot
    return PSDCheck(True, size, positive, zero, None, max_bits)


@dataclass(frozen=True)
class GapLowerCertificate:
    bound: Fraction
    positive_support: tuple[int, ...]
    psd: PSDCheck

    @property
    def certified(self) -> bool:
        return self.psd.is_psd


def certify_gap_lower_bound(kernel: ExactKernel, bound: int | Fraction, *,
                            max_states: int = 128) -> GapLowerCertificate:
    """Check ``D(I-P) - bound*(D-pi*pi.T)`` is positive semidefinite.

    Null target states are excluded. On positive support the matrix has zero
    row sums, so deleting any one row and the matching column preserves the
    PSD question. A singleton support has gap one by convention. ``bound`` is
    constrained to [0, 2], the range of a reversible algebraic gap.
    """
    pi = _validated(kernel, max_states)
    gamma = _fraction(bound, "gap lower bound")
    if not 0 <= gamma <= 2:
        raise ValueError("gap lower bound must lie in [0, 2]")
    support = tuple(i for i, p in enumerate(pi) if p)
    if len(support) == 1:
        return GapLowerCertificate(gamma, support, PSDCheck(gamma <= 1, 0, 0, 0,
                                                           None if gamma <= 1 else 0, 0))
    principal = tuple(tuple(pi[i] * ((1 if i == j else 0) - kernel.matrix[i][j])
                            - gamma * ((pi[i] if i == j else 0) - pi[i] * pi[j])
                            for j in support[:-1]) for i in support[:-1])
    return GapLowerCertificate(gamma, support, check_psd(principal, max_states=max_states))


def _variance(pi: Sequence[Fraction], values: Sequence[Fraction]) -> Fraction:
    mean = sum((p * f for p, f in zip(pi, values)), Fraction(0))
    return sum((p * (f - mean) ** 2 for p, f in zip(pi, values)), Fraction(0))


def _rayleigh(kernel: ExactKernel, values: Sequence[Fraction], variance: Fraction) -> Fraction:
    # Detailed balance turns the half-sum over ordered pairs into this sum.
    energy = sum((kernel.stationary[i] * kernel.matrix[i][j] * (values[i] - values[j]) ** 2
                  for i in range(len(values)) for j in range(i)), Fraction(0))
    return energy / variance


def rayleigh_quotient(kernel: ExactKernel, values: Sequence[int | Fraction], *,
                       max_states: int = 128) -> Fraction:
    """An exact upper bound on the gap from any nonconstant rational vector."""
    pi = _validated(kernel, max_states)
    vector = tuple(_fraction(value, "witness value") for value in values)
    if len(vector) != len(pi):
        raise ValueError("witness needs one value per state")
    variance = _variance(pi, vector)
    if variance == 0:
        raise ValueError("witness must be nonconstant on positive target support")
    return _rayleigh(kernel, vector, variance)


@dataclass(frozen=True)
class MixtureGapUpperCertificate:
    bound: Fraction
    component_bounds: tuple[Fraction, ...]


def mixture_gap_upper_bound(kernels: Sequence[ExactKernel],
                            witnesses: Sequence[Sequence[int | Fraction]],
                            probabilities: Sequence[int | Fraction], *,
                            max_states: int = 128) -> MixtureGapUpperCertificate:
    """Bound the gap of *every* fixed mixture of the supplied kernels.

    For witness probabilities a_j and rational functions f_j, every mixture
    has gap at most max_i sum_j a_j R(P_i, f_j). This is a finite dual witness;
    it proves no global optimality beyond this specific component family.
    """
    family = _family(kernels, max_states)
    vectors = tuple(tuple(_fraction(value, "witness value") for value in vector)
                    for vector in witnesses)
    choices = _probabilities(probabilities, len(vectors))
    if any(len(vector) != len(family[0].states) for vector in vectors):
        raise ValueError("each witness needs one value per state")
    variances = tuple(_variance(family[0].stationary, vector) for vector in vectors)
    if any(variance == 0 for variance in variances):
        raise ValueError("each witness must be nonconstant on positive target support")
    bounds = tuple(sum((choice * _rayleigh(kernel, vector, variance)
                        for choice, vector, variance in zip(choices, vectors, variances)), Fraction(0))
                   for kernel in family)
    return MixtureGapUpperCertificate(max(bounds), bounds)
