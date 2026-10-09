"""Exact stationary variance diagnostics for bounded finite reversible kernels.

These are algebraic diagnostics, not cold-start convergence or runtime claims.
The asymptotic variance is lim(n * Var(mean(f(X_1), ..., f(X_n))))
under a stationary start. This definition includes periodic kernels.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

from .kernels import ExactKernel
from .tables import ComputationBudgetExceeded


@dataclass(frozen=True)
class StationaryVariance:
    mean: Fraction
    variance: Fraction
    between_class_variance: Fraction
    asymptotic_variance: Fraction | None
    variance_inflation_factor: Fraction | None
    positive_support_classes: tuple[tuple[int, ...], ...]
    component_means: tuple[Fraction, ...]
    status: str

    @property
    def irreducible_on_positive_support(self) -> bool:
        return len(self.positive_support_classes) == 1


def _fraction(value: int | Fraction) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise ValueError("exact diagnostics require integers or Fractions")
    return Fraction(value)


def _bounded(value: Fraction, max_bits: int) -> Fraction:
    if max(value.numerator.bit_length(), value.denominator.bit_length()) > max_bits:
        raise ComputationBudgetExceeded("exact diagnostic exceeded max_rational_bits")
    return value


def _solve(matrix: list[list[Fraction]], rhs: list[Fraction], max_bits: int) -> list[Fraction]:
    """Rational elimination with post-operation retained-result bit checks.

    Temporary products/sums before Fraction reduction are not preflight capped.
    """
    size = len(rhs)
    rows = [row[:] + [value] for row, value in zip(matrix, rhs)]
    for column in range(size):
        pivot = next((i for i in range(column, size) if rows[i][column]), None)
        if pivot is None:
            raise ValueError("singular Poisson system")
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = rows[column][column]
        rows[column][column:] = [_bounded(x / scale, max_bits) for x in rows[column][column:]]
        for i in range(column + 1, size):
            scale = rows[i][column]
            if scale:
                rows[i][column:] = [_bounded(x - scale * y, max_bits)
                                   for x, y in zip(rows[i][column:], rows[column][column:])]
    result = [Fraction(0)] * size
    for i in reversed(range(size)):
        result[i] = _bounded(rows[i][-1] - sum((rows[i][j] * result[j]
                                               for j in range(i + 1, size)), Fraction()), max_bits)
    return result


def stationary_variance(kernel: ExactKernel, values: Sequence[int | Fraction], *,
                        max_states: int = 48, max_rational_bits: int = 4096) -> StationaryVariance:
    """Solve (I-P+1*pi)h=f-E_pi[f] in each positive-mass closed class.

    If component means differ, stationary sample-mean variance has a positive
    limit and n times that variance diverges; asymptotic_variance is None and
    status is 'infinite_between_classes'. Identical class means permit a finite
    stationary-ensemble variance but do not imply fixed-start target sampling.
    Zero observable variance and zero asymptotic variance are explicit statuses;
    neither is assigned an ESS. Zero-target states are excluded from the solve.
    """
    for bound in (max_states, max_rational_bits):
        if type(bound) is not int or bound < 1:
            raise ValueError("diagnostic budgets must be positive integers")
    size = len(kernel.states)
    if size > max_states:
        raise ComputationBudgetExceeded("exact diagnostic exceeded max_states")
    if not size or len(values) != size or len(kernel.matrix) != size or len(kernel.stationary) != size:
        raise ValueError("kernel and observable dimensions differ or are empty")
    if any(len(row) != size for row in kernel.matrix) or len(set(kernel.states)) != size:
        raise ValueError("kernel must be square with distinct states")
    matrix = tuple(tuple(_bounded(_fraction(p), max_rational_bits) for p in row) for row in kernel.matrix)
    pi = tuple(_bounded(_fraction(p), max_rational_bits) for p in kernel.stationary)
    observable = tuple(_bounded(_fraction(value), max_rational_bits) for value in values)
    checked = ExactKernel(kernel.states, matrix, pi)
    if any(p < 0 for p in pi) or sum(pi) != 1 or not checked.is_stochastic():
        raise ValueError("kernel must have stochastic rows and a probability stationary vector")
    if not checked.satisfies_detailed_balance():
        raise ValueError("kernel must be reversible for the supplied stationary law")
    classes = tuple(tuple(i for i in component if pi[i]) for component in checked.communicating_classes()
                    if any(pi[i] for i in component))
    mean = _bounded(sum((p * f for p, f in zip(pi, observable)), Fraction()), max_rational_bits)
    variance = _bounded(sum((p * (f - mean) ** 2 for p, f in zip(pi, observable)), Fraction()), max_rational_bits)
    masses = tuple(_bounded(sum((pi[i] for i in component), Fraction()), max_rational_bits) for component in classes)
    means = tuple(_bounded(sum((pi[i] * observable[i] for i in component), Fraction()) / mass, max_rational_bits)
                  for component, mass in zip(classes, masses))
    between = _bounded(sum((mass * (mu - mean) ** 2 for mass, mu in zip(masses, means)), Fraction()), max_rational_bits)
    if between:
        return StationaryVariance(mean, variance, between, None, None, classes, means, "infinite_between_classes")
    if not variance:
        return StationaryVariance(mean, variance, between, Fraction(0), None, classes, means, "zero_observable_variance")
    asymptotic = Fraction(0)
    for component, mass, mu in zip(classes, masses, means):
        target = [_bounded(pi[i] / mass, max_rational_bits) for i in component]
        centered = [_bounded(observable[i] - mu, max_rational_bits) for i in component]
        poisson = [[_bounded(Fraction(i == j) - matrix[a][b] + target[j], max_rational_bits)
                    for j, b in enumerate(component)] for i, a in enumerate(component)]
        solution = _solve(poisson, centered, max_rational_bits)
        # Verify the exact equations, rather than relying solely on elimination.
        if any(sum((poisson[i][j] * solution[j] for j in range(len(component))), Fraction()) != centered[i]
               for i in range(len(component))):
            raise ArithmeticError("Poisson-equation verification failed")
        local_variance = _bounded(sum((p * f * f for p, f in zip(target, centered)), Fraction()), max_rational_bits)
        local_av = _bounded(2 * sum((p * f * h for p, f, h in zip(target, centered, solution)), Fraction()) - local_variance, max_rational_bits)
        asymptotic = _bounded(asymptotic + mass * local_av, max_rational_bits)
    if asymptotic < 0:
        raise ArithmeticError("reversible asymptotic variance cannot be negative")
    status = "zero_asymptotic_variance" if not asymptotic else "finite"
    return StationaryVariance(mean, variance, between, asymptotic, _bounded(asymptotic / variance, max_rational_bits),
                              classes, means, status)
