"""Exact counts and a rejection barrier for one uniformly padded family.

Original 2-by-n margins are (U, (n-1)U) and n columns of U. Padding every
cell by L gives first-row sum U+nL and column sums U+2L. These functions
concern uniform aggregate tables, not the conditional-worker distribution.
The obstruction is specific to this fixed padding/rejection construction.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb
from typing import Sequence

from .tables import ComputationBudgetExceeded, _integer


def _parameters(columns: int, margin: int, padding: int) -> tuple[int, int, int]:
    n = _integer(columns, "columns", positive=True)
    if n < 2:
        raise ValueError("at least two columns are required")
    return n, _integer(margin, "margin", positive=True), _integer(padding, "padding", positive=True)


def unpadding_success_upper_bound(columns: int, margin: int, padding: int) -> Fraction:
    """Universal upper bound for this family's uniform unpadding success.

    A good-to-bad incidence map has outdegree L*n*(n-1) and indegree at most
    U+1. The bound is exact for n=2. It is not a bound on other algorithms,
    nonuniform proposal laws, different padding, or arbitrary table fibers.
    """
    n, u, ell = _parameters(columns, margin, padding)
    return Fraction(u + 1, u + 1 + ell * n * (n - 1))


def half_acceptance_necessary_margin(columns: int, padding: int) -> int:
    """Necessary, not sufficient, U for success probability at least 1/2."""
    n, _, ell = _parameters(columns, 1, padding)
    return ell * n * (n - 1) - 1


def padding_target_indegree(first_row: Sequence[int], margin: int, padding: int) -> int:
    """Count incoming labeled incidences to a feasible padded first row.

    An image has exactly one first-row cell h<L, at a source column j. For
    each receiving column k!=j there are max(Y[k]-2L+h+1, 0) preimages.
    Feasible targets without a unique low cell have indegree zero.
    """
    values = tuple(_integer(value, "first-row entry") for value in first_row)
    n, u, ell = _parameters(len(values), margin, padding)
    if sum(values) != u + n * ell or any(value > u + 2 * ell for value in values):
        raise ValueError("first_row is not feasible for the padded family")
    low = [index for index, value in enumerate(values) if value < ell]
    if len(low) != 1:
        return 0
    j = low[0]
    h = values[j]
    return sum(max(value - 2 * ell + h + 1, 0)
               for k, value in enumerate(values) if k != j)


@dataclass(frozen=True)
class PaddingCountPlan:
    """Preflight bounds for an exact inclusion-exclusion count.

    ``binomial_order_sum`` is the sum of symmetric lower arguments of all
    binomial evaluations. It is a work proxy, not a count of the internal
    operations used by Python's ``math.comb``. ``integer_bit_bound`` bounds
    the nonnegative counts, signed terms, and partial sums conservatively.
    """

    inclusion_exclusion_terms: int
    binomial_evaluations: int
    binomial_order_sum: int
    integer_bit_bound: int


def _comb_plan(top: int, bottom: int) -> tuple[int, int]:
    order = min(bottom, top - bottom)
    # choose(top, order) <= top**order; the extra bit covers order=0.
    return order, 1 + order * top.bit_length()


def padding_count_plan(
    columns: int,
    margin: int,
    padding: int,
    *,
    max_terms: int = 1000,
    max_binomial_order_sum: int = 100_000,
    max_integer_bits: int = 1_000_000,
) -> PaddingCountPlan:
    """Reject excessive work before any binomial coefficient is evaluated."""
    term_limit = _integer(max_terms, "max_terms")
    order_limit = _integer(max_binomial_order_sum, "max_binomial_order_sum")
    bit_limit = _integer(max_integer_bits, "max_integer_bits")
    n, u, ell = _parameters(columns, margin, padding)
    row_sum = u + n * ell
    cell_cap = u + 2 * ell
    maximum_k = min(n, row_sum // (cell_cap + 1))
    terms = maximum_k + 1
    if terms > term_limit:
        raise ComputationBudgetExceeded(
            f"count needs {terms} inclusion-exclusion terms, exceeding max_terms={term_limit}"
        )
    order_sum, good_bits = _comb_plan(u + n - 1, n - 1)
    term_bits = 0
    for k in range(terms):
        coefficient_order, coefficient_bits = _comb_plan(n, k)
        count_order, count_bits = _comb_plan(row_sum - k * (cell_cap + 1) + n - 1, n - 1)
        order_sum += coefficient_order + count_order
        term_bits = max(term_bits, coefficient_bits + count_bits)
    integer_bits = max(good_bits, term_bits + terms.bit_length())
    if order_sum > order_limit:
        raise ComputationBudgetExceeded(
            f"binomial order sum {order_sum} exceeds max_binomial_order_sum={order_limit}"
        )
    if integer_bits > bit_limit:
        raise ComputationBudgetExceeded(
            f"conservative integer bound {integer_bits} bits exceeds max_integer_bits={bit_limit}"
        )
    return PaddingCountPlan(terms, 1 + 2 * terms, order_sum, integer_bits)


@dataclass(frozen=True)
class PaddingCounts:
    """Exact numbers of successful and all uniform padded tables."""

    columns: int
    margin: int
    padding: int
    good: int
    total: int
    plan: PaddingCountPlan

    @property
    def success_probability(self) -> Fraction:
        return Fraction(self.good, self.total)

    @property
    def success_upper_bound(self) -> Fraction:
        return unpadding_success_upper_bound(self.columns, self.margin, self.padding)


def count_padded_tables(
    columns: int,
    margin: int,
    padding: int,
    *,
    max_terms: int = 1000,
    max_binomial_order_sum: int = 100_000,
    max_integer_bits: int = 1_000_000,
) -> PaddingCounts:
    """Compute exact stars-and-bars and capped-composition counts.

    For S=U+nL and C=U+2L, good=choose(U+n-1,n-1) and total equals
    sum((-1)**k * choose(n,k) * choose(S-k*(C+1)+n-1,n-1)). All arithmetic
    is integer/rational. The finite sum can contain severe cancellation;
    floating-point evaluation would not be a substitute for this count.
    """
    plan = padding_count_plan(columns, margin, padding, max_terms=max_terms,
                              max_binomial_order_sum=max_binomial_order_sum,
                              max_integer_bits=max_integer_bits)
    n, u, ell = _parameters(columns, margin, padding)
    row_sum, cell_cap = u + n * ell, u + 2 * ell
    good = comb(u + n - 1, n - 1)
    total = sum((-1)**k * comb(n, k) * comb(row_sum - k * (cell_cap + 1) + n - 1, n - 1)
                for k in range(plan.inclusion_exclusion_terms))
    if total < good or good < 1:
        raise ArithmeticError("inclusion-exclusion count violates good <= total")
    return PaddingCounts(n, u, ell, good, total, plan)
