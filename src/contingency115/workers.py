"""Exact ordinary conditional-worker tables by sampling without replacement.

This is a classical conditional-independence law, not uniform aggregate tables:
P(X) is proportional to 1 / product(factorial(X[i][j])). The implementation
uses integer urn draws and a Fenwick tree; no table enumeration is needed.
There is no support for cell bounds, structural zeros, or interaction weights.
Numeric worker count, not its binary encoding length, controls the draw budget.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import random
from typing import Sequence

from .tables import (ComputationBudgetExceeded, InfeasibleTableError,
                     RandomIntegerSource, Table, _integer)


def _margins(row_sums: Sequence[int], column_sums: Sequence[int]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    rows = tuple(_integer(value, "row margin") for value in row_sums)
    columns = tuple(_integer(value, "column margin") for value in column_sums)
    if not rows or not columns:
        raise ValueError("at least one row and one column are required")
    if sum(rows) != sum(columns):
        raise InfeasibleTableError("row and column grand totals must agree")
    return rows, columns


@dataclass(frozen=True)
class WorkerLinearMoments:
    """Exact expectation and variance of a linear observable under the law."""

    mean: Fraction
    variance: Fraction


def worker_linear_moments(
    row_sums: Sequence[int],
    column_sums: Sequence[int],
    coefficients: Sequence[Sequence[int | Fraction]],
    *,
    max_cells: int = 1_000_000,
) -> WorkerLinearMoments:
    """Evaluate full-covariance linear moments without simulation or factorials.

    Coefficients can be signed integers or Fractions, but not floats. This
    ordinary unbounded-table formula takes O(m*n) rational operations; unlike
    the sampler it has no loop over the numeric worker total. For total 0 or
    1 the table is deterministic. This does not describe bounds or nonseparable
    activity-weighted laws.
    """
    cell_limit = _integer(max_cells, "max_cells")
    rows, columns = _margins(row_sums, column_sums)
    m, n = len(rows), len(columns)
    if m * n > cell_limit:
        raise ComputationBudgetExceeded(
            f"moment calculation needs {m * n} coefficients, exceeding max_cells={cell_limit}"
        )
    if len(coefficients) != m or any(len(row) != n for row in coefficients):
        raise ValueError(f"coefficients must have shape {m} by {n}")
    column_totals = [Fraction(0)] * n
    linear_total = Fraction(0)
    square_total = Fraction(0)
    row_square_total = Fraction(0)
    for i, row in enumerate(coefficients):
        row_total = Fraction(0)
        for j, value in enumerate(row):
            if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
                raise TypeError("coefficients must be integers or Fractions")
            coefficient = Fraction(value)
            row_total += columns[j] * coefficient
            column_totals[j] += rows[i] * coefficient
            square_total += rows[i] * columns[j] * coefficient**2
        linear_total += rows[i] * row_total
        row_square_total += rows[i] * row_total**2
    total = sum(rows)
    if total == 0:
        return WorkerLinearMoments(Fraction(0), Fraction(0))
    mean = linear_total / total
    if total == 1:
        return WorkerLinearMoments(mean, Fraction(0))
    column_square_total = sum(columns[j] * value**2
                              for j, value in enumerate(column_totals))
    variance = (total**2 * square_total
                - total * (row_square_total + column_square_total)
                + linear_total**2) / (total**2 * (total - 1))
    return WorkerLinearMoments(mean, variance)


@dataclass(frozen=True)
class WorkerSamplingPlan:
    """Conservative work limits determined before any random choices.

    ``maximum_random_draws`` counts calls to ``randrange``, not random bits or
    elapsed time. ``output_cells`` bounds the dense output allocation. The
    largest row is reserved for deterministic completion (last index on ties).
    """

    workers: int
    rows: int
    columns: int
    output_cells: int
    final_row: int
    maximum_random_draws: int


@dataclass(frozen=True)
class WorkerSample:
    """One exact draw with implementation work counters.

    ``deterministically_assigned_workers`` includes the final row and any
    assignments after only one column category remains. ``fenwick_steps``
    counts initialization, selection, and decrement loop iterations. Integer
    size and RNG-internal work are not counted by those loop iterations.
    """

    table: Table
    random_draws: int
    deterministically_assigned_workers: int
    fenwick_steps: int


class _FenwickCounts:
    """Nonnegative category counts with logarithmic rank selection."""

    def __init__(self, counts: Sequence[int]) -> None:
        self.size = len(counts)
        self.tree = [0, *counts]
        self.steps = 0
        for i in range(1, self.size + 1):
            self.steps += 1
            parent = i + (i & -i)
            if parent <= self.size:
                self.tree[parent] += self.tree[i]

    def select(self, rank: int) -> int:
        """Return the zero-based category containing a zero-based urn rank."""
        index = 0
        bit = 1 << (self.size.bit_length() - 1)
        while bit:
            self.steps += 1
            candidate = index + bit
            if candidate <= self.size and self.tree[candidate] <= rank:
                index = candidate
                rank -= self.tree[candidate]
            bit >>= 1
        return index

    def decrement(self, column: int) -> None:
        index = column + 1
        while index <= self.size:
            self.steps += 1
            self.tree[index] -= 1
            index += index & -index


@dataclass(frozen=True, init=False)
class OrdinaryWorkerSampler:
    """Sample the ordinary fixed-margin conditional-worker law exactly.

    Only plain row and column margins are accepted. All cells are allowed;
    this API intentionally does not accept ``TableProblem`` or activities.
    Positive row-times-column activity factors would cancel from this law,
    but arbitrary cell interactions would not.

    Construction validates and copies margins, then rejects an inadequate
    ``max_draws`` or ``max_cells`` before any RNG is accepted or output table
    allocated. Limits are nonnegative integers. A conservative draw bound is
    N - max(row_sums); it is zero when at most one row or column is positive.
    The actual draw count can be smaller because the last remaining category
    is filled without randomness. No attempt is made to continue a rejected
    plan in the hope of reaching that favorable branch.

    With D actual random draws and m by n output, time is
    O(m*n + m + n + D*log(n+1)) integer operations and O(m*n + m + n)
    stored integers. Counts have O(log(N+1)) bits. This is not a polynomial
    bound in the binary margin length. Conditional on past calls, an RNG must
    return each integer in range(stop) with exactly equal probability.
    """

    row_sums: tuple[int, ...]
    column_sums: tuple[int, ...]
    plan: WorkerSamplingPlan

    def __init__(
        self,
        row_sums: Sequence[int],
        column_sums: Sequence[int],
        *,
        max_draws: int = 1_000_000,
        max_cells: int = 1_000_000,
    ) -> None:
        draw_limit = _integer(max_draws, "max_draws")
        cell_limit = _integer(max_cells, "max_cells")
        rows, columns = _margins(row_sums, column_sums)
        total = sum(rows)
        output_cells = len(rows) * len(columns)
        final_row = max(range(len(rows)), key=lambda i: (rows[i], i))
        positive_rows = sum(value > 0 for value in rows)
        positive_columns = sum(value > 0 for value in columns)
        maximum_draws = (total - rows[final_row]
                         if positive_rows > 1 and positive_columns > 1 else 0)
        if output_cells > cell_limit:
            raise ComputationBudgetExceeded(
                f"output needs {output_cells} cells, exceeding max_cells={cell_limit}"
            )
        if maximum_draws > draw_limit:
            raise ComputationBudgetExceeded(
                f"plan may need {maximum_draws} integer draws, "
                f"exceeding max_draws={draw_limit}"
            )
        object.__setattr__(self, "row_sums", rows)
        object.__setattr__(self, "column_sums", columns)
        object.__setattr__(self, "plan", WorkerSamplingPlan(
            total, len(rows), len(columns), output_cells, final_row, maximum_draws
        ))

    def sample(self, rng: RandomIntegerSource | None = None) -> Table:
        """Draw one aggregate table; use ``sample_with_stats`` for counters."""
        return self.sample_with_stats(rng).table

    def sample_with_stats(self, rng: RandomIntegerSource | None = None) -> WorkerSample:
        """Draw using an already accepted plan, with no data-dependent cutoff."""
        source = rng if rng is not None else random.SystemRandom()
        remaining = list(self.column_sums)
        table = [[0] * self.plan.columns for _ in self.row_sums]
        active_columns = sum(value > 0 for value in remaining)
        remaining_total = self.plan.workers
        counts = _FenwickCounts(remaining)
        sole_column = None
        draws = 0

        for i, row_total in enumerate(self.row_sums):
            if i == self.plan.final_row:
                continue
            left = row_total
            while left:
                if active_columns == 1:
                    if sole_column is None:
                        sole_column = counts.select(0)
                    table[i][sole_column] += left
                    remaining[sole_column] -= left
                    remaining_total -= left
                    # No later random selection is possible. The Fenwick tree
                    # need not track these deterministic decrements.
                    break
                rank = _integer(source.randrange(remaining_total), "RNG output")
                if rank >= remaining_total:
                    raise ValueError("RNG output must be less than its stop argument")
                column = counts.select(rank)
                table[i][column] += 1
                remaining[column] -= 1
                counts.decrement(column)
                active_columns -= remaining[column] == 0
                remaining_total -= 1
                draws += 1
                left -= 1

        table[self.plan.final_row] = remaining
        return WorkerSample(tuple(map(tuple, table)), draws,
                            self.plan.workers - draws, counts.steps)
