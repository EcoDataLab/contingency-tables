"""Exact finite-state cycle heat baths for experiments on small table fibers.

The catalog and its selection probabilities are fixed by the input, never by
the current state. A returned kernel is exact; no general mixing-rate claim is
made. Catalog enumeration and full-fiber enumeration can be exponential.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from typing import Iterable, Sequence

from .tables import (ComputationBudgetExceeded, ExactTableSampler, ProductWeights,
                     Table, TableProblem, ZeroMassError, _integer, _rational)


@dataclass(frozen=True)
class Cycle:
    """A canonical alternating simple cycle, encoded by a signed matrix."""

    signs: Table

    @classmethod
    def from_nodes(cls, problem: TableProblem, rows: Sequence[int], columns: Sequence[int]) -> Cycle:
        """Use +(rows[t], columns[t]) and -(rows[t+1], columns[t]), cyclically."""
        if len(rows) != len(columns) or len(rows) < 2:
            raise ValueError("a cycle needs equally many rows/columns, at least two each")
        m, n = problem.shape
        rr = tuple(_integer(i, "cycle row") for i in rows)
        cc = tuple(_integer(j, "cycle column") for j in columns)
        if len(set(rr)) != len(rr) or len(set(cc)) != len(cc):
            raise ValueError("a simple cycle may not repeat a row or column")
        if max(rr) >= m or max(cc) >= n:
            raise ValueError("cycle index is outside the table")
        signs = [[0] * n for _ in range(m)]
        for t, j in enumerate(cc):
            signs[rr[t]][j] = 1
            signs[rr[(t + 1) % len(rr)]][j] = -1
        first = next(value for row in signs for value in row if value)
        result = cls(tuple(tuple(first * value for value in row) for row in signs))
        result.validate(problem)
        return result

    @property
    def length(self) -> int:
        return sum(value != 0 for row in self.signs for value in row)

    def validate(self, problem: TableProblem) -> None:
        m, n = problem.shape
        if len(self.signs) != m or any(len(row) != n for row in self.signs):
            raise ValueError("cycle shape differs from the table")
        if any(isinstance(value, bool) or not isinstance(value, int) or value not in (-1, 0, 1)
               for row in self.signs for value in row):
            raise ValueError("cycle signs must be -1, 0, or 1")
        active_rows = [i for i in range(m) if any(self.signs[i])]
        active_columns = [j for j in range(n) if any(self.signs[i][j] for i in range(m))]
        if len(active_rows) < 2 or len(active_rows) != len(active_columns):
            raise ValueError("cycle is empty or does not alternate")
        for row in self.signs:
            if sum(row) != 0 or sum(x != 0 for x in row) not in (0, 2):
                raise ValueError("each active cycle row needs one plus and one minus")
        for j in range(n):
            column = [self.signs[i][j] for i in range(m)]
            if sum(column) != 0 or sum(x != 0 for x in column) not in (0, 2):
                raise ValueError("each active cycle column needs one plus and one minus")
        if any(self.signs[i][j] and problem.upper_bounds[i][j] == 0
               for i in range(m) for j in range(n)):
            raise ValueError("a cycle may not use a structural-zero cell")
        seen, queue = {active_rows[0]}, [active_rows[0]]
        while queue:
            node = queue.pop()
            adjacent = ([m + j for j in range(n) if self.signs[node][j]] if node < m
                        else [i for i in range(m) if self.signs[i][node - m]])
            for neighbor in adjacent:
                if neighbor not in seen:
                    seen.add(neighbor)
                    queue.append(neighbor)
        if len(seen) != len(active_rows) + len(active_columns):
            raise ValueError("the direction contains disconnected cycles")


def four_cycles(problem: TableProblem) -> tuple[Cycle, ...]:
    m, n = problem.shape
    return tuple(Cycle.from_nodes(problem, rows, columns)
                 for rows in combinations(range(m), 2)
                 for columns in combinations(range(n), 2)
                 if all(problem.upper_bounds[i][j] > 0 for i in rows for j in columns))


def simple_cycles(problem: TableProblem, *, max_length: int | None = None,
                  max_cycles: int = 10_000, max_search_nodes: int = 1_000_000) -> tuple[Cycle, ...]:
    """Enumerate all simple allowed cycles up to an optional even cell length.

    Exceeding either cap raises; a partial catalog is never silently returned.
    A caller may intentionally choose a short maximum length, but must then
    check connectivity rather than assume the resulting moves are sufficient.
    """
    _integer(max_cycles, "max_cycles", positive=True)
    _integer(max_search_nodes, "max_search_nodes", positive=True)
    m, n = problem.shape
    if max_length is None:
        max_length = 2 * min(m, n)
    else:
        _integer(max_length, "max_length", positive=True)
        if max_length < 4 or max_length % 2:
            raise ValueError("max_length must be an even integer of at least four")
    neighbors = [tuple(j for j in range(n) if problem.upper_bounds[i][j] > 0) for i in range(m)]
    reverse = [tuple(i for i in range(m) if problem.upper_bounds[i][j] > 0) for j in range(n)]
    result: set[Cycle] = set()
    searched = 0
    for start in range(m):
        stack = [((start,), ())]
        while stack:
            rows, columns = stack.pop()
            searched += 1
            if searched > max_search_nodes:
                raise ComputationBudgetExceeded("cycle catalog exceeded max_search_nodes")
            last = rows[-1]
            for j in neighbors[last]:
                if j in columns:
                    continue
                for i in reverse[j]:
                    if i == start and len(rows) >= 2:
                        if columns[0] < j:  # one orientation, with the minimum row as start
                            result.add(Cycle.from_nodes(problem, rows, columns + (j,)))
                            if len(result) > max_cycles:
                                raise ComputationBudgetExceeded("cycle catalog exceeded max_cycles")
                    elif i > start and i not in rows and 2 * (len(rows) + 1) <= max_length:
                        stack.append((rows + (i,), columns + (j,)))
    return tuple(sorted(result, key=lambda cycle: (cycle.length, cycle.signs)))


def line_interval(problem: TableProblem, table: Sequence[Sequence[int]], cycle: Cycle) -> tuple[int, int]:
    """All integer shifts t for which table+t*cycle satisfies its cell bounds."""
    validated = problem.validate_table(table)
    cycle.validate(problem)
    lower, upper = None, None
    for i, row in enumerate(cycle.signs):
        for j, sign in enumerate(row):
            if sign:
                x = validated[i][j]
                lo, hi = problem.lower_bounds[i][j], problem.upper_bounds[i][j]
                left, right = ((lo - x, hi - x) if sign == 1 else (x - hi, x - lo))
                lower = left if lower is None else max(lower, left)
                upper = right if upper is None else min(upper, right)
    assert lower is not None and upper is not None and lower <= 0 <= upper
    return lower, upper


def _shift(table: Table, cycle: Cycle, amount: int) -> Table:
    return tuple(tuple(x + amount * cycle.signs[i][j] for j, x in enumerate(row))
                 for i, row in enumerate(table))


@dataclass(frozen=True)
class ExactKernel:
    states: tuple[Table, ...]
    matrix: tuple[tuple[Fraction, ...], ...]
    stationary: tuple[Fraction, ...]

    def is_stochastic(self) -> bool:
        return all(all(p >= 0 for p in row) and sum(row) == 1 for row in self.matrix)

    def satisfies_detailed_balance(self) -> bool:
        return all(self.stationary[i] * self.matrix[i][j] == self.stationary[j] * self.matrix[j][i]
                   for i in range(len(self.states)) for j in range(len(self.states)))

    def communicating_classes(self) -> tuple[tuple[int, ...], ...]:
        """Strongly connected classes, including transient zero-weight states."""
        size = len(self.states)
        reachability = []
        for start in range(size):
            seen, queue = {start}, [start]
            while queue:
                i = queue.pop()
                for j, p in enumerate(self.matrix[i]):
                    if p and j not in seen:
                        seen.add(j)
                        queue.append(j)
            reachability.append(seen)
        remaining, classes = set(range(size)), []
        while remaining:
            first = min(remaining)
            component = tuple(j for j in sorted(remaining)
                              if j in reachability[first] and first in reachability[j])
            classes.append(component)
            remaining.difference_update(component)
        return tuple(classes)

    def spectral_gap(self) -> float:
        """Numerical algebraic gap on positive target support; requires NumPy.

        This is a diagnostic for this finite instance, not a bound for a family
        of problems. It does not include computation cost per transition.
        """
        import numpy as np
        indices = [i for i, p in enumerate(self.stationary) if p]
        if len(indices) == 1:
            return 1.0
        pi = np.array([float(self.stationary[i]) for i in indices])
        if not np.isfinite(pi).all() or (pi <= 0).any():
            raise ArithmeticError("positive rational target masses are outside float64 range")
        matrix = np.array([[float(self.matrix[i][j]) for j in indices] for i in indices])
        symmetric = np.sqrt(pi[:, None] / pi[None, :]) * matrix
        if not np.isfinite(symmetric).all() or not np.allclose(symmetric, symmetric.T, atol=1e-12, rtol=1e-10):
            raise ArithmeticError("the rational kernel is not numerically representable as a reversible matrix")
        return float(1 - np.linalg.eigvalsh(symmetric)[-2])


def heat_bath_kernel(
    problem: TableProblem,
    states: Iterable[Sequence[Sequence[int]]],
    cycles: Sequence[Cycle],
    *,
    weights: ProductWeights | None = None,
    cycle_probabilities: Sequence[int | Fraction] | None = None,
    hold_probability: int | Fraction = Fraction(0),
    max_states: int = 100_000,
    max_transitions: int = 1_000_000,
    max_kernel_states: int = 2_000,
) -> ExactKernel:
    """Build a rational matrix on a verified complete, explicitly supplied fiber.

    Uniform weights give a uniform draw along the entire feasible cycle line.
    Product weights instead give its exact conditional law. A fixed mixture of
    these conditional kernels is reversible. Empty catalogs produce a hold.
    """
    _integer(max_kernel_states, "max_kernel_states", positive=True)
    # Do not materialize an arbitrarily long iterator before checking its cap.
    collected = []
    for table in states:
        if len(collected) >= max_kernel_states:
            raise ComputationBudgetExceeded("explicit kernel exceeds max_kernel_states")
        collected.append(problem.validate_table(table))
    tables = tuple(collected)
    if not tables:
        raise ValueError("a kernel requires a nonempty fiber")
    lookup = {table: i for i, table in enumerate(tables)}
    if len(lookup) != len(tables):
        raise ValueError("kernel states must be distinct")
    count = ExactTableSampler(problem, max_states=max_states, max_transitions=max_transitions).count()
    if count != len(tables):
        raise ValueError(f"states omit feasible tables: supplied {len(tables)}, exact count {count}")
    catalog = tuple(cycles)
    for cycle in catalog:
        cycle.validate(problem)
    if cycle_probabilities is None:
        choices = tuple(Fraction(1, len(catalog)) for _ in catalog)
    else:
        choices = tuple(_rational(p, "cycle probability") for p in cycle_probabilities)
        if len(choices) != len(catalog) or (catalog and sum(choices) != 1):
            raise ValueError("cycle probabilities must have catalog length and sum to one")
    hold = _rational(hold_probability, "hold_probability")
    if hold > 1:
        raise ValueError("hold_probability must be at most one")
    if weights is not None and weights.shape != problem.shape:
        raise ValueError("activities and table problem must have the same shape")
    masses = tuple(weights.table_weight(table) if weights is not None else Fraction(1) for table in tables)
    total = sum(masses, Fraction(0))
    if not total:
        raise ZeroMassError("all kernel states have zero target weight")
    matrix = [[Fraction(0) for _ in tables] for _ in tables]
    for index, table in enumerate(tables):
        if not catalog:
            matrix[index][index] = 1
            continue
        matrix[index][index] += hold
        for cycle, choice in zip(catalog, choices):
            lo, hi = line_interval(problem, table, cycle)
            targets = [lookup[_shift(table, cycle, t)] for t in range(lo, hi + 1)]
            line_mass = sum((masses[j] for j in targets), Fraction(0))
            if line_mass:
                for j in targets:
                    matrix[index][j] += (1 - hold) * choice * masses[j] / line_mass
            else:
                # A zero-mass line only contains null states of the target.
                matrix[index][index] += (1 - hold) * choice
    result = ExactKernel(tables, tuple(tuple(row) for row in matrix), tuple(m / total for m in masses))
    assert result.is_stochastic() and result.satisfies_detailed_balance()
    return result
