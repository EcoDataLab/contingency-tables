"""Exact linear bounds on bounded integer-table fibers, with certificates.

This is a small rational-arithmetic min-cost-flow implementation, not a new
optimization algorithm or an implementation of the sampling theorem in #115.
It never enumerates tables. A work limit aborts instead of returning an
uncertified endpoint. See docs/linear-bounds.md for the certificate proof and
the limits of the work budget and complexity claims.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from math import lcm
from typing import Sequence

from .tables import ComputationBudgetExceeded, InfeasibleTableError, Table, TableProblem


Costs = tuple[tuple[Fraction, ...], ...]


def _rational(value: object, name: str) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise TypeError(f"{name} must be an int or Fraction")
    return Fraction(value)


def _costs(problem: TableProblem, values: Sequence[Sequence[int | Fraction]]) -> Costs:
    if not isinstance(problem, TableProblem):
        raise TypeError("problem must be a TableProblem")
    m, n = problem.shape
    if len(values) != m or any(len(row) != n for row in values):
        raise ValueError(f"costs must have shape {m} by {n}")
    return tuple(tuple(_rational(value, f"costs[{i}][{j}]") for j, value in enumerate(row))
                 for i, row in enumerate(values))


def _residual_margins(problem: TableProblem) -> tuple[list[int], list[int]]:
    m, n = problem.shape
    if sum(problem.row_sums) != sum(problem.column_sums):
        raise InfeasibleTableError("row and column totals differ")
    if any(problem.lower_bounds[i][j] > problem.upper_bounds[i][j]
           for i in range(m) for j in range(n)):
        raise InfeasibleTableError("a required cell exceeds its effective cap")
    rows = [problem.row_sums[i] - sum(problem.lower_bounds[i]) for i in range(m)]
    columns = [problem.column_sums[j] - sum(problem.lower_bounds[i][j] for i in range(m))
               for j in range(n)]
    if min(rows + columns) < 0:
        raise InfeasibleTableError("lower bounds exceed a margin")
    return rows, columns


@dataclass(frozen=True)
class LinearCertificate:
    """Exact row/column potentials and a claimed original-objective endpoint."""

    maximize: bool
    row_potentials: tuple[Fraction, ...]
    column_potentials: tuple[Fraction, ...]
    bound: Fraction


@dataclass(frozen=True)
class LinearOptimum:
    table: Table
    certificate: LinearCertificate
    augmentations: int
    work_used: int

    @property
    def value(self) -> Fraction:
        return self.certificate.bound


@dataclass(frozen=True)
class LinearBounds:
    minimum: LinearOptimum
    maximum: LinearOptimum

    @property
    def work_used(self) -> int:
        return self.minimum.work_used + self.maximum.work_used


@dataclass(frozen=True)
class FlowCutCertificate:
    """Source-side rows and columns of an insufficient lower-shifted flow cut."""

    rows: tuple[int, ...]
    columns: tuple[int, ...]
    capacity: int
    required: int


class InfeasibleFlowError(InfeasibleTableError):
    """A support/capacity obstruction with an independently checkable cut."""

    def __init__(self, certificate: FlowCutCertificate) -> None:
        self.certificate = certificate
        super().__init__(f"cell support/caps allow a cut capacity of {certificate.capacity}, "
                         f"below required flow {certificate.required}; source-side rows "
                         f"{certificate.rows}, columns {certificate.columns}")


def verify_optimality(
    problem: TableProblem, costs: Sequence[Sequence[int | Fraction]],
    table: Sequence[Sequence[int]], certificate: LinearCertificate,
) -> bool:
    """Check a witness and primal/dual equality without running an optimizer.

    Malformed costs raise as in ``optimize_linear``; an invalid witness or
    certificate returns False. Work is O(rows*columns) arithmetic operations,
    with no search, enumeration, feasibility solve, or reliance on solver state.
    """
    values = _costs(problem, costs)
    if not isinstance(certificate, LinearCertificate) or not isinstance(certificate.maximize, bool):
        return False
    m, n = problem.shape
    try:
        witness = problem.validate_table(table)
        if len(certificate.row_potentials) != m or len(certificate.column_potentials) != n:
            return False
        rows = tuple(_rational(p, "row potential") for p in certificate.row_potentials)
        columns = tuple(_rational(p, "column potential") for p in certificate.column_potentials)
        bound = _rational(certificate.bound, "bound")
    except (TypeError, ValueError):
        return False
    sign = -1 if certificate.maximize else 1
    primal = sum((values[i][j] * witness[i][j] for i in range(m) for j in range(n)), Fraction(0))
    dual = (sum((columns[j] * problem.column_sums[j] for j in range(n)), Fraction(0))
            - sum((rows[i] * problem.row_sums[i] for i in range(m)), Fraction(0)))
    for i in range(m):
        for j in range(n):
            reduced = sign * values[i][j] + rows[i] - columns[j]
            lower, upper = problem.lower_bounds[i][j], problem.upper_bounds[i][j]
            if witness[i][j] < upper and reduced < 0:
                return False
            if witness[i][j] > lower and reduced > 0:
                return False
            dual += min(reduced * lower, reduced * upper)
    return primal == bound and sign * bound == dual


def verify_infeasibility(problem: TableProblem, certificate: FlowCutCertificate) -> bool:
    """Check a deficient cut directly from the constraints, with no flow solve."""
    if not isinstance(problem, TableProblem) or not isinstance(certificate, FlowCutCertificate):
        return False
    try:
        rows, columns = _residual_margins(problem)
    except InfeasibleTableError:
        return False  # These simpler contradictions do not require a cut.
    m, n = problem.shape
    for indices, size in ((certificate.rows, m), (certificate.columns, n)):
        if not isinstance(indices, tuple) or any(
            isinstance(i, bool) or not isinstance(i, int) or not 0 <= i < size for i in indices
        ) or len(set(indices)) != len(indices):
            return False
    if any(isinstance(value, bool) or not isinstance(value, int)
           for value in (certificate.capacity, certificate.required)):
        return False
    selected_rows, selected_columns = set(certificate.rows), set(certificate.columns)
    capacity = (sum(rows[i] for i in range(m) if i not in selected_rows)
                + sum(columns[j] for j in selected_columns)
                + sum(problem.upper_bounds[i][j] - problem.lower_bounds[i][j]
                      for i in selected_rows for j in range(n) if j not in selected_columns))
    return capacity == certificate.capacity < certificate.required == sum(rows)


class _WorkBudget:
    def __init__(self, limit: int) -> None:
        if isinstance(limit, bool) or not isinstance(limit, int):
            raise TypeError("max_work must be an integer (not a bool)")
        if limit < 1:
            raise ValueError("max_work must be positive")
        self.limit, self.used = limit, 0

    def scan(self) -> None:
        if self.used >= self.limit:
            raise ComputationBudgetExceeded(
                f"linear optimization exceeded max_work={self.limit} residual arc examinations; "
                "no result is available")
        self.used += 1


@dataclass
class _Arc:
    to: int
    reverse: int
    capacity: int
    cost: int


def _distances(graph: list[list[_Arc]], source: int | None, budget: _WorkBudget) -> list[int | None]:
    # source=None is a zero-cost supersource to every node. Its distances are
    # feasible potentials exactly when the residual network has no negative cycle.
    size = len(graph)
    distances: list[int | None] = ([0] * size if source is None else [None] * size)
    if source is not None:
        distances[source] = 0
    for _ in range(size):
        changed = False
        for u, arcs in enumerate(graph):
            for arc in arcs:
                budget.scan()
                if arc.capacity == 0 or distances[u] is None:
                    continue
                candidate = distances[u] + arc.cost
                if distances[arc.to] is None or candidate < distances[arc.to]:
                    distances[arc.to] = candidate
                    changed = True
        if not changed:
            return distances
    raise RuntimeError("negative residual cycle: the min-cost-flow invariant failed")


def _optimize(problem: TableProblem, costs: Costs, maximize: bool, budget: _WorkBudget) -> LinearOptimum:
    start_work = budget.used
    rows, columns = _residual_margins(problem)
    m, n = problem.shape
    source, sink = m + n, m + n + 1
    graph: list[list[_Arc]] = [[] for _ in range(sink + 1)]
    # Multiplication by this positive common denominator preserves all path
    # comparisons, ties, and optima. Integer path arithmetic avoids repeated
    # Fraction normalization; returned potentials are divided back exactly.
    denominator = 1
    for row in costs:
        for value in row:
            denominator = lcm(denominator, value.denominator)

    def edge(u: int, v: int, capacity: int, cost: int) -> _Arc:
        forward = _Arc(v, len(graph[v]), capacity, cost)
        backward = _Arc(u, len(graph[u]), 0, -cost)
        graph[u].append(forward)
        graph[v].append(backward)
        return forward

    for i, amount in enumerate(rows):
        if amount:
            edge(source, i, amount, 0)
    for j, amount in enumerate(columns):
        if amount:
            edge(m + j, sink, amount, 0)
    sign = -1 if maximize else 1
    cells: list[tuple[int, int, _Arc]] = []
    for i in range(m):
        for j in range(n):
            capacity = problem.upper_bounds[i][j] - problem.lower_bounds[i][j]
            if capacity:
                integer_cost = costs[i][j].numerator * (denominator // costs[i][j].denominator)
                cells.append((i, j, edge(i, m + j, capacity, sign * integer_cost)))

    required, flow, augmentations = sum(rows), 0, 0
    while flow < required:
        distances = _distances(graph, source, budget)
        if distances[sink] is None:
            reachable_rows = tuple(i for i in range(m) if distances[i] is not None)
            reachable_columns = tuple(j for j in range(n) if distances[m + j] is not None)
            cut = FlowCutCertificate(reachable_rows, reachable_columns, flow, required)
            if not verify_infeasibility(problem, cut):
                raise RuntimeError("internal infeasibility certificate did not verify")
            raise InfeasibleFlowError(cut)

        # Recover a simple shortest path through tight arcs. This also avoids
        # depending on predecessor tie-breaking in the presence of zero-cost cycles.
        parents: list[tuple[int, _Arc] | None] = [None] * len(graph)
        visited, queue = {source}, deque([source])
        while queue and sink not in visited:
            u = queue.popleft()
            for arc in graph[u]:
                budget.scan()
                if (arc.capacity and arc.to not in visited and distances[u] is not None
                        and distances[arc.to] == distances[u] + arc.cost):
                    parents[arc.to] = (u, arc)
                    visited.add(arc.to)
                    queue.append(arc.to)
        if parents[sink] is None:
            raise RuntimeError("a finite shortest-path distance had no tight path")
        amount, v = required - flow, sink
        path = []
        while v != source:
            parent = parents[v]
            assert parent is not None
            u, arc = parent
            amount = min(amount, arc.capacity)
            path.append((u, arc))
            v = u
        for u, arc in path:
            arc.capacity -= amount
            graph[arc.to][arc.reverse].capacity += amount
        flow += amount
        augmentations += 1

    witness = [list(row) for row in problem.lower_bounds]
    for i, j, arc in cells:
        witness[i][j] += graph[arc.to][arc.reverse].capacity
    table = tuple(tuple(row) for row in witness)
    potentials = _distances(graph, None, budget)
    assert all(p is not None for p in potentials)
    certificate = LinearCertificate(
        maximize,
        tuple(Fraction(potentials[i], denominator) for i in range(m)),
        tuple(Fraction(potentials[m + j], denominator) for j in range(n)),
        sum((costs[i][j] * table[i][j] for i in range(m) for j in range(n)), Fraction(0)),
    )
    if not verify_optimality(problem, costs, table, certificate):
        raise RuntimeError("internal optimality certificate did not verify")
    return LinearOptimum(table, certificate, augmentations, budget.used - start_work)


def optimize_linear(
    problem: TableProblem, costs: Sequence[Sequence[int | Fraction]], *,
    maximize: bool = False, max_work: int = 1_000_000,
) -> LinearOptimum:
    """Find one exact endpoint and integer witness for sum(costs[i,j]*X[i,j]).

    Costs must be int/Fraction, including negative rationals; floats and bools
    are rejected. ``max_work`` bounds residual arc examinations across shortest
    paths, tight-path searches, and final potentials. It does not bound input
    size, integer bit lengths, setup/verification work, memory, or elapsed time.
    Infeasibility raises InfeasibleTableError; a support/capacity failure raises
    its InfeasibleFlowError subclass with a checkable cut certificate.
    """
    values = _costs(problem, costs)
    if not isinstance(maximize, bool):
        raise TypeError("maximize must be a bool")
    budget = _WorkBudget(max_work)
    return _optimize(problem, values, maximize, budget)


def linear_bounds(
    problem: TableProblem, costs: Sequence[Sequence[int | Fraction]], *,
    max_work: int = 2_000_000,
) -> LinearBounds:
    """Both sharp endpoints, using one shared work budget for the two solves.

    If either solve fails, no partial LinearBounds is returned. The endpoints
    enclose every feasible table under any probability law supported there;
    they are not a confidence interval or a claim that all intermediate values
    can be attained.
    """
    values = _costs(problem, costs)
    budget = _WorkBudget(max_work)
    minimum = _optimize(problem, values, False, budget)
    maximum = _optimize(problem, values, True, budget)
    return LinearBounds(minimum, maximum)
