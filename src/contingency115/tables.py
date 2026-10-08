"""Exact reference algorithms for small integer-table fibers.

These algorithms are not the polynomial-time algorithms of OpenAI result #115.
All probabilities use integer/Fraction arithmetic; resource exhaustion raises
instead of returning a partial count or a biased draw.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from math import factorial, gcd
import random
from typing import Iterable, Iterator, Protocol, Sequence


Table = tuple[tuple[int, ...], ...]
Cell = tuple[int, int]
Rational = int | Fraction


class RandomIntegerSource(Protocol):
    """A source that returns a uniform integer in ``range(stop)``."""

    def randrange(self, stop: int) -> int: ...


class ComputationBudgetExceeded(RuntimeError):
    """An exact computation was stopped before it could produce a result."""


class InfeasibleTableError(ValueError):
    """No table satisfies the supplied constraints."""


class ZeroMassError(ValueError):
    """Feasible tables exist, but all have zero weight under the target law."""


def _integer(value: object, name: str, *, positive: bool = False) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an integer (not a bool)")
    if value < (1 if positive else 0):
        raise ValueError(f"{name} must be {'positive' if positive else 'nonnegative'}")
    return value


def _rational(value: object, name: str) -> Fraction:
    # Refuse floating point: Fraction(float) would silently encode its binary
    # approximation as though it were the intended exact scientific input.
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise TypeError(f"{name} must be an int or Fraction")
    result = Fraction(value)
    if result < 0:
        raise ValueError(f"{name} must be nonnegative")
    return result


def _matrix(values: Sequence[Sequence[int]], m: int, n: int, name: str) -> Table:
    if len(values) != m or any(len(row) != n for row in values):
        raise ValueError(f"{name} must have shape {m} by {n}")
    return tuple(tuple(_integer(x, f"{name}[{i}][{j}]")
                       for j, x in enumerate(row)) for i, row in enumerate(values))


@dataclass(frozen=True)
class FeasibilityResult:
    feasible: bool
    table: Table | None
    reason: str


@dataclass(frozen=True, init=False)
class TableProblem:
    """Nonnegative integer tables with fixed margins and inclusive cell bounds.

    Zero upper bounds specify structural zeros. Margins and bounds are copied
    into immutable tuples. Upper bounds are tightened by the row/column margins.
    Malformed inputs raise immediately; a well-formed empty fiber has count zero
    and ``feasibility().feasible == False``.
    """

    row_sums: tuple[int, ...]
    column_sums: tuple[int, ...]
    lower_bounds: Table
    upper_bounds: Table

    def __init__(
        self,
        row_sums: Sequence[int],
        column_sums: Sequence[int],
        upper_bounds: Sequence[Sequence[int]] | None = None,
        lower_bounds: Sequence[Sequence[int]] | None = None,
        structural_zeros: Iterable[Cell] = (),
    ) -> None:
        rows = tuple(_integer(x, "row margin") for x in row_sums)
        columns = tuple(_integer(x, "column margin") for x in column_sums)
        if not rows or not columns:
            raise ValueError("at least one row and one column are required")
        m, n = len(rows), len(columns)
        lower = (_matrix(lower_bounds, m, n, "lower_bounds") if lower_bounds is not None
                 else tuple((0,) * n for _ in rows))
        supplied_upper = (_matrix(upper_bounds, m, n, "upper_bounds")
                          if upper_bounds is not None else None)
        if supplied_upper is not None and any(
            lower[i][j] > supplied_upper[i][j] for i in range(m) for j in range(n)
        ):
            raise ValueError("a supplied lower bound exceeds its supplied upper bound")
        upper = [[min(rows[i], columns[j], supplied_upper[i][j])
                  if supplied_upper is not None else min(rows[i], columns[j])
                  for j in range(n)] for i in range(m)]
        for cell in structural_zeros:
            if len(cell) != 2:
                raise ValueError("a structural zero must be a (row, column) pair")
            i, j = (_integer(cell[0], "structural-zero row"),
                    _integer(cell[1], "structural-zero column"))
            if i >= m or j >= n:
                raise ValueError("structural-zero index is outside the table")
            upper[i][j] = 0
        object.__setattr__(self, "row_sums", rows)
        object.__setattr__(self, "column_sums", columns)
        object.__setattr__(self, "lower_bounds", lower)
        object.__setattr__(self, "upper_bounds", tuple(tuple(row) for row in upper))

    @property
    def shape(self) -> tuple[int, int]:
        return len(self.row_sums), len(self.column_sums)

    def transpose(self) -> TableProblem:
        """Transpose constraints; useful when the mode dimension is much smaller."""
        # A contradictory structural zero may have upper < lower. Preserve the
        # empty fiber by not routing it through supplied-bound validation.
        result = object.__new__(TableProblem)
        object.__setattr__(result, "row_sums", self.column_sums)
        object.__setattr__(result, "column_sums", self.row_sums)
        object.__setattr__(result, "lower_bounds", tuple(zip(*self.lower_bounds)))
        object.__setattr__(result, "upper_bounds", tuple(zip(*self.upper_bounds)))
        return result

    def validate_table(self, table: Sequence[Sequence[int]]) -> Table:
        """Return an immutable table, or raise if any constraint is violated."""
        m, n = self.shape
        result = _matrix(table, m, n, "table")
        if tuple(map(sum, result)) != self.row_sums:
            raise ValueError("table row sums do not match")
        if tuple(sum(result[i][j] for i in range(m)) for j in range(n)) != self.column_sums:
            raise ValueError("table column sums do not match")
        if any(not self.lower_bounds[i][j] <= result[i][j] <= self.upper_bounds[i][j]
               for i in range(m) for j in range(n)):
            raise ValueError("table violates a cell bound")
        return result

    def feasibility(self) -> FeasibilityResult:
        """Decide feasibility and construct a witness using integer max flow.

        Lower bounds are subtracted first. Edmonds--Karp augmentations handle
        sparse-support obstructions that marginal capacity checks miss.
        """
        m, n = self.shape
        if sum(self.row_sums) != sum(self.column_sums):
            return FeasibilityResult(False, None, "row and column totals differ")
        if any(self.lower_bounds[i][j] > self.upper_bounds[i][j]
               for i in range(m) for j in range(n)):
            return FeasibilityResult(False, None, "a required cell exceeds its effective cap")
        rows = [self.row_sums[i] - sum(self.lower_bounds[i]) for i in range(m)]
        columns = [self.column_sums[j] - sum(self.lower_bounds[i][j] for i in range(m))
                   for j in range(n)]
        if min(rows + columns) < 0:
            return FeasibilityResult(False, None, "lower bounds exceed a margin")
        source, sink = m + n, m + n + 1
        size = sink + 1
        residual: list[dict[int, int]] = [{} for _ in range(size)]
        neighbors: list[list[int]] = [[] for _ in range(size)]

        def edge(u: int, v: int, capacity: int) -> None:
            residual[u][v] = capacity
            residual[v][u] = 0
            neighbors[u].append(v)
            neighbors[v].append(u)

        for i, amount in enumerate(rows):
            edge(source, i, amount)
        for j, amount in enumerate(columns):
            edge(m + j, sink, amount)
        for i in range(m):
            for j in range(n):
                cap = self.upper_bounds[i][j] - self.lower_bounds[i][j]
                if cap:
                    edge(i, m + j, cap)
        required, flow = sum(rows), 0
        while flow < required:
            parent = [-1] * size
            parent[source] = source
            queue = deque([source])
            while queue and parent[sink] == -1:
                u = queue.popleft()
                for v in neighbors[u]:
                    if parent[v] == -1 and residual[u][v] > 0:
                        parent[v] = u
                        queue.append(v)
                        if v == sink:
                            break
            if parent[sink] == -1:
                return FeasibilityResult(False, None, "cell support/caps obstruct a feasible flow")
            amount, v = required - flow, sink
            while v != source:
                u = parent[v]
                amount = min(amount, residual[u][v])
                v = u
            v = sink
            while v != source:
                u = parent[v]
                residual[u][v] -= amount
                residual[v][u] += amount
                v = u
            flow += amount
        table = tuple(tuple(self.lower_bounds[i][j] + residual[m + j].get(i, 0)
                            for j in range(n)) for i in range(m))
        self.validate_table(table)
        return FeasibilityResult(True, table, "an integer feasible flow was found")


@dataclass(frozen=True, init=False)
class ProductWeights:
    """Exact target weight ``product(a[i,j] ** x[i,j] / x[i,j]!)``.

    The factorial divisor is used only when ``factorial_weight=True``. Without
    it, this is an aggregate-table activity law; with it, it is the conditional
    independent-Poisson/labeled-worker law. Neither law is fitted by this class.
    Activities may be zero; 0**0 is one and a positive count at zero activity has
    zero weight. Use Fraction explicitly for rational scientific inputs.
    """

    activities: tuple[tuple[Fraction, ...], ...]
    factorial_weight: bool

    def __init__(self, activities: Sequence[Sequence[Rational]],
                 factorial_weight: bool = False) -> None:
        if not activities or not activities[0]:
            raise ValueError("activities must be a nonempty matrix")
        n = len(activities[0])
        if any(len(row) != n for row in activities):
            raise ValueError("activities must be rectangular")
        if not isinstance(factorial_weight, bool):
            raise TypeError("factorial_weight must be a bool")
        converted = tuple(tuple(_rational(x, "activity") for x in row) for row in activities)
        object.__setattr__(self, "activities", converted)
        object.__setattr__(self, "factorial_weight", factorial_weight)

    @property
    def shape(self) -> tuple[int, int]:
        return len(self.activities), len(self.activities[0])

    def transpose(self) -> ProductWeights:
        return ProductWeights(tuple(zip(*self.activities)), self.factorial_weight)

    def cell_weight(self, i: int, j: int, value: int) -> Fraction:
        weight = self.activities[i][j] ** value
        return weight / factorial(value) if self.factorial_weight else weight

    def row_weight(self, i: int, values: Sequence[int]) -> Fraction:
        result = Fraction(1)
        for j, value in enumerate(values):
            result *= self.cell_weight(i, j, value)
        return result

    def table_weight(self, table: Sequence[Sequence[int]]) -> Fraction:
        m, n = self.shape
        validated = _matrix(table, m, n, "table")
        result = Fraction(1)
        for i, row in enumerate(validated):
            result *= self.row_weight(i, row)
        return result


def _bounded_vectors(total: int, lower: Sequence[int], upper: Sequence[int]) -> Iterator[tuple[int, ...]]:
    """Lexicographic bounded compositions, with no recursion in column count."""
    n = len(lower)
    lo_suffix, hi_suffix = [0] * (n + 1), [0] * (n + 1)
    for j in range(n - 1, -1, -1):
        lo_suffix[j] = lo_suffix[j + 1] + lower[j]
        hi_suffix[j] = hi_suffix[j + 1] + upper[j]
    if any(a > b for a, b in zip(lower, upper)) or not lo_suffix[0] <= total <= hi_suffix[0]:
        return

    def choices(j: int, remaining: int) -> range:
        return range(max(lower[j], remaining - hi_suffix[j + 1]),
                     min(upper[j], remaining - lo_suffix[j + 1]) + 1)

    chosen: list[int] = []
    remaining = [total]
    stack = [iter(choices(0, total))]
    while stack:
        try:
            value = next(stack[-1])
        except StopIteration:
            stack.pop()
            if chosen:
                chosen.pop()
                remaining.pop()
            continue
        j = len(stack) - 1
        if j == n - 1:
            yield tuple(chosen + [value])
        else:
            chosen.append(value)
            remaining.append(remaining[-1] - value)
            stack.append(iter(choices(j + 1, remaining[-1])))


State = tuple[int, tuple[int, ...]]


@dataclass(frozen=True)
class _Branch:
    row: tuple[int, ...]
    child: State
    mass: int | Fraction


class _CompletionEngine:
    def __init__(self, problem: TableProblem, weights: ProductWeights | None,
                 max_states: int, max_transitions: int) -> None:
        self.problem, self.weights = problem, weights
        self.max_states = _integer(max_states, "max_states", positive=True)
        self.max_transitions = _integer(max_transitions, "max_transitions", positive=True)
        if weights is not None and weights.shape != problem.shape:
            raise ValueError("activities and table problem must have the same shape")
        m, n = problem.shape
        self.suffix_lower = [[0] * n for _ in range(m + 1)]
        self.suffix_upper = [[0] * n for _ in range(m + 1)]
        self.suffix_rows = [0] * (m + 1)
        for i in range(m - 1, -1, -1):
            self.suffix_rows[i] = self.suffix_rows[i + 1] + problem.row_sums[i]
            for j in range(n):
                self.suffix_lower[i][j] = self.suffix_lower[i + 1][j] + problem.lower_bounds[i][j]
                self.suffix_upper[i][j] = self.suffix_upper[i + 1][j] + problem.upper_bounds[i][j]
        self.masses: dict[State, int | Fraction] = {}
        self.branches: dict[State, tuple[_Branch, ...]] = {}
        self.states_visited = 0
        self.transitions_visited = 0
        self.failure: str | None = None
        self.root: State = (0, problem.column_sums)
        self.feasibility = problem.feasibility()

    def _fail(self, message: str) -> None:
        self.failure = message
        raise ComputationBudgetExceeded(message)

    def total(self) -> int | Fraction:
        if self.failure is not None:
            raise ComputationBudgetExceeded(self.failure)
        if not self.feasibility.feasible:
            return 0
        try:
            return self._mass(self.root)
        except RecursionError:
            self._fail("Python row-recursion depth exceeded; transpose or use a smaller instance")
        raise AssertionError("unreachable")

    def _mass(self, state: State) -> int | Fraction:
        if state in self.masses:
            return self.masses[state]
        if self.states_visited >= self.max_states:
            self._fail(f"exact DP exceeded max_states={self.max_states}; no result is available")
        self.states_visited += 1
        i, residual = state
        m, n = self.problem.shape
        if sum(residual) != self.suffix_rows[i] or any(
            not self.suffix_lower[i][j] <= residual[j] <= self.suffix_upper[i][j]
            for j in range(n)
        ):
            self.masses[state], self.branches[state] = 0, ()
            return 0
        if i == m:
            self.masses[state], self.branches[state] = 1, ()
            return 1
        lower = tuple(max(self.problem.lower_bounds[i][j], residual[j] - self.suffix_upper[i + 1][j])
                      for j in range(n))
        upper = tuple(min(self.problem.upper_bounds[i][j], residual[j] - self.suffix_lower[i + 1][j])
                      for j in range(n))
        total: int | Fraction = 0
        branches = []
        for row in _bounded_vectors(self.problem.row_sums[i], lower, upper):
            if self.transitions_visited >= self.max_transitions:
                self._fail(f"exact DP exceeded max_transitions={self.max_transitions}; no result is available")
            self.transitions_visited += 1
            row_mass = self.weights.row_weight(i, row) if self.weights is not None else 1
            if row_mass == 0:
                continue
            child = (i + 1, tuple(residual[j] - row[j] for j in range(n)))
            mass = row_mass * self._mass(child)
            if mass:
                branches.append(_Branch(row, child, mass))
                total += mass
        self.masses[state], self.branches[state] = total, tuple(branches)
        return total

    @property
    def stats(self) -> dict[str, int | bool]:
        return {"states_visited": self.states_visited,
                "transitions_visited": self.transitions_visited,
                "complete": self.failure is None and (not self.feasibility.feasible or self.root in self.masses)}


class ExactTableSampler:
    """Count and sample uniformly using memoized integer completion counts.

    Budget limits count distinct DP states and candidate row transitions. The
    resulting transition DAG is cached. They do not bound input size, integer
    bit lengths, feasibility work, elapsed time, or the RNG's rejection loop.
    """

    def __init__(self, problem: TableProblem, *, max_states: int = 100_000,
                 max_transitions: int = 1_000_000) -> None:
        self.problem = problem
        self._engine = _CompletionEngine(problem, None, max_states, max_transitions)

    @property
    def stats(self) -> dict[str, int | bool]:
        return self._engine.stats

    def count(self) -> int:
        result = self._engine.total()
        assert isinstance(result, int)
        return result

    def unrank(self, rank: int) -> Table:
        """The table at a zero-based lexicographic rank; an exact bijection."""
        _integer(rank, "rank")
        count = self.count()
        if rank >= count:
            raise IndexError(f"rank {rank} is outside a fiber of size {count}")
        state, rows = self._engine.root, []
        while state[0] < self.problem.shape[0]:
            for branch in self._engine.branches[state]:
                if rank < branch.mass:
                    rows.append(branch.row)
                    state = branch.child
                    break
                rank -= branch.mass
            else:
                raise AssertionError("completion count and branches disagree")
        return tuple(rows)

    def rank(self, table: Sequence[Sequence[int]]) -> int:
        validated = self.problem.validate_table(table)
        self.count()  # Complete the exact DAG before exposing any result.
        state, rank = self._engine.root, 0
        for row in validated:
            for branch in self._engine.branches[state]:
                if branch.row == row:
                    state = branch.child
                    break
                rank += branch.mass
            else:
                raise AssertionError("a feasible table is missing from the exact DAG")
        assert isinstance(rank, int)
        return rank

    def sample(self, rng: RandomIntegerSource | None = None) -> Table:
        count = self.count()
        if count == 0:
            raise InfeasibleTableError(self._engine.feasibility.reason)
        return self.unrank((rng if rng is not None else random.SystemRandom()).randrange(count))

    def tables(self, *, max_tables: int = 100_000) -> Iterator[Table]:
        """Enumerate the entire fiber, refusing to start if the output cap fails."""
        _integer(max_tables, "max_tables", positive=True)
        count = self.count()
        if count > max_tables:
            raise ComputationBudgetExceeded(f"fiber has {count} tables, exceeding max_tables={max_tables}")
        return (self.unrank(rank) for rank in range(count))


def _draw_rational(masses: Sequence[Fraction], rng: RandomIntegerSource) -> int:
    denominator = 1
    for mass in masses:
        denominator = denominator * mass.denominator // gcd(denominator, mass.denominator)
    integer_masses = [mass.numerator * (denominator // mass.denominator) for mass in masses]
    rank = rng.randrange(sum(integer_masses))
    for i, mass in enumerate(integer_masses):
        if rank < mass:
            return i
        rank -= mass
    raise AssertionError("RNG returned an integer outside the requested range")


class ExactWeightedTableSampler:
    """Exact product-weight sampling; deliberately distinct from table-uniform."""

    def __init__(self, problem: TableProblem, weights: ProductWeights, *,
                 max_states: int = 100_000, max_transitions: int = 1_000_000) -> None:
        self.problem, self.weights = problem, weights
        self._engine = _CompletionEngine(problem, weights, max_states, max_transitions)

    @property
    def stats(self) -> dict[str, int | bool]:
        return self._engine.stats

    def normalizer(self) -> Fraction:
        """Sum unnormalized weights exactly (zero for an empty/zero-mass fiber)."""
        return Fraction(self._engine.total())

    def _positive_normalizer(self) -> Fraction:
        normalizer = self.normalizer()
        if not normalizer:
            if not self._engine.feasibility.feasible:
                raise InfeasibleTableError(self._engine.feasibility.reason)
            raise ZeroMassError("all feasible tables have zero target weight")
        return normalizer

    def probability(self, table: Sequence[Sequence[int]]) -> Fraction:
        validated = self.problem.validate_table(table)
        return self.weights.table_weight(validated) / self._positive_normalizer()

    def sample(self, rng: RandomIntegerSource | None = None) -> Table:
        self._positive_normalizer()
        source = rng if rng is not None else random.SystemRandom()
        state, rows = self._engine.root, []
        while state[0] < self.problem.shape[0]:
            branches = self._engine.branches[state]
            index = _draw_rational([Fraction(branch.mass) for branch in branches], source)
            branch = branches[index]
            rows.append(branch.row)
            state = branch.child
        return tuple(rows)
