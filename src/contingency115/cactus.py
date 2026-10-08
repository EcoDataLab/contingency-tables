"""Exact coordinate samplers when the variable-cell bipartite graph is a cactus.

Fixed cells are removed before the graph test. Edge-disjoint cycles may share
vertices. Uniform counting/ranking never iterates over an interval's width.
Product-weight line normalization is separately guarded and may iterate over
the width; it makes no general polynomial-time weighted-sampling claim.
"""

from __future__ import annotations

from bisect import bisect_right
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from math import lcm, prod
import random
from typing import Iterator, Sequence

from .tables import (ComputationBudgetExceeded, InfeasibleTableError, ProductWeights,
                     RandomIntegerSource, Table, TableProblem, ZeroMassError, _integer)


class NotCactusError(ValueError):
    """The variable-cell graph contains overlapping simple cycles."""


@dataclass(frozen=True)
class CycleCoordinate:
    cells: tuple[tuple[int, int, int], ...]
    lower: int
    upper: int

    @property
    def size(self) -> int:
        return self.upper - self.lower + 1


def _graph_cycles(problem: TableProblem, max_cycle_edges: int):
    """Fundamental cycles of a spanning forest; edge overlap rejects a cactus."""
    m, n = problem.shape
    edges = tuple((i, m + j) for i in range(m) for j in range(n)
                  if problem.upper_bounds[i][j] > problem.lower_bounds[i][j])
    adjacency = [[] for _ in range(m + n)]
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    parent, depth = [-1] * (m + n), [0] * (m + n)
    for start in range(m + n):
        if parent[start] != -1:
            continue
        parent[start] = start
        queue = deque([start])
        while queue:
            u = queue.popleft()
            for v in adjacency[u]:
                if parent[v] == -1:
                    parent[v], depth[v] = u, depth[u] + 1
                    queue.append(v)
    cycles, used = [], set()
    visited_cycle_edges = 0
    for u, v in edges:
        if parent[u] == v or parent[v] == u:
            continue
        left, right = [u], [v]
        while left[-1] != right[-1]:
            if depth[left[-1]] >= depth[right[-1]]:
                left.append(parent[left[-1]])
            else:
                right.append(parent[right[-1]])
            visited_cycle_edges += 1
            if visited_cycle_edges > max_cycle_edges:
                raise ComputationBudgetExceeded("cactus decomposition exceeded max_cycle_edges")
        vertices = left + list(reversed(right[:-1]))
        visited_cycle_edges += 1  # the non-tree closing edge
        if visited_cycle_edges > max_cycle_edges:
            raise ComputationBudgetExceeded("cactus decomposition exceeded max_cycle_edges")
        signed = []
        for index, a in enumerate(vertices):
            b = vertices[(index + 1) % len(vertices)]
            i, j = (a, b - m) if a < m else (b, a - m)
            signed.append((i, j, 1 if index % 2 == 0 else -1))
        signed.sort()
        orientation = signed[0][2]
        signed = tuple((i, j, sign * orientation) for i, j, sign in signed)
        cells = {(i, j) for i, j, _ in signed}
        if cells & used:
            raise NotCactusError("variable-cell graph has cycles sharing an edge")
        used.update(cells)
        cycles.append(signed)
    return tuple(sorted(cycles)), tuple((i, j - m) for i, j in edges)


class CactusTableSampler:
    """Uniform table sampler with Cartesian integer cycle coordinates.

    Counting and ranking use binary integer arithmetic independent of numeric
    interval widths. Feasibility uses the existing integer max-flow witness.
    Resource limits cover matrix cells and cycle-path visits, not integer bit
    lengths, max-flow work, elapsed time, memory, or RNG execution length.
    """

    def __init__(self, problem: TableProblem, *, max_cells: int = 100_000,
                 max_cycle_edges: int = 100_000) -> None:
        self.problem = problem
        _integer(max_cells, "max_cells", positive=True)
        _integer(max_cycle_edges, "max_cycle_edges", positive=True)
        if prod(problem.shape) > max_cells:
            raise ComputationBudgetExceeded("cactus sampler exceeded max_cells")
        self.feasibility = problem.feasibility()
        self.base = self.feasibility.table
        self.cycles: tuple[CycleCoordinate, ...] = ()
        self.variable_edges: tuple[tuple[int, int], ...] = ()
        self.cycle_cells: frozenset[tuple[int, int]] = frozenset()
        if self.base is None:
            self._count = 0
            return
        raw_cycles, self.variable_edges = _graph_cycles(problem, max_cycle_edges)
        coordinates = []
        for cells in raw_cycles:
            lower, upper = [], []
            for i, j, sign in cells:
                lo, hi, value = problem.lower_bounds[i][j], problem.upper_bounds[i][j], self.base[i][j]
                lower.append(lo - value if sign == 1 else value - hi)
                upper.append(hi - value if sign == 1 else value - lo)
            coordinate = CycleCoordinate(cells, max(lower), min(upper))
            assert coordinate.lower <= 0 <= coordinate.upper
            coordinates.append(coordinate)
        self.cycles = tuple(coordinates)
        self.cycle_cells = frozenset((i, j) for coordinate in self.cycles for i, j, _ in coordinate.cells)
        self._count = prod(coordinate.size for coordinate in self.cycles)

    @property
    def stats(self) -> dict[str, int | bool]:
        return {"feasible": self.base is not None, "support_checked": self.base is not None,
                "variable_edges": len(self.variable_edges), "cycle_count": len(self.cycles),
                "bridge_edges": len(self.variable_edges) - len(self.cycle_cells),
                "count_bit_length": self._count.bit_length()}

    def count(self) -> int:
        return self._count

    def from_coordinates(self, parameters: Sequence[int]) -> Table:
        if self.base is None:
            raise InfeasibleTableError(self.feasibility.reason)
        if len(parameters) != len(self.cycles):
            raise ValueError("one integer parameter is required per cycle")
        result = [list(row) for row in self.base]
        for coordinate, value in zip(self.cycles, parameters):
            if isinstance(value, bool) or not isinstance(value, int):
                raise TypeError("cycle parameters must be integers")
            if not coordinate.lower <= value <= coordinate.upper:
                raise ValueError("cycle parameter is outside its feasible interval")
            for i, j, sign in coordinate.cells:
                result[i][j] += sign * value
        return tuple(tuple(row) for row in result)

    def coordinates(self, table: Sequence[Sequence[int]]) -> tuple[int, ...]:
        validated = self.problem.validate_table(table)
        if self.base is None:
            raise InfeasibleTableError(self.feasibility.reason)
        result = tuple((validated[c.cells[0][0]][c.cells[0][1]]
                        - self.base[c.cells[0][0]][c.cells[0][1]]) * c.cells[0][2] for c in self.cycles)
        if self.from_coordinates(result) != validated:
            raise AssertionError("feasible circulation was missing from the cactus basis")
        return result

    def rank(self, table: Sequence[Sequence[int]]) -> int:
        rank = 0
        for coordinate, value in zip(self.cycles, self.coordinates(table)):
            rank = rank * coordinate.size + value - coordinate.lower
        return rank

    def unrank(self, rank: int) -> Table:
        _integer(rank, "rank")
        if rank >= self._count:
            raise IndexError(f"rank {rank} is outside a fiber of size {self._count}")
        parameters = [0] * len(self.cycles)
        for index in range(len(self.cycles) - 1, -1, -1):
            rank, digit = divmod(rank, self.cycles[index].size)
            parameters[index] = self.cycles[index].lower + digit
        return self.from_coordinates(parameters)

    def sample(self, rng: RandomIntegerSource | None = None) -> Table:
        if not self._count:
            raise InfeasibleTableError(self.feasibility.reason)
        if self._count == 1:
            return self.unrank(0)
        return self.unrank((rng if rng is not None else random.SystemRandom()).randrange(self._count))

    def tables(self, *, max_tables: int = 100_000) -> Iterator[Table]:
        _integer(max_tables, "max_tables", positive=True)
        if self._count > max_tables:
            raise ComputationBudgetExceeded("cactus enumeration exceeded max_tables")
        return (self.unrank(rank) for rank in range(self._count))


@dataclass(frozen=True)
class CactusWeightPlan:
    line_states: int
    cell_weight_evaluations: int
    largest_cell_value: int
    stored_coefficient_bits_bound: int


@dataclass(frozen=True)
class _WeightedLine:
    lower: int
    upper: int
    masses: tuple[Fraction, ...]
    total: Fraction
    cumulative: tuple[int, ...]


def _power_exponents(weights: ProductWeights, i: int, j: int, maximum: int) -> tuple[int, int]:
    """Raw cell numerator <= 2**a and denominator <= 2**b."""
    activity = weights.activities[i][j]
    numerator = maximum * max(0, (activity.numerator - 1).bit_length())
    denominator = maximum * (activity.denominator - 1).bit_length()
    if weights.factorial_weight and maximum > 1:
        denominator += maximum * (maximum - 1).bit_length()  # maximum! <= maximum**maximum
    return numerator, denominator


class CactusWeightedSampler:
    """Exact product-weight law from independent, fully normalized cycle lines.

    The constructor completes a conservative plan and all rational arithmetic
    before sampling can touch an RNG. Line normalization may scale with numeric
    widths and cell magnitudes. Zero activities restrict the positive support
    before planning; fixed positive counts at zero activity give zero mass.
    """

    def __init__(self, problem: TableProblem, weights: ProductWeights, *,
                 max_line_states: int = 100_000, max_cell_value: int = 10_000,
                 max_weight_evaluations: int = 1_000_000, max_stored_weight_bits: int = 16_000_000,
                 max_cells: int = 100_000, max_cycle_edges: int = 100_000) -> None:
        if weights.shape != problem.shape:
            raise ValueError("activities and problem must have the same shape")
        limits = (max_line_states, max_cell_value, max_weight_evaluations, max_stored_weight_bits)
        for name, value in zip(("max_line_states", "max_cell_value", "max_weight_evaluations", "max_stored_weight_bits"), limits):
            _integer(value, name, positive=True)
        self.problem, self.weights = problem, weights
        self.geometry = CactusTableSampler(problem, max_cells=max_cells, max_cycle_edges=max_cycle_edges)
        self.plan = CactusWeightPlan(0, 0, 0, 0)
        self.lines: tuple[_WeightedLine, ...] = ()
        self._normalizer = Fraction(0)
        self._support_count = 0
        if self.geometry.base is None:
            return
        base = self.geometry.base
        m, n = problem.shape
        fixed = [(i, j) for i in range(m) for j in range(n) if (i, j) not in self.geometry.cycle_cells]
        if any(weights.activities[i][j] == 0 and base[i][j] > 0 for i, j in fixed):
            return
        intervals = []
        for coordinate in self.geometry.cycles:
            lo, hi = coordinate.lower, coordinate.upper
            for i, j, sign in coordinate.cells:
                if not weights.activities[i][j]:
                    required = -sign * base[i][j]
                    lo, hi = max(lo, required), min(hi, required)
            if lo > hi:
                return
            intervals.append((lo, hi))
        line_states = sum(hi - lo + 1 for lo, hi in intervals)
        evaluations = len(fixed) + sum((hi - lo + 1) * len(c.cells)
                                      for c, (lo, hi) in zip(self.geometry.cycles, intervals))
        if line_states > max_line_states or evaluations > max_weight_evaluations:
            raise ComputationBudgetExceeded("cactus weight plan exceeds line-state or cell-evaluation budget")
        largest = max((base[i][j] for i, j in fixed), default=0)
        fixed_num = fixed_den = 0
        for i, j in fixed:
            a, b = _power_exponents(weights, i, j, base[i][j])
            fixed_num += a
            fixed_den += b
        normalizer_num, normalizer_den = fixed_num, fixed_den
        storage = 0
        for coordinate, (lo, hi) in zip(self.geometry.cycles, intervals):
            width = hi - lo + 1
            raw_num = raw_den = 0
            for i, j, sign in coordinate.cells:
                maximum = max(base[i][j] + sign * lo, base[i][j] + sign * hi)
                largest = max(largest, maximum)
                a, b = _power_exponents(weights, i, j, maximum)
                raw_num += a
                raw_den += b
            integer_mass_exp = (width - 1).bit_length() + raw_num + width * raw_den
            storage += width * (3 + raw_num + raw_den + integer_mass_exp)
            storage += 2 + integer_mass_exp + width * raw_den  # cached line normalizer
            normalizer_num += integer_mass_exp
            normalizer_den += width * raw_den
        storage += 2 + normalizer_num + normalizer_den
        self.plan = CactusWeightPlan(line_states, evaluations, largest, storage)
        if largest > max_cell_value or storage > max_stored_weight_bits:
            raise ComputationBudgetExceeded("cactus weight plan exceeds cell-magnitude or coefficient-bit budget")
        fixed_mass = prod((weights.cell_weight(i, j, base[i][j]) for i, j in fixed), start=Fraction(1))
        normalizer, lines = fixed_mass, []
        for coordinate, (lo, hi) in zip(self.geometry.cycles, intervals):
            masses = tuple(prod((weights.cell_weight(i, j, base[i][j] + sign * t)
                                 for i, j, sign in coordinate.cells), start=Fraction(1)) for t in range(lo, hi + 1))
            denominator = lcm(*(mass.denominator for mass in masses))
            running, cumulative = 0, []
            for mass in masses:
                running += mass.numerator * (denominator // mass.denominator)
                cumulative.append(running)
            total = sum(masses, Fraction(0))
            assert total > 0
            lines.append(_WeightedLine(lo, hi, masses, total, tuple(cumulative)))
            normalizer *= total
        self.lines = tuple(lines)
        self._normalizer = normalizer
        self._support_count = prod(hi - lo + 1 for lo, hi in intervals)

    def normalizer(self) -> Fraction:
        return self._normalizer

    def support_count(self) -> int:
        return self._support_count

    def _positive(self) -> None:
        if not self._normalizer:
            if self.geometry.base is None:
                raise InfeasibleTableError(self.geometry.feasibility.reason)
            raise ZeroMassError("all feasible tables have zero target weight")

    def probability(self, table: Sequence[Sequence[int]]) -> Fraction:
        parameters = self.geometry.coordinates(table)
        self._positive()
        result = Fraction(1)
        for value, line in zip(parameters, self.lines):
            if not line.lower <= value <= line.upper:
                return Fraction(0)
            result *= line.masses[value - line.lower] / line.total
        return result

    def sample(self, rng: RandomIntegerSource | None = None) -> Table:
        self._positive()
        source = rng if rng is not None else random.SystemRandom()
        parameters = []
        for line in self.lines:
            index = (0 if line.lower == line.upper else
                     bisect_right(line.cumulative, source.randrange(line.cumulative[-1])))
            parameters.append(line.lower + index)
        return self.geometry.from_coordinates(parameters)
