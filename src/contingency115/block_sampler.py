"""Classical circulation/block factorization for exact bounded table sampling.

Fixed cells and bridges are constants. Biconnected edge blocks have invariant
incident margins, even at shared articulation vertices. Single-cycle factors
use cactus coordinates; complex factors use the existing budgeted exact DP.
No polynomial-time claim is made for general complex blocks.
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from fractions import Fraction
from math import prod
import random
from typing import Iterator, Sequence

from .cactus import CactusTableSampler, CactusWeightedSampler
from .tables import (ComputationBudgetExceeded, ExactTableSampler, ExactWeightedTableSampler,
                     InfeasibleTableError, ProductWeights, RandomIntegerSource,
                     Table, TableProblem, ZeroMassError, _integer)


@dataclass(frozen=True)
class BlockSamplerBudget:
    max_cells: int = 100_000
    max_dp_states_total: int = 100_000
    max_dp_transitions_total: int = 1_000_000
    max_dp_states_per_block: int = 100_000
    max_dp_transitions_per_block: int = 1_000_000
    max_cycle_line_states_total: int = 100_000
    max_cycle_weight_evaluations_total: int = 1_000_000
    max_cycle_stored_weight_bits_total: int = 16_000_000
    max_weight_cell_value: int = 10_000
    max_raw_cell_weight_bits: int = 1_000_000

    def __post_init__(self):
        for field in fields(self):
            _integer(getattr(self, field.name), field.name, positive=True)


@dataclass(frozen=True)
class TableBlock:
    """A non-bridge edge block and its induced local table problem."""

    cells: tuple[tuple[int, int], ...]
    rows: tuple[int, ...]
    columns: tuple[int, ...]
    problem: TableProblem
    method: str

    def project(self, table: Table) -> Table:
        members = set(self.cells)
        return tuple(tuple(table[i][j] if (i, j) in members else 0 for j in self.columns) for i in self.rows)

    def weights(self, original: ProductWeights) -> ProductWeights:
        members = set(self.cells)
        return ProductWeights([[original.activities[i][j] if (i, j) in members else 1
                                for j in self.columns] for i in self.rows], original.factorial_weight)


def _edge_blocks(problem: TableProblem) -> tuple[tuple[tuple[int, int], ...], ...]:
    """Iterative Tarjan decomposition, including a one-edge block per bridge."""
    m, n = problem.shape
    adjacency = [[] for _ in range(m + n)]
    for i in range(m):
        for j in range(n):
            if problem.upper_bounds[i][j] > problem.lower_bounds[i][j]:
                adjacency[i].append(m + j)
                adjacency[m + j].append(i)
    discovery, low, parent = [-1] * (m + n), [-1] * (m + n), [-1] * (m + n)
    timer, edges, blocks = 0, [], []
    for root in range(m + n):
        if discovery[root] != -1:
            continue
        discovery[root] = low[root] = timer
        timer += 1
        stack = [(root, iter(adjacency[root]))]
        while stack:
            vertex, neighbors = stack[-1]
            try:
                neighbor = next(neighbors)
            except StopIteration:
                stack.pop()
                p = parent[vertex]
                if p != -1:
                    low[p] = min(low[p], low[vertex])
                    if low[vertex] >= discovery[p]:
                        component = []
                        while True:
                            edge = edges.pop()
                            u, v = edge
                            component.append((u, v - m) if u < m else (v, u - m))
                            if edge == (p, vertex):
                                break
                        blocks.append(tuple(sorted(component)))
                continue
            if neighbor == parent[vertex]:
                continue
            if discovery[neighbor] == -1:
                parent[neighbor] = vertex
                edges.append((vertex, neighbor))
                discovery[neighbor] = low[neighbor] = timer
                timer += 1
                stack.append((neighbor, iter(adjacency[neighbor])))
            elif discovery[neighbor] < discovery[vertex]:
                low[vertex] = min(low[vertex], discovery[neighbor])
                edges.append((vertex, neighbor))
        assert not edges
    return tuple(sorted(blocks))


class _ProductEngine:
    def __init__(self, problem: TableProblem, weights: ProductWeights | None, budget: BlockSamplerBudget | None):
        self.problem, self.weights = problem, weights
        self.budget = budget if budget is not None else BlockSamplerBudget()
        if not isinstance(self.budget, BlockSamplerBudget):
            raise TypeError("budget must be BlockSamplerBudget")
        if prod(problem.shape) > self.budget.max_cells:
            raise ComputationBudgetExceeded("block sampler exceeded max_cells")
        if weights is not None and weights.shape != problem.shape:
            raise ValueError("activities and table problem must have the same shape")
        self.feasibility = problem.feasibility()
        self.base = self.feasibility.table
        self.blocks: tuple[TableBlock, ...] = ()
        self.fixed_cells: tuple[tuple[int, int], ...] = ()
        self.engines = ()
        self.values = ()
        self.total: int | Fraction = 0
        self.failure: str | None = None
        self.complete = False
        self.work = {"dp_states": 0, "dp_transitions": 0, "cycle_line_states": 0,
                     "cycle_weight_evaluations": 0, "cycle_stored_weight_bits": 0,
                     "prepared_factors": 0}
        if self.base is None:
            return
        blocks = []
        for cells in _edge_blocks(problem):
            if len(cells) == 1:
                continue
            rows, columns = tuple(sorted({i for i, _ in cells})), tuple(sorted({j for _, j in cells}))
            members = set(cells)
            local = TableProblem(
                [sum(self.base[i][j] for j in columns if (i, j) in members) for i in rows],
                [sum(self.base[i][j] for i in rows if (i, j) in members) for j in columns],
                [[problem.upper_bounds[i][j] if (i, j) in members else 0 for j in columns] for i in rows],
                [[problem.lower_bounds[i][j] if (i, j) in members else 0 for j in columns] for i in rows])
            method = "cycle" if len(cells) == len(rows) + len(columns) else "dp"
            blocks.append(TableBlock(cells, rows, columns, local, method))
        self.blocks = tuple(blocks)
        variable_factor_cells = {cell for block in self.blocks for cell in block.cells}
        m, n = problem.shape
        self.fixed_cells = tuple((i, j) for i in range(m) for j in range(n) if (i, j) not in variable_factor_cells)

    @property
    def stats(self):
        return {**self.work, "complete": self.complete, "failed": self.failure is not None,
                "factor_count": len(self.blocks), "cycle_factors": sum(b.method == "cycle" for b in self.blocks),
                "dp_factors": sum(b.method == "dp" for b in self.blocks),
                "fixed_cells_including_bridges": len(self.fixed_cells)}

    def _weight_preflight(self):
        assert self.weights is not None and self.base is not None
        values = [(i, j, self.base[i][j]) for i, j in self.fixed_cells]
        for block in self.blocks:
            members = set(block.cells)
            values.extend((i, j, block.problem.upper_bounds[a][b])
                          for a, i in enumerate(block.rows) for b, j in enumerate(block.columns) if (i, j) in members)
        for i, j, maximum in values:
            activity = self.weights.activities[i][j]
            bits = 2 + maximum * (max(0, (activity.numerator - 1).bit_length())
                                  + (activity.denominator - 1).bit_length())
            if self.weights.factorial_weight and maximum > 1:
                bits += maximum * (maximum - 1).bit_length()
            if maximum > self.budget.max_weight_cell_value or bits > self.budget.max_raw_cell_weight_bits:
                raise ComputationBudgetExceeded("block weight preflight exceeded cell magnitude or raw-cell coefficient bits")

    def _make_factor(self, block):
        budget = self.budget
        if block.method == "cycle":
            if self.weights is None:
                engine = CactusTableSampler(block.problem, max_cells=budget.max_cells, max_cycle_edges=budget.max_cells)
                return engine, engine.count()
            remaining = (budget.max_cycle_line_states_total - self.work["cycle_line_states"],
                         budget.max_cycle_weight_evaluations_total - self.work["cycle_weight_evaluations"],
                         budget.max_cycle_stored_weight_bits_total - self.work["cycle_stored_weight_bits"])
            if min(remaining) <= 0:
                raise ComputationBudgetExceeded("shared cycle preparation budget is exhausted")
            engine = CactusWeightedSampler(
                block.problem, block.weights(self.weights), max_line_states=remaining[0],
                max_weight_evaluations=remaining[1], max_stored_weight_bits=remaining[2],
                max_cell_value=budget.max_weight_cell_value, max_cells=budget.max_cells, max_cycle_edges=budget.max_cells)
            self.work["cycle_line_states"] += engine.plan.line_states
            self.work["cycle_weight_evaluations"] += engine.plan.cell_weight_evaluations
            self.work["cycle_stored_weight_bits"] += engine.plan.stored_coefficient_bits_bound
            return engine, engine.normalizer()
        states = min(budget.max_dp_states_per_block, budget.max_dp_states_total - self.work["dp_states"])
        transitions = min(budget.max_dp_transitions_per_block, budget.max_dp_transitions_total - self.work["dp_transitions"])
        if states <= 0 or transitions <= 0:
            raise ComputationBudgetExceeded("shared DP state or transition budget is exhausted")
        if self.weights is None:
            engine = ExactTableSampler(block.problem, max_states=states, max_transitions=transitions)
        else:
            engine = ExactWeightedTableSampler(block.problem, block.weights(self.weights), max_states=states, max_transitions=transitions)
        try:
            value = engine.count() if self.weights is None else engine.normalizer()
        finally:
            self.work["dp_states"] += engine.stats["states_visited"]
            self.work["dp_transitions"] += engine.stats["transitions_visited"]
        return engine, value

    def prepare(self):
        if self.failure is not None:
            raise ComputationBudgetExceeded(self.failure)
        if self.complete:
            return self.total
        if self.base is None:
            self.complete = True
            return 0
        try:
            total: int | Fraction = 1
            if self.weights is not None:
                if any(self.weights.activities[i][j] == 0 and self.base[i][j] > 0 for i, j in self.fixed_cells):
                    self.complete = True
                    return 0
                self._weight_preflight()
                total = prod((self.weights.cell_weight(i, j, self.base[i][j]) for i, j in self.fixed_cells), start=Fraction(1))
            engines, values = [], []
            for block in self.blocks:
                engine, value = self._make_factor(block)
                engines.append(engine)
                values.append(value)
                self.work["prepared_factors"] += 1
                total *= value
                if total == 0:  # A complete zero factor already proves a zero product.
                    break
            self.engines, self.values = tuple(engines), tuple(values)
            self.total, self.complete = total, True
            return total
        except ComputationBudgetExceeded as error:
            self.failure = str(error)
            raise

    def positive(self):
        total = self.prepare()
        if total == 0:
            if self.base is None:
                raise InfeasibleTableError(self.feasibility.reason)
            raise ZeroMassError("at least one block or fixed cell has zero target mass")
        return total

    def combine(self, local_tables):
        assert self.base is not None
        result = [list(row) for row in self.base]
        for block, table in zip(self.blocks, local_tables):
            row_indices = {i: a for a, i in enumerate(block.rows)}
            column_indices = {j: b for b, j in enumerate(block.columns)}
            for i, j in block.cells:
                result[i][j] = table[row_indices[i]][column_indices[j]]
        return tuple(tuple(row) for row in result)


class BlockTableSampler:
    """Uniform mixed-radix product of exact cycle and DP block factors."""

    def __init__(self, problem: TableProblem, *, budget: BlockSamplerBudget | None = None):
        self.problem = problem
        self._engine = _ProductEngine(problem, None, budget)

    @property
    def blocks(self):
        return self._engine.blocks

    @property
    def stats(self):
        return self._engine.stats

    def count(self) -> int:
        result = self._engine.prepare()
        assert isinstance(result, int)
        return result

    def rank(self, table: Sequence[Sequence[int]]) -> int:
        validated = self.problem.validate_table(table)
        self.count()
        rank = 0
        for block, engine, radix in zip(self.blocks, self._engine.engines, self._engine.values):
            rank = rank * radix + engine.rank(block.project(validated))
        return rank

    def unrank(self, rank: int) -> Table:
        _integer(rank, "rank")
        count = self.count()
        if rank >= count:
            raise IndexError(f"rank {rank} is outside a fiber of size {count}")
        tables = [None] * len(self.blocks)
        for index in range(len(self.blocks) - 1, -1, -1):
            rank, digit = divmod(rank, self._engine.values[index])
            tables[index] = self._engine.engines[index].unrank(digit)
        return self._engine.combine(tables)

    def sample(self, rng: RandomIntegerSource | None = None) -> Table:
        count = self.count()
        if count == 0:
            raise InfeasibleTableError(self._engine.feasibility.reason)
        if count == 1:
            return self.unrank(0)
        return self.unrank((rng if rng is not None else random.SystemRandom()).randrange(count))

    def tables(self, *, max_tables: int = 100_000) -> Iterator[Table]:
        _integer(max_tables, "max_tables", positive=True)
        count = self.count()
        if count > max_tables:
            raise ComputationBudgetExceeded("block enumeration exceeded max_tables")
        return (self.unrank(rank) for rank in range(count))


class BlockWeightedSampler:
    """Product-cell target with independently normalized edge-block factors.

    All factor normalizers finish before any sample uses an RNG. Shared budgets
    limit DP states/transitions and cycle preparation separately. Raw-cell
    preflight does not bound DP completion-mass bits or total memory; the DP's
    existing arithmetic and RNG limitations remain in force. Each randrange
    call must be uniform conditional on the preceding calls, not just have a
    uniform marginal distribution when considered alone.
    """

    def __init__(self, problem: TableProblem, weights: ProductWeights, *, budget: BlockSamplerBudget | None = None):
        self.problem, self.weights = problem, weights
        self._engine = _ProductEngine(problem, weights, budget)

    @property
    def blocks(self):
        return self._engine.blocks

    @property
    def stats(self):
        return self._engine.stats

    def normalizer(self) -> Fraction:
        return Fraction(self._engine.prepare())

    def probability(self, table: Sequence[Sequence[int]]) -> Fraction:
        validated = self.problem.validate_table(table)
        self._engine.positive()
        return prod((engine.probability(block.project(validated))
                     for block, engine in zip(self.blocks, self._engine.engines)), start=Fraction(1))

    def sample(self, rng: RandomIntegerSource | None = None) -> Table:
        self._engine.positive()
        source = rng if rng is not None else random.SystemRandom()
        return self._engine.combine([engine.sample(source) for engine in self._engine.engines])
