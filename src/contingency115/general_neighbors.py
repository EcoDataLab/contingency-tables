"""Exact aggregate catalog of valid balanced-to-defect neighbors.

Only ordinary margins, a balanced small profile, and local slacks are used.
No physical-state or completion enumeration occurs in this module. Sampling
uses the existing exact randrange reference contract; finite-bit realization
and accepted completion/trace transitions are separate obligations.
"""

import random

from contingency115.ideal_chain import PhysicalState
from contingency115.tables import ComputationBudgetExceeded, RandomIntegerSource, TableProblem, _integer


def _weighted_pick(items, rank):
    for item, weight in items:
        if rank < weight:
            return item, rank
        rank -= weight
    raise ArithmeticError("aggregate rank outside its weighted family")


def _prefix(items):
    result, total = {}, 0
    for item, weight in items:
        result[item] = total
        total += weight
    return result, total


class BalancedNeighborCatalog:
    """Five disjoint families, O(p) geometry metadata and rank operations.

    Raw margin validation takes O(m+n); owned copies of raw input margins use
    O(m+n) space. Geometry construction is O(m+n+p), not O(p**2). Immutable
    tuple margins are reused. Each from_problem construction additionally checks
    O(m*n) effective bounds; there is no global validation cache. Neither setup
    nor rank/unrank invokes a completion oracle.
    """

    def __init__(self, row_sums, column_sums, state: PhysicalState, *, U: int,
                 L: int = 1, large_capacity: int | None = None,
                 max_small_cells: int = 100_000):
        _integer(U, "U", positive=True)
        _integer(L, "L", positive=True)
        _integer(max_small_cells, "max_small_cells", positive=True)
        if U < 2:
            raise ValueError("requires U >= 2")
        rows, columns = tuple(row_sums), tuple(column_sums)
        for margins in (rows, columns):
            for value in margins:
                _integer(value, "margin")
        m, n = len(rows), len(columns)
        if m < 2 or n < 2:
            raise ValueError("requires at least two rows and two columns")
        if sum(rows) != sum(columns):
            raise ValueError("requires equal margin totals")
        self.rows, self.columns, self.U, self.L = rows, columns, U, L
        self.small_rows = tuple(i for i, value in enumerate(rows) if value < U)
        self.small_columns = tuple(j for j, value in enumerate(columns) if value < U)
        self.a, self.b = len(self.small_rows), len(self.small_columns)
        self.p = self.a * n + self.b * (m - self.a)
        if self.p > max_small_cells:
            raise ComputationBudgetExceeded("neighbor catalog exceeded max_small_cells")
        small_rows, small_columns = set(self.small_rows), set(self.small_columns)
        self.cells = tuple((i, j) for i in range(m)
                           for j in (range(n) if i in small_rows else self.small_columns))
        self.locations = {cell: index for index, cell in enumerate(self.cells)}
        # PhysicalState's annotations do not enforce immutable integer views.
        # Validate both before equality (True==1 and 1.0==1 in Python), then own
        # an immutable snapshot so caller mutation cannot invalidate metadata.
        row_view = tuple(_integer(value, "balanced row-view entry") for value in state.row_view)
        column_view = tuple(_integer(value, "balanced column-view entry") for value in state.column_view)
        state = PhysicalState(row_view, column_view)
        if not state.balanced or len(row_view) != self.p:
            raise ValueError("requires a balanced profile on the source small-cell mask")
        self.state, self.values = state, state.row_view
        row_cells, column_cells = {}, {}
        row_used, column_used = {}, {}
        self.row_pos, self.column_pos = {}, {}
        for index, ((i, j), value) in enumerate(zip(self.cells, self.values)):
            _integer(value, "balanced small entry")
            if value >= U:
                raise ValueError("balanced small entry must be strictly below U")
            rr, cc = row_cells.setdefault(i, []), column_cells.setdefault(j, [])
            self.row_pos[index], self.column_pos[index] = len(rr), len(cc)
            rr.append(index); cc.append(index)
            row_used[i] = row_used.get(i, 0) + value
            column_used[j] = column_used.get(j, 0) + value
        if any(row_used.get(i, 0) != rows[i] for i in self.small_rows) or any(
                column_used.get(j, 0) != columns[j] for j in self.small_columns):
            raise ValueError("profile violates a fixed small-line margin")
        if any(value > rows[i] for i, value in row_used.items()) or any(
                value > columns[j] for j, value in column_used.items()):
            raise ValueError("profile has negative ordinary residual slack")
        self.row_cells, self.column_cells = row_cells, column_cells
        # If b=0 there are no LS entries or row transfer/large crossing choices;
        # storing a potentially huge irrelevant large-row list would waste space.
        self.active_rows = tuple(i for i in row_cells if i not in small_rows and row_used[i] < rows[i])
        self.active_columns = tuple(j for j in column_cells if j not in small_columns and column_used[j] < columns[j])
        self.active_row_pos = {i: rank for rank, i in enumerate(self.active_rows)}
        self.active_column_pos = {j: rank for rank, j in enumerate(self.active_columns)}
        self.small_row_pos = {i: rank for rank, i in enumerate(self.small_rows)}
        self.small_column_pos = {j: rank for rank, j in enumerate(self.small_columns)}
        # Neighbor family 5 can increase the profile's padded residual total by
        # one. Use the source's profile-independent full-total domination premise.
        full_padded_total_bound = sum(rows) + (m-self.a) * (n-self.b) * L
        capacity = (sum(rows) + (10+(m+1)*(n+1))*L + U + 2
                    if large_capacity is None else _integer(large_capacity, "large_capacity", positive=True))
        if capacity < full_padded_total_bound:
            raise ValueError("requires large capacity to dominate full padded residual total")
        self.large_capacity = capacity
        # All lists below contain cell indices; nothing scales with neighbor count.
        self.origins = [(v, len(row_cells[i]) * len(column_cells[j]) - 1)
                        for v, ((i, j), value) in enumerate(zip(self.cells, self.values)) if value > 0]
        self.sl_active = [v for v, (i, j) in enumerate(self.cells)
                          if i in small_rows and j in self.active_column_pos]
        self.ls_active = [v for v, (i, j) in enumerate(self.cells)
                          if i in self.active_row_pos and j in small_columns]
        self.positive_ls = [v for v, ((i, _), value) in enumerate(zip(self.cells, self.values))
                            if i not in small_rows and value > 0]
        self.positive_sl = [v for v, ((_, j), value) in enumerate(zip(self.cells, self.values))
                            if j not in small_columns and value > 0]
        self.row_donors = [(v, self.b * (len(self.active_rows) - int(self.cells[v][0] in self.active_row_pos)))
                           for v in self.positive_ls]
        self.column_donors = [(v, self.a * (len(self.active_columns) - int(self.cells[v][1] in self.active_column_pos)))
                              for v in self.positive_sl]
        self.origin_prefix, n0 = _prefix(self.origins)
        self.row_prefix, n2 = _prefix(self.row_donors)
        self.column_prefix, n3 = _prefix(self.column_donors)
        self.counts = (n0, len(self.sl_active) * len(self.ls_active), n2, n3,
                       len(self.positive_ls) * len(self.positive_sl))
        self.degree = sum(self.counts)
        self.offsets = tuple(sum(self.counts[:family]) for family in range(5))

    @classmethod
    def from_problem(cls, problem: TableProblem, state: PhysicalState, **kwargs):
        """Full ordinary-bound validation per construction; no global cache/oracle."""
        m, n = problem.shape
        if any(problem.lower_bounds[i][j] or problem.upper_bounds[i][j] !=
               min(problem.row_sums[i], problem.column_sums[j])
               for i in range(m) for j in range(n)):
            raise ValueError("requires ordinary margins without extra cell bounds")
        return cls(problem.row_sums, problem.column_sums, state, **kwargs)

    def _make(self, family, v=None, s=None, t=None):
        x, q = list(self.values), list(self.values)
        if family == 0:
            x[t] += 1; x[v] -= 1
            q[s] += 1; q[v] -= 1
        elif family == 1:
            x[t] += 1; q[s] += 1
        elif family == 2:
            x[s] -= 1; x[t] += 1
        elif family == 3:
            q[t] -= 1; q[s] += 1
        else:
            x[s] -= 1; q[t] -= 1
        return PhysicalState(tuple(x), tuple(q))

    def unrank(self, rank: int) -> PhysicalState:
        _integer(rank, "rank")
        if rank >= self.degree:
            raise IndexError("rank outside balanced neighbor catalog")
        family = next(f for f, count in enumerate(self.counts) if rank < self.offsets[f] + count)
        local = rank - self.offsets[family]
        if family == 0:
            v, pair = _weighted_pick(self.origins, local)
            i, j = self.cells[v]
            rr, cc = self.row_cells[i], self.column_cells[j]
            skip = self.column_pos[v] * len(rr) + self.row_pos[v]
            flat = pair + (pair >= skip)
            srank, trank = divmod(flat, len(rr))
            return self._make(0, v, cc[srank], rr[trank])
        if family == 1:
            srank, trank = divmod(local, len(self.ls_active))
            return self._make(1, s=self.sl_active[srank], t=self.ls_active[trank])
        if family == 2:
            donor, residual = _weighted_pick(self.row_donors, local)
            line_rank, col_rank = divmod(residual, self.b)
            exclude = self.active_row_pos.get(self.cells[donor][0])
            row = self.active_rows[line_rank + (exclude is not None and line_rank >= exclude)]
            return self._make(2, s=donor, t=self.locations[row, self.small_columns[col_rank]])
        if family == 3:
            donor, residual = _weighted_pick(self.column_donors, local)
            line_rank, row_rank = divmod(residual, self.a)
            exclude = self.active_column_pos.get(self.cells[donor][1])
            column = self.active_columns[line_rank + (exclude is not None and line_rank >= exclude)]
            return self._make(3, s=self.locations[self.small_rows[row_rank], column], t=donor)
        srank, trank = divmod(local, len(self.positive_sl))
        return self._make(4, s=self.positive_ls[srank], t=self.positive_sl[trank])

    def rank(self, target: PhysicalState) -> int:
        if len(target.row_view) != self.p or len(target.column_view) != self.p:
            raise ValueError("neighbor views have the wrong shape")
        for view in (target.row_view, target.column_view):
            for value in view:
                _integer(value, "neighbor entry")
        labels = target.defect_labels()
        if labels is None:
            raise ValueError("target must have exactly one ordered defect")
        s, t = labels
        dx = sum(target.row_view) - sum(self.values)
        dq = sum(target.column_view) - sum(self.values)
        try:
            if dx == dq == 1:
                family = 1
                local = self.sl_active.index(s) * len(self.ls_active) + self.ls_active.index(t)
                expected = self._make(1, s=s, t=t)
            elif dx == dq == -1:
                family = 4
                local = self.positive_ls.index(s) * len(self.positive_sl) + self.positive_sl.index(t)
                expected = self._make(4, s=s, t=t)
            elif target.column_view == self.values and self.cells[s][0] != self.cells[t][0]:
                family = 2
                row = self.cells[t][0]
                line_rank = self.active_row_pos[row]
                exclude = self.active_row_pos.get(self.cells[s][0])
                line_rank -= exclude is not None and line_rank > exclude
                local = self.row_prefix[s] + line_rank * self.b + self.small_column_pos[self.cells[t][1]]
                expected = self._make(2, s=s, t=t)
            elif target.row_view == self.values and self.cells[s][1] != self.cells[t][1]:
                family = 3
                column = self.cells[s][1]
                line_rank = self.active_column_pos[column]
                exclude = self.active_column_pos.get(self.cells[t][1])
                line_rank -= exclude is not None and line_rank > exclude
                local = self.column_prefix[t] + line_rank * self.a + self.small_row_pos[self.cells[s][0]]
                expected = self._make(3, s=s, t=t)
            else:
                family = 0
                v = self.locations[self.cells[t][0], self.cells[s][1]]
                rr = self.row_cells[self.cells[v][0]]
                flat = self.column_pos[s] * len(rr) + self.row_pos[t]
                skip = self.column_pos[v] * len(rr) + self.row_pos[v]
                local = self.origin_prefix[v] + flat - (flat > skip)
                expected = self._make(0, v, s, t)
        except (KeyError, ValueError) as error:
            raise ValueError("target is not a valid balanced neighbor") from error
        if target != expected or local < 0 or local >= self.counts[family]:
            raise ValueError("target is not a valid balanced neighbor")
        result = self.offsets[family] + local
        if self.unrank(result) != target:
            raise ValueError("target is not a valid balanced neighbor")
        return result

    def sample(self, rng: RandomIntegerSource | None = None) -> PhysicalState:
        if self.degree == 0:
            raise ValueError("balanced profile has no defect neighbors")
        source = rng if rng is not None else random.SystemRandom()
        rank = _integer(source.randrange(self.degree), "random neighbor rank")
        return self.unrank(rank)
