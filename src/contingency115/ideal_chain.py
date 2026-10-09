"""Bounded exponential oracle for the pinned #115 finite ideal physical chain.

This implements exact finite laws, not finite-bit programs, the theorem's
mixing schedule, or a general polynomial-time sampler. Censoring is algebraic;
drawing its matrix bypasses the actual physical excursions.
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from fractions import Fraction
import random

from .kernels import ExactKernel
from .tables import (ComputationBudgetExceeded, ExactTableSampler,
                     InfeasibleTableError, RandomIntegerSource, Table,
                     TableProblem, _integer)

UPSTREAM_REVISION = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


@dataclass(frozen=True)
class IdealChainBudget:
    max_cells: int = 16
    max_input_bits: int = 4096
    max_profile_candidates: int = 100_000
    max_physical_states: int = 512
    max_completions: int = 100_000
    max_dp_states: int = 100_000
    max_dp_transitions: int = 1_000_000
    max_transition_work: int = 2_000_000
    max_solve_size: int = 128
    max_solve_work: int = 2_000_000
    max_rational_bits: int = 8192

    def __post_init__(self):
        for field in fields(self):
            _integer(getattr(self, field.name), field.name, positive=True)


class _Work:
    def __init__(self, budget):
        self.budget, self.counts = budget, {}

    def add(self, key, amount=1):
        count = self.counts.get(key, 0) + amount
        self.counts[key] = count
        if count > getattr(self.budget, "max_" + key):
            raise ComputationBudgetExceeded(f"ideal chain exceeded max_{key}")

    def rational(self, value):
        if max(value.numerator.bit_length(), value.denominator.bit_length()) > self.budget.max_rational_bits:
            raise ComputationBudgetExceeded("ideal chain exceeded max_rational_bits")
        return value


@dataclass(frozen=True, order=True)
class PhysicalState:
    row_view: tuple[int, ...]
    column_view: tuple[int, ...]

    @property
    def balanced(self):
        return self.row_view == self.column_view

    def defect_labels(self):
        delta = tuple(q - x for x, q in zip(self.row_view, self.column_view))
        if delta.count(1) == delta.count(-1) == 1 and all(d in (-1, 0, 1) for d in delta):
            return delta.index(1), delta.index(-1)  # source negative s, positive t
        return None


@dataclass(frozen=True)
class CensoredTableKernel:
    kernel: ExactKernel
    stationary_success_probability: Fraction
    expected_physical_steps_per_return: Fraction
    per_start_expected_physical_steps: tuple[Fraction, ...]
    construction: str = "exact algebraic censoring; direct draws bypass physical excursions"


@dataclass(frozen=True)
class PhysicalReturn:
    state_index: int
    table: Table
    physical_steps: int


@dataclass(frozen=True)
class IdealPhysicalChain:
    problem: TableProblem
    d: int
    U: int
    L: int
    beta: Fraction
    small_cells: tuple[tuple[int, int], ...]
    large_rows: tuple[int, ...]
    large_columns: tuple[int, ...]
    states: tuple[PhysicalState, ...]
    residual_margins: tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]
    completions: tuple[tuple[Table, ...], ...]
    neighbors: tuple[tuple[int, ...], ...]
    acceptance_counts: tuple[tuple[int, ...], ...]
    matrix: tuple[tuple[Fraction, ...], ...]
    stationary: tuple[Fraction, ...]
    work_counts: tuple[tuple[str, int], ...]
    budget: IdealChainBudget
    parameter_regime: str
    upstream_revision: str = UPSTREAM_REVISION

    @property
    def all_small(self):
        return not self.large_rows or not self.large_columns

    @property
    def completion_counts(self):
        return tuple(map(len, self.completions))

    @property
    def reference_cell(self):
        return None if self.all_small else (self.large_rows[0], self.large_columns[0])

    @property
    def large_capacity(self):
        """Source capacity; dominates all residual entries, so no extra cap."""
        return sum(self.problem.row_sums) + self.d * self.L + self.U + 2

    def doubled_profile(self, index):
        state = self.states[index]
        return state.row_view + tuple(self.U - q for q in state.column_view)

    def translation(self, source, target):
        """Literal star translation on the ordered large rectangle (reference 0,0)."""
        if self.all_small:
            return ()
        r0, c0 = self.residual_margins[source]
        r1, c1 = self.residual_margins[target]
        dr = tuple(y - x for x, y in zip(r0, r1))
        dc = tuple(y - x for x, y in zip(c0, c1))
        return tuple(tuple(dr[0] - sum(dc[1:]) if i == j == 0 else
                           dc[j] if i == 0 else dr[i] if j == 0 else 0
                           for j in range(len(dc))) for i in range(len(dr)))

    def completion_passes(self, source, target, completion):
        delta = self.translation(source, target)
        return all(value + delta[i][j] >= 0 for i, row in enumerate(completion)
                   for j, value in enumerate(row))

    def step(self, state_index: int, rng: RandomIntegerSource | None = None):
        """One literal proposal/hold, then fresh uniform completion acceptance."""
        _integer(state_index, "state_index")
        if state_index >= len(self.states):
            raise IndexError("state index outside the physical chain")
        source = rng if rng is not None else random.SystemRandom()
        slot = source.randrange(self.beta.denominator)
        if slot >= len(self.neighbors[state_index]):
            return state_index
        target = self.neighbors[state_index][slot]
        fibre = self.completions[state_index]
        completion = fibre[source.randrange(len(fibre))]
        return target if self.completion_passes(state_index, target, completion) else state_index

    def _output_pair(self, state_index, completion):
        state = self.states[state_index]
        if not state.balanced or any(value < self.L for row in completion for value in row):
            return None
        m, n = self.problem.shape
        table = [[0] * n for _ in range(m)]
        for (i, j), value in zip(self.small_cells, state.row_view):
            table[i][j] = value
        for a, i in enumerate(self.large_rows):
            for b, j in enumerate(self.large_columns):
                table[i][j] = completion[a][b] - self.L
        return self.problem.validate_table(table)

    def output(self, state_index, rng: RandomIntegerSource | None = None):
        """Fresh conditional completion and source success/unpadding map."""
        _integer(state_index, "state_index")
        if state_index >= len(self.states):
            raise IndexError("state index outside the physical chain")
        source = rng if rng is not None else random.SystemRandom()
        fibre = self.completions[state_index]
        return self._output_pair(state_index, fibre[source.randrange(len(fibre))])

    def stationary_output_law(self):
        """Unconditional successful-table masses and failure mass at stationarity."""
        law, failure = {}, Fraction(0)
        for index, fibre in enumerate(self.completions):
            mass = self.stationary[index] / len(fibre)
            for completion in fibre:
                table = self._output_pair(index, completion)
                if table is None:
                    failure += mass
                else:
                    law[table] = law.get(table, Fraction(0)) + mass
        return dict(sorted(law.items())), failure

    def physical_return(self, state_index, *, max_steps: int, rng=None):
        """Literal all-small excursion, counting holds; fail on the step cap."""
        if not self.all_small:
            raise ValueError("balanced table returns are only exposed for all-small chains")
        _integer(max_steps, "max_steps", positive=True)
        _integer(state_index, "state_index")
        if state_index >= len(self.states):
            raise IndexError("state index outside the physical chain")
        if not self.states[state_index].balanced:
            raise ValueError("a return must start at a balanced state")
        for steps in range(1, max_steps + 1):
            state_index = self.step(state_index, rng)
            if self.states[state_index].balanced:
                return PhysicalReturn(state_index, self._output_pair(state_index, ()), steps)
        raise ComputationBudgetExceeded("physical excursion exceeded max_steps")

    def all_small_return_kernel(self, *, budget: IdealChainBudget | None = None):
        """Exact first-return law; never runs or times a physical excursion."""
        if not self.all_small:
            raise ValueError("censoring to original tables requires all-small cells")
        work = _Work(budget if budget is not None else self.budget)
        a = [i for i, state in enumerate(self.states) if state.balanced]
        b = [i for i, state in enumerate(self.states) if not state.balanced]
        if len(b) > work.budget.max_solve_size:
            raise ComputationBudgetExceeded("censored kernel exceeded max_solve_size")
        if not a:
            raise ValueError("no balanced states")
        # Every physical vertex must reach the balanced set before rational solve.
        seen, queue = set(a), list(a)
        while queue:
            j = queue.pop()
            for i in range(len(self.states)):
                work.add("solve_work")
                if self.matrix[i][j] and i not in seen:
                    seen.add(i)
                    queue.append(i)
        if len(seen) != len(self.states):
            raise ValueError("a physical class cannot reach balanced states")
        work.add("solve_work", len(b) * (len(b) + len(a) + 1))
        augmented = [[Fraction(i == j) - self.matrix[i][j] for j in b] +
                     [self.matrix[i][j] for j in a] + [Fraction(1)] for i in b]
        # Solve (I-P_BB) H = [P_BA, 1], with bounded exact Gaussian elimination.
        for pivot in range(len(b)):
            row = next((r for r in range(pivot, len(b)) if augmented[r][pivot]), None)
            if row is None:
                raise ValueError("singular first-hit system")
            augmented[pivot], augmented[row] = augmented[row], augmented[pivot]
            divisor = augmented[pivot][pivot]
            for j in range(pivot, len(b) + len(a) + 1):
                work.add("solve_work")
                augmented[pivot][j] = work.rational(augmented[pivot][j] / divisor)
            for i in range(len(b)):
                if i == pivot:
                    continue
                multiplier = augmented[i][pivot]
                if not multiplier:
                    continue
                for j in range(pivot, len(b) + len(a) + 1):
                    work.add("solve_work", 2)
                    augmented[i][j] = work.rational(augmented[i][j] - multiplier * augmented[pivot][j])
        matrix, times = [], []
        for i in a:
            row = []
            for target, j in enumerate(a):
                value = self.matrix[i][j]
                for k, index in enumerate(b):
                    work.add("solve_work", 2)
                    value = work.rational(value + self.matrix[i][index] * augmented[k][len(b) + target])
                row.append(value)
            matrix.append(tuple(row))
            time = Fraction(1)
            for k, index in enumerate(b):
                work.add("solve_work", 2)
                time = work.rational(time + self.matrix[i][index] * augmented[k][-1])
            times.append(time)
        success = sum(self.stationary[i] for i in a)
        kernel = ExactKernel(tuple(self._output_pair(i, ()) for i in a), tuple(matrix),
                             tuple(self.stationary[i] / success for i in a))
        if not kernel.is_stochastic() or not kernel.satisfies_detailed_balance():
            raise ArithmeticError("censored law failed exact invariants")
        if sum(p * t for p, t in zip(kernel.stationary, times)) != 1 / success:
            raise ArithmeticError("stationary return-time identity failed")
        return CensoredTableKernel(kernel, success, 1 / success, tuple(times))


def build_ideal_chain(problem: TableProblem, *, budget: IdealChainBudget | None = None):
    """Build the literal U=d^20,L=d^12 ideal law, subject to hard budgets."""
    d = 10 + (problem.shape[0] + 1) * (problem.shape[1] + 1)
    return _build(problem, d**20, d**12, budget or IdealChainBudget(), "literal paper parameters")


def build_rescaled_ideal_chain(problem: TableProblem, *, U: int, L: int,
                              budget: IdealChainBudget | None = None):
    """Explicitly rescaled diagnostic; carries no source quantitative guarantees."""
    _integer(U, "U", positive=True)
    _integer(L, "L", positive=True)
    if U < 2:
        raise ValueError("rescaled U must be at least two")
    return _build(problem, U, L, budget or IdealChainBudget(),
                  "rescaled diagnostic; no paper quantitative guarantees")


def _build(problem, U, L, budget, regime):
    work = _Work(budget)
    m, n = problem.shape
    if m * n > budget.max_cells:
        raise ComputationBudgetExceeded("ideal chain exceeded max_cells")
    if sum(x.bit_length() for x in problem.row_sums + problem.column_sums) + U.bit_length() + L.bit_length() > budget.max_input_bits:
        raise ComputationBudgetExceeded("ideal chain exceeded max_input_bits")
    if any(problem.lower_bounds[i][j] or problem.upper_bounds[i][j] != min(problem.row_sums[i], problem.column_sums[j])
           for i in range(m) for j in range(n)):
        raise ValueError("ideal chain requires ordinary unrestricted margins")
    if sum(problem.row_sums) != sum(problem.column_sums):
        raise InfeasibleTableError("row and column totals differ")
    d = 10 + (m + 1) * (n + 1)
    beta = Fraction(1, 1 << (32 * d * d - 1).bit_length())
    lr = tuple(i for i, r in enumerate(problem.row_sums) if r >= U)
    lc = tuple(j for j, c in enumerate(problem.column_sums) if c >= U)
    cells = tuple((i, j) for i in range(m) for j in range(n) if i not in lr or j not in lc)
    lookup_cells = {cell: k for k, cell in enumerate(cells)}
    states, residuals = [], []

    def retain(x, q):
        work.add("profile_candidates")
        if any(value < 0 or value > U for value in q):
            return
        rows = [0] * m
        columns = [0] * n
        for (i, j), value, other in zip(cells, x, q):
            rows[i] += value
            columns[j] += other
        if any(a > r for a, r in zip(rows, problem.row_sums)) or any(b > c for b, c in zip(columns, problem.column_sums)):
            return
        rr = tuple(r - a + (len(lc) * L if i in lr else 0) for i, (r, a) in enumerate(zip(problem.row_sums, rows)))
        cc = tuple(c - b + (len(lr) * L if j in lc else 0) for j, (c, b) in enumerate(zip(problem.column_sums, columns)))
        if any(rr[i] for i in range(m) if i not in lr) or any(cc[j] for j in range(n) if j not in lc) or sum(rr) != sum(cc):
            return
        work.add("physical_states")
        states.append(PhysicalState(x, q))
        residuals.append((tuple(rr[i] for i in lr), tuple(cc[j] for j in lc)))

    def enumerate_x(prefix, row_used):
        work.add("profile_candidates")
        if len(prefix) == len(cells):
            x = tuple(prefix)
            retain(x, x)
            for s in range(len(cells)):
                for t in range(len(cells)):
                    if s != t and x[t]:
                        q = list(x)
                        q[s] += 1
                        q[t] -= 1
                        retain(x, tuple(q))
            return
        i, j = cells[len(prefix)]
        bound = min(U, problem.row_sums[i] - row_used[i], problem.column_sums[j] + 1)
        for value in range(bound + 1):
            row_used[i] += value
            enumerate_x(prefix + [value], row_used)
            row_used[i] -= value

    enumerate_x([], [0] * m)
    ordered = sorted(zip(states, residuals))
    states = tuple(state for state, _ in ordered)
    residuals = tuple(residual for _, residual in ordered)
    if not states:
        raise InfeasibleTableError("no feasible physical states")
    work.add("transition_work", len(states)**2)  # dense exact matrix allocation
    completions, cache = [], {}
    for rr, cc in residuals:
        key = rr, cc
        if key not in cache:
            if not lr or not lc:
                fibre = ((),)
            elif len(lr) == 1:
                fibre = ((tuple(cc),),)
            elif len(lc) == 1:
                fibre = (tuple((value,) for value in rr),)
            else:
                if (work.counts.get("dp_states", 0) >= budget.max_dp_states or
                        work.counts.get("dp_transitions", 0) >= budget.max_dp_transitions):
                    raise ComputationBudgetExceeded("ideal chain exhausted aggregate DP budget")
                sampler = ExactTableSampler(TableProblem(rr, cc),
                    max_states=budget.max_dp_states - work.counts.get("dp_states", 0),
                    max_transitions=budget.max_dp_transitions - work.counts.get("dp_transitions", 0))
                count = sampler.count()
                work.add("dp_states", sampler.stats["states_visited"])
                work.add("dp_transitions", sampler.stats["transitions_visited"])
                if count > budget.max_completions - work.counts.get("completions", 0):
                    raise ComputationBudgetExceeded("ideal chain exceeded max_completions")
                # Public unrank scans cached branches. Precharge a conservative
                # worst case for every rank, rather than only its emitted cells.
                work.add("transition_work", count * (sampler.stats["transitions_visited"] + len(rr) + len(cc)))
                fibre = tuple(sampler.tables(max_tables=budget.max_completions))
            work.add("completions", len(fibre))
            cache[key] = fibre
        completions.append(cache[key])
    completions = tuple(completions)
    if any(not fibre for fibre in completions):
        raise ArithmeticError("arithmetic feasibility produced an empty completion fibre")
    indices = {state: i for i, state in enumerate(states)}
    adjacent = [set() for _ in states]
    for index, state in enumerate(states):
        profile = state.row_view + tuple(U - q for q in state.column_view)
        for receiver in range(len(profile)):
            for donor in range(len(profile)):
                work.add("transition_work")
                if receiver == donor or not profile[donor] or profile[receiver] == U:
                    continue
                candidate = list(profile)
                candidate[receiver] += 1
                candidate[donor] -= 1
                k = len(cells)
                target = indices.get(PhysicalState(tuple(candidate[:k]), tuple(U - v for v in candidate[k:])))
                if target is not None:
                    adjacent[index].add(target)
        labels = state.defect_labels()
        if labels is not None:
            s, t = labels
            repaired = list(state.row_view)
            repaired[t] -= 1
            crossing = cells[t][0], cells[s][1]
            if crossing in lookup_cells:
                repaired[lookup_cells[crossing]] += 1
            target = indices.get(PhysicalState(tuple(repaired), tuple(repaired)))
            if target is None:
                raise ArithmeticError("designated repair missing from feasible physical states")
            adjacent[index].add(target)
            adjacent[target].add(index)
    neighbors = tuple(tuple(sorted(row)) for row in adjacent)
    if any(i in row or len(row) > 5 * d*d + 1 or len(row) * beta > Fraction(1, 2)
           for i, row in enumerate(neighbors)):
        raise ArithmeticError("graph violates source degree/hold allowance")
    if any(i not in neighbors[j] for i, row in enumerate(neighbors) for j in row):
        raise ArithmeticError("physical graph is not symmetric")
    weights = tuple(map(len, completions))
    total = sum(weights)
    stationary = tuple(work.rational(Fraction(weight, total)) for weight in weights)
    size = len(states)
    matrix = [[Fraction(0)] * size for _ in states]
    accepted = [[0] * size for _ in states]
    chain = IdealPhysicalChain(problem, d, U, L, beta, cells, lr, lc, states, residuals,
                             completions, neighbors, (), (), stationary, (), budget, regime)
    for i, row in enumerate(neighbors):
        for j in row:
            for completion in completions[i]:
                work.add("transition_work", max(1, len(lr) * len(lc)))
                accepted[i][j] += chain.completion_passes(i, j, completion)
            matrix[i][j] = work.rational(beta * accepted[i][j] / weights[i])
        matrix[i][i] = work.rational(1 - sum(matrix[i]))
    if any(accepted[i][j] != accepted[j][i] for i in range(size) for j in range(size)):
        raise ArithmeticError("forward and reverse completion counts differ")
    return IdealPhysicalChain(problem, d, U, L, beta, cells, lr, lc, states, residuals,
                             completions, neighbors, tuple(map(tuple, accepted)), tuple(map(tuple, matrix)),
                             stationary, tuple(sorted(work.counts.items())), budget, regime)
