"""Direct bounded defect walker; finite refresh draws perturb its law.

No physical-state enumeration, exact randrange, or random-retry loop is used.
The ideal dyadic kernel is symmetric. This executed approximate kernel need
not be symmetric or preserve the uniform physical stationary law exactly.
"""

from dataclasses import dataclass, fields
from fractions import Fraction as F
import random

from contingency115.ideal_chain import PhysicalState
from contingency115.repair_accept import FairBitSource
from contingency115.tables import ComputationBudgetExceeded, Table, TableProblem, _integer, _rational


@dataclass(frozen=True)
class DefectBudget:
    max_cells: int = 4096
    max_input_bits: int = 4096
    max_attempts: int = 1_000
    max_steps: int = 1_000_000
    max_fair_bits: int = 10_000_000

    def __post_init__(self):
        for field in fields(self):
            _integer(getattr(self, field.name), field.name, positive=True)


@dataclass(frozen=True)
class DefectStep:
    state: PhysicalState
    fair_bits: int
    refresh: bool


@dataclass(frozen=True)
class DefectWalk:
    state: PhysicalState
    physical_steps: int
    fair_bits: int
    refreshes: int
    ideal_walk_tv_bound: F


@dataclass(frozen=True)
class DefectSampleError:
    stationary_exhaustion: F
    ideal_endpoint_mixing: F
    transition_rounding: F
    terminal_rounding: F

    @property
    def total_variation_bound(self) -> F:
        return min(F(1), self.stationary_exhaustion + self.ideal_endpoint_mixing +
                   self.transition_rounding + self.terminal_rounding)


@dataclass(frozen=True)
class DefectSample:
    table: Table | None
    endpoint: PhysicalState
    attempts: int
    physical_steps: int
    fair_bits: int
    refreshes: int
    rejected_attempts: int
    fallback_used: bool
    error: DefectSampleError

    @property
    def exhausted(self) -> bool:
        return self.table is None or self.fallback_used


def integer_draw_tv(stop: int, bits: int) -> F:
    """Exact TV of floor(stop*word/2**bits) against uniform range(stop)."""
    _integer(stop, "stop", positive=True)
    _integer(bits, "bits")
    width = 1 << bits
    remainder = width % stop
    return F(remainder * (stop - remainder), stop * width)


def _word(rng: FairBitSource, bits: int) -> int:
    if bits == 0:
        return 0
    value = _integer(rng.getrandbits(bits), "fair-bit word")
    if value >= 1 << bits:
        raise ValueError("fair-bit source returned a word outside its range")
    return value


class DyadicDefectChain:
    """Positive ordinary one-side-small unit branch; m,n >= 2, O(m*n) steps.

    Either every row or every column margin must be strictly below U. The other
    side may reach or exceed U. The one-defect equations then bound both views
    by U, including boundary entries exactly U. The numerical both-small gap
    improvement is a separate proof premise, not supplied by this scope check.
    Fair words must be uniform conditional on previous calls. Fresh words for
    channel, support and labels share one advancing stream. Refresh rounding
    is the sole transition-law approximation; no mixing certificate is inferred.
    """

    def __init__(self, problem: TableProblem, *, U: int, refresh_bits: int,
                 budget: DefectBudget | None = None):
        _integer(U, "U", positive=True)
        _integer(refresh_bits, "refresh_bits")
        self.problem, self.U = problem, U
        self.budget = budget if budget is not None else DefectBudget()
        self.m, self.n = problem.shape
        self.p = self.m * self.n
        if self.m < 2 or self.n < 2:
            raise ValueError("requires at least two rows and two columns")
        if any(value <= 0 for value in problem.row_sums + problem.column_sums):
            raise ValueError("requires positive margins")
        if not (all(value < U for value in problem.row_sums) or
                all(value < U for value in problem.column_sums)):
            raise ValueError("requires one entire margin side strictly below U")
        if sum(problem.row_sums) != sum(problem.column_sums):
            raise ValueError("requires equal margin totals")
        if any(problem.lower_bounds[i][j] or problem.upper_bounds[i][j] !=
               min(problem.row_sums[i], problem.column_sums[j])
               for i in range(self.m) for j in range(self.n)):
            raise ValueError("requires ordinary unrestricted margins")
        if self.p > self.budget.max_cells:
            raise ComputationBudgetExceeded("defect chain exceeded max_cells")
        if sum(v.bit_length() for v in problem.row_sums + problem.column_sums) + U.bit_length() > self.budget.max_input_bits:
            raise ComputationBudgetExceeded("defect chain exceeded max_input_bits")
        self.h = 2 * (self.m + self.n - 2) + 1
        self.channel_bits = (2 * self.h - 1).bit_length()
        self.refresh_bits = refresh_bits
        self.max_bits_per_step = self.channel_bits + 2 * refresh_bits
        if self.max_bits_per_step > self.budget.max_fair_bits:
            raise ComputationBudgetExceeded("defect chain exceeded max_fair_bits")
        self.beta = F(1, 1 << self.channel_bits)
        support_bound = min(self.p, sum(problem.row_sums))
        self.transition_tv_bound = self.beta * min(F(1), F(support_bound + self.p - 1, 4 << refresh_bits))

    def validate_state(self, state: PhysicalState) -> PhysicalState:
        if len(state.row_view) != self.p or len(state.column_view) != self.p:
            raise ValueError("defect views have the wrong shape")
        for value in state.row_view + state.column_view:
            _integer(value, "physical entry")
        if tuple(sum(state.row_view[i*self.n:(i+1)*self.n]) for i in range(self.m)) != self.problem.row_sums:
            raise ValueError("row view has the wrong row margins")
        if tuple(sum(state.column_view[i*self.n+j] for i in range(self.m)) for j in range(self.n)) != self.problem.column_sums:
            raise ValueError("column view has the wrong column margins")
        if state.defect_labels() is None:
            raise ValueError("requires an ordered single defect, not a balanced state")
        return state

    def repair(self, state: PhysicalState) -> Table:
        state = self.validate_state(state)
        s, t = state.defect_labels()
        values = list(state.row_view)
        values[t] -= 1
        values[(t // self.n) * self.n + s % self.n] += 1
        return self.problem.validate_table(tuple(tuple(values[i*self.n:(i+1)*self.n])
                                                 for i in range(self.m)))

    def defect(self, table: Table, receiver: int, label_rank: int) -> PhysicalState:
        """Inverse crossing map; rank chooses all p-1 labels without enumeration."""
        table = self.problem.validate_table(table)
        _integer(receiver, "receiver")
        _integer(label_rank, "label_rank")
        if receiver >= self.p or label_rank >= self.p - 1:
            raise ValueError("receiver or label rank outside its range")
        values = tuple(v for row in table for v in row)
        if not values[receiver]:
            raise ValueError("receiver cell must be positive")
        flat = label_rank + (label_rank >= receiver)
        s = (flat // self.n) * self.n + receiver % self.n
        t = (receiver // self.n) * self.n + flat % self.n
        x, q = list(values), list(values)
        x[t] += 1; x[receiver] -= 1
        q[s] += 1; q[receiver] -= 1
        return self.validate_state(PhysicalState(tuple(x), tuple(q)))

    def _channels(self, state: PhysicalState):
        s, t = state.defect_labels()
        # Receiver/donor in one x-row or q-column; balanced candidates are omitted.
        return ([(0, a, t) for a in range((t//self.n)*self.n, (t//self.n+1)*self.n) if a != t] +
                [(0, s, b) for b in range((s//self.n)*self.n, (s//self.n+1)*self.n) if b != s] +
                [(1, a, s) for a in range(s % self.n, self.p, self.n) if a != s] +
                [(1, t, b) for b in range(t % self.n, self.p, self.n) if b != t])

    def step(self, state: PhysicalState, rng: FairBitSource | None = None) -> DefectStep:
        state = self.validate_state(state)
        source = rng if rng is not None else random.SystemRandom()
        channel = _word(source, self.channel_bits)
        if channel >= self.h:
            return DefectStep(state, self.channel_bits, False)
        if channel == self.h - 1:
            table = self.repair(state)
            support = [i for i, value in enumerate(v for row in table for v in row) if value]
            width = 1 << self.refresh_bits
            receiver = support[len(support) * _word(source, self.refresh_bits) // width]
            label = (self.p - 1) * _word(source, self.refresh_bits) // width
            return DefectStep(self.defect(table, receiver, label), self.max_bits_per_step, True)
        view, receiver, donor = self._channels(state)[channel]
        values = list((state.row_view, state.column_view)[view])
        if values[donor] == 0:
            return DefectStep(state, self.channel_bits, False)
        values[receiver] += 1; values[donor] -= 1
        target = (PhysicalState(tuple(values), state.column_view) if view == 0
                  else PhysicalState(state.row_view, tuple(values)))
        if target.balanced:
            target = state
        return DefectStep(self.validate_state(target), self.channel_bits, False)

    def walk(self, state: PhysicalState, *, steps: int,
             rng: FairBitSource | None = None) -> DefectWalk:
        state = self.validate_state(state)
        _integer(steps, "steps")
        if steps > self.budget.max_steps:
            raise ComputationBudgetExceeded("defect walk exceeded max_steps")
        if steps * self.max_bits_per_step > self.budget.max_fair_bits:
            raise ComputationBudgetExceeded("defect walk exceeded max_fair_bits")
        source = rng if rng is not None else random.SystemRandom()
        used_bits = refreshes = 0
        for _ in range(steps):
            result = self.step(state, source)
            state = result.state
            used_bits += result.fair_bits
            refreshes += result.refresh
        return DefectWalk(state, steps, used_bits, refreshes,
                          min(F(1), steps * self.transition_tv_bound))

    def sample(self, start_table: Table, *, attempts: int, steps_per_attempt: int,
               terminal_bits: int, endpoint_mixing_delta: int | F,
               rng: FairBitSource | None = None, use_fallback: bool = True) -> DefectSample:
        """Bounded restarts and support correction, with explicit error components.

        Each attempt resets only the initial defect. One advancing fair-word
        source drives every transition and terminal. The supplied mixing bound
        concerns the IDEAL dyadic trace endpoint after steps_per_attempt steps;
        this function does not establish it. On exhaustion the fixed feasible
        start_table is returned and flagged, unless use_fallback=False requests
        explicit None. The TV allowance concerns the default fallback law, not
        conditioning the finite-bit sampler on success.
        """
        table = self.problem.validate_table(start_table)
        _integer(attempts, "attempts", positive=True)
        _integer(steps_per_attempt, "steps_per_attempt")
        _integer(terminal_bits, "terminal_bits")
        delta = _rational(endpoint_mixing_delta, "endpoint_mixing_delta")
        if delta > 1:
            raise ValueError("endpoint_mixing_delta must lie between zero and one")
        if not isinstance(use_fallback, bool):
            raise TypeError("use_fallback must be a bool")
        planned_steps = attempts * steps_per_attempt
        planned_bits = attempts * (steps_per_attempt * self.max_bits_per_step + terminal_bits)
        for count, cap, name in ((attempts, self.budget.max_attempts, "max_attempts"),
                                 (planned_steps, self.budget.max_steps, "max_steps"),
                                 (planned_bits, self.budget.max_fair_bits, "max_fair_bits")):
            if count > cap:
                raise ComputationBudgetExceeded(f"defect sampler exceeded {name}")
        support_bound = min(self.p, sum(self.problem.row_sums))
        lower = max(self.m, self.n)
        error = DefectSampleError((1 - F(lower, support_bound)) ** attempts,
                                  attempts * delta, planned_steps * self.transition_tv_bound,
                                  F(attempts, 1 << terminal_bits))
        values = tuple(value for row in table for value in row)
        receiver = next(i for i, value in enumerate(values) if value > 0)
        initial = self.defect(table, receiver, 0)
        source = rng if rng is not None else random.SystemRandom()
        used_steps = used_bits = refreshes = rejected = 0
        for attempt in range(1, attempts + 1):
            endpoint = initial
            for _ in range(steps_per_attempt):
                move = self.step(endpoint, source)
                endpoint = move.state
                used_steps += 1
                used_bits += move.fair_bits
                refreshes += move.refresh
            repaired = self.repair(endpoint)
            support = sum(value > 0 for row in repaired for value in row)
            threshold = (lower << terminal_bits) // support
            word = _word(source, terminal_bits)
            used_bits += terminal_bits
            if word < threshold:
                return DefectSample(repaired, endpoint, attempt, used_steps, used_bits,
                                    refreshes, rejected, False, error)
            rejected += 1
        return DefectSample(table if use_fallback else None, endpoint, attempts,
                            used_steps, used_bits, refreshes, rejected, use_fallback, error)
