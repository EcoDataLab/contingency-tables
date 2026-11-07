"""Bounded one-step reference for the accepted-conductance general defect trace.

Geometry is direct; no states, tables or completions are enumerated here. The
completion callback's conditional accuracy and cooperative cost bounds remain
explicit premises, not certified callback CPU-time or an outer-sampler theorem.
Finite rank words and capped star exits perturb the ideal dyadic trace kernel.
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from fractions import Fraction as F
import random
from types import MappingProxyType
from typing import Protocol

from .general_neighbors import BalancedNeighborCatalog
from .ideal_chain import PhysicalState
from .repair_accept import FairBitSource
from .tables import ComputationBudgetExceeded, InfeasibleTableError, Table, TableProblem, _integer, _rational


def defect_degree_bound(m: int, n: int, a: int, b: int) -> int:
    """Global shape/type bound for FULL defect degree, independent of state.

    a,b count small rows/columns. Only available label-type pairs are used;
    a same-type pair needs two distinct cells. Empty completion rectangles also
    admit the known unit-branch degree bound. This is geometric bound arithmetic,
    not a Poincare/mixing certificate or a state-specific degree normalization.
    """
    for name,value in (("m",m),("n",n),("a",a),("b",b)):
        _integer(value,name)
    if m < 2 or n < 2 or a > m or b > n:
        raise ValueError("requires m,n >= 2 and 0 <= a <= m, 0 <= b <= n")
    R,C = m-a,n-b
    A,B = a*C,R*b
    p = a*b+A+B
    if p < 2:
        raise ValueError("defect degree requires at least two small cells")
    counts = {"SS":a*b,"LS":B,"SL":A}
    formulas = {("SS","SS"):2*(m+n)-3,
                ("SS","LS"):n+2*m+A+B-3,
                ("SS","SL"):2*n+m+A+B-3,
                ("LS","LS"):2*(A+B+m)-3,
                ("SL","SL"):2*(A+B+n)-3,
                ("LS","SL"):2*(A+B)+m+n-4}
    available = [bound for (s,t),bound in formulas.items() if counts[s] and counts[t]
                 and (s != t or counts[s] >= 2)]
    bound = min(8*p-7,max(available))
    return min(bound,2*(m+n)-3) if R==0 or C==0 else bound


@dataclass(frozen=True)
class CompletionOracleContract:
    """Conditional TV to uniform completion, including None failure, and caps.

    After ANY past transcript, a draw at the requested margins must have TV at
    most tv_error from exact uniform feasible completion (None has ideal mass
    zero). The callback must use only context words and charge declared work
    before performing it. These are contractual premises; arbitrary callback
    CPU time and probability laws are not certified by the runtime checks.
    Every non-None result must be a feasible finite tuple/list table; malformed
    results and exceptions violate the callback contract, rather than belonging
    to the permitted None-failure mass. Host validation rejects those results.
    """
    tv_error: int | F
    max_fair_bits: int
    max_work_units: int

    def __post_init__(self):
        error = _rational(self.tv_error, "tv_error")
        if error > 1:
            raise ValueError("tv_error must lie between zero and one")
        object.__setattr__(self, "tv_error", error)
        _integer(self.max_fair_bits, "max_fair_bits")
        _integer(self.max_work_units, "max_work_units")


@dataclass(frozen=True)
class CompletionRequest:
    row_sums: tuple[int, ...]
    column_sums: tuple[int, ...]
    capacity: int

    def __post_init__(self):
        if not isinstance(self.row_sums,(tuple,list)) or not isinstance(self.column_sums,(tuple,list)):
            raise TypeError("completion margins must be tuples or lists")
        rows = tuple(_integer(value,"completion row margin") for value in self.row_sums)
        columns = tuple(_integer(value,"completion column margin") for value in self.column_sums)
        _integer(self.capacity,"completion capacity")
        if sum(rows) != sum(columns):
            raise InfeasibleTableError("completion request totals differ")
        object.__setattr__(self,"row_sums",rows)
        object.__setattr__(self,"column_sums",columns)

    @property
    def empty(self):
        return not self.row_sums or not self.column_sums


class CompletionOracle(Protocol):
    contract: CompletionOracleContract

    def draw(self, request: CompletionRequest, context: CompletionContext) -> Table | None: ...


@dataclass(frozen=True)
class GeneralDefectBudget:
    max_cells: int = 100_000
    max_input_bits: int = 100_000
    max_star_trials: int = 1_000
    max_oracle_calls: int = 1_001
    max_fair_bits: int = 10_000_000
    max_oracle_work: int = 10_000_000

    def __post_init__(self):
        for field in fields(self):
            _integer(getattr(self, field.name), field.name, positive=True)


class _Execution:
    def __init__(self, source, limit):
        self.source, self.limit = source, limit
        self.bits = self.calls = self.work = self.failures = 0

    def word(self, bits):
        _integer(bits, "word bits")
        if self.bits + bits > self.limit:
            raise ComputationBudgetExceeded("general defect step exceeded max_fair_bits")
        if not bits:
            return 0
        value = _integer(self.source.getrandbits(bits), "fair-bit word")
        if value >= 1 << bits:
            raise ValueError("fair-bit source returned a word outside its range")
        self.bits += bits
        return value


class CompletionContext:
    """Per-call cooperative word/work meter; fresh words share one step stream."""
    def __init__(self, execution: _Execution, contract: CompletionOracleContract):
        self._execution, self._contract = execution, contract
        self._fair_bits = self._work_units = 0
        self._active = True

    @property
    def fair_bits(self):
        return self._fair_bits

    @property
    def work_units(self):
        return self._work_units

    def _close(self):
        self._active = False

    def word(self, bits: int) -> int:
        if not self._active:
            raise RuntimeError("completion context is closed")
        _integer(bits, "word bits")
        if self.fair_bits + bits > self._contract.max_fair_bits:
            raise ComputationBudgetExceeded("completion oracle exceeded its fair-bit contract")
        value = self._execution.word(bits)
        self._fair_bits += bits
        return value

    def charge(self, work_units: int):
        if not self._active:
            raise RuntimeError("completion context is closed")
        _integer(work_units, "work_units")
        if self.work_units + work_units > self._contract.max_work_units:
            raise ComputationBudgetExceeded("completion oracle exceeded its work contract")
        self._work_units += work_units


@dataclass(frozen=True)
class CompletionDraw:
    completion: Table | None
    fair_bits: int
    work_units: int
    oracle_calls: int


@dataclass(frozen=True)
class GeneralStepError:
    initial_oracle: F
    star_oracle: F
    geometry_rounding: F
    star_cap: F

    @property
    def total_variation_bound(self):
        return min(F(1), self.initial_oracle + self.star_oracle + self.geometry_rounding + self.star_cap)


@dataclass(frozen=True)
class GeneralDefectStep:
    state: PhysicalState
    outcome: str
    proposal_slot: int
    star_trials: int
    fair_bits: int
    oracle_calls: int
    oracle_work: int
    oracle_failures: int
    error: GeneralStepError


class GeneralDefectChain:
    """Reusable source layout, repair, completion and bounded transition seams.

    Directed source acceptance >=1/2 is a mathematical premise under the checked
    padding/capacity hypotheses. The declared oracle law is another premise.
    One-time layout/bound validation costs O(m*n+m+n+p); preparing balanced
    catalogs per visited star costs O(m+n+p), not uniformly O(p). Per chosen
    defect slot and repair uses local O(m+n+p) work; dense validation/translation
    scans the completion rectangle. No complete machine-time claim follows.
    """
    def __init__(self, problem: TableProblem, *, U: int, L: int,
                 oracle: CompletionOracle, geometry_bits: int, star_trials: int,
                 budget: GeneralDefectBudget | None = None):
        _integer(U, "U", positive=True)
        _integer(L, "L", positive=True)
        _integer(geometry_bits, "geometry_bits")
        _integer(star_trials, "star_trials")
        if U < 2:
            raise ValueError("requires U >= 2")
        supplied_budget = budget if budget is not None else GeneralDefectBudget()
        self.budget = GeneralDefectBudget(**{field.name:getattr(supplied_budget,field.name)
                                            for field in fields(GeneralDefectBudget)})
        rows, columns = tuple(problem.row_sums), tuple(problem.column_sums)
        m, n = len(rows), len(columns)
        if m < 2 or n < 2:
            raise ValueError("requires at least two rows and two columns")
        if m*n > self.budget.max_cells:
            raise ComputationBudgetExceeded("general defect layout exceeded max_cells")
        self.problem = TableProblem(rows, columns, upper_bounds=problem.upper_bounds,
                                    lower_bounds=problem.lower_bounds)
        if sum(rows) != sum(columns):
            raise ValueError("requires equal margin totals")
        if any(self.problem.lower_bounds[i][j] or self.problem.upper_bounds[i][j] != min(rows[i], columns[j])
               for i in range(m) for j in range(n)):
            raise ValueError("requires ordinary unrestricted margins")
        if sum(value.bit_length() for value in rows+columns) + U.bit_length()+L.bit_length() > self.budget.max_input_bits:
            raise ComputationBudgetExceeded("general defect layout exceeded max_input_bits")
        self.U, self.L, self.m, self.n = U, L, m, n
        self.large_rows = tuple(i for i, r in enumerate(rows) if r >= U)
        self.large_columns = tuple(j for j, c in enumerate(columns) if c >= U)
        self.large_row_locations = MappingProxyType({i: rank for rank, i in enumerate(self.large_rows)})
        self.large_column_locations = MappingProxyType({j: rank for rank, j in enumerate(self.large_columns)})
        self.cells = tuple((i,j) for i in range(m) for j in range(n)
                           if i not in self.large_row_locations or j not in self.large_column_locations)
        self.locations = MappingProxyType({cell: rank for rank, cell in enumerate(self.cells)})
        self.p = len(self.cells)
        if self.p < 2:
            raise ValueError("defect transition requires at least two small cells")
        self.unit_branch = not self.large_rows or not self.large_columns
        e = 0 if self.unit_branch else (len(self.large_rows)-1)*(len(self.large_columns)-1)
        # Every large row receives C padding cells, and every large column R.
        # The physical source-translation theorem uses these residual floors.
        # The weighted-switch zero-cell bound separately suffices at L >= 7.
        residual_floor = min(len(self.large_rows), len(self.large_columns))*L
        if residual_floor < 3*e and L < 7:
            raise ValueError("requires min(R,C)*L >= 3e or L >= 7 for directed half acceptance")
        d = 10+(m+1)*(n+1)
        self.large_capacity = sum(rows)+d*L+U+2
        self.oracle = oracle
        contract = oracle.contract
        self.oracle_contract = CompletionOracleContract(contract.tv_error, contract.max_fair_bits, contract.max_work_units)
        self.geometry_bits, self.star_trials = geometry_bits, star_trials
        self.Q = defect_degree_bound(m,n,m-len(self.large_rows),n-len(self.large_columns))
        self.proposal_bits = (2*self.Q-1).bit_length()
        self.beta = F(1, 1 << self.proposal_bits)
        self.max_oracle_calls = 0 if self.unit_branch else 1+star_trials
        self.max_fair_bits = (self.proposal_bits + star_trials*geometry_bits +
                              self.max_oracle_calls*self.oracle_contract.max_fair_bits)
        self.max_oracle_work = self.max_oracle_calls*self.oracle_contract.max_work_units
        for count, cap, name in ((star_trials, self.budget.max_star_trials, "max_star_trials"),
                                 (self.max_oracle_calls, self.budget.max_oracle_calls, "max_oracle_calls"),
                                 (self.max_fair_bits, self.budget.max_fair_bits, "max_fair_bits"),
                                 (self.max_oracle_work, self.budget.max_oracle_work, "max_oracle_work")):
            if count > cap:
                raise ComputationBudgetExceeded(f"general defect step exceeded {name}")
        eps = F(0) if self.unit_branch else self.oracle_contract.tv_error
        geometry = (min(F(1), F(5*self.p*self.p, 4 << geometry_bits)) if star_trials else F(0))
        self.error = GeneralStepError(self.Q*self.beta*eps, 2*self.beta*star_trials*eps,
                                      2*self.beta*star_trials*geometry, 2*self.beta/F(1 << star_trials))
        self._layout_frozen = True

    def __setattr__(self, name, value):
        if getattr(self,"_layout_frozen",False):
            raise AttributeError("general defect layout and configuration are immutable")
        object.__setattr__(self,name,value)

    def validate_state(self, state: PhysicalState, *, require_defect: bool = False) -> PhysicalState:
        if not isinstance(state.row_view,(tuple,list)) or not isinstance(state.column_view,(tuple,list)):
            raise TypeError("physical views must be finite tuples or lists")
        if len(state.row_view) != self.p or len(state.column_view) != self.p:
            raise ValueError("physical views have the wrong shape")
        x = tuple(_integer(state.row_view[i], "row-view entry") for i in range(self.p))
        q = tuple(_integer(state.column_view[i], "column-view entry") for i in range(self.p))
        if any(value > self.U for value in x+q):
            raise ValueError("physical views have wrong shape or exceed U")
        result = PhysicalState(x,q)
        if result.defect_labels() is None and (require_defect or not result.balanced):
            raise ValueError("requires a balanced or single-defect physical state")
        self._residual_margins(result)
        return result

    def _residual_margins(self, state):
        row_used, column_used = [0]*self.m, [0]*self.n
        for (i,j), x, q in zip(self.cells, state.row_view, state.column_view):
            row_used[i] += x; column_used[j] += q
        rows, columns = self.problem.row_sums, self.problem.column_sums
        if any(value > rows[i] or (i not in self.large_row_locations and value != rows[i])
               for i,value in enumerate(row_used)) or any(
                value > columns[j] or (j not in self.large_column_locations and value != columns[j])
                for j,value in enumerate(column_used)):
            raise ValueError("physical state violates ordinary or fixed small margins")
        rr = tuple(rows[i]-row_used[i]+len(self.large_columns)*self.L for i in self.large_rows)
        cc = tuple(columns[j]-column_used[j]+len(self.large_rows)*self.L for j in self.large_columns)
        if sum(rr) != sum(cc):
            raise ValueError("physical residual totals differ")
        return rr,cc

    def residual_margins(self, state):
        return self._residual_margins(self.validate_state(state))

    def completion_request(self, state):
        rr,cc = self.residual_margins(state)
        return CompletionRequest(rr,cc,self.large_capacity)

    def repair_crossing(self, state):
        state = self.validate_state(state, require_defect=True)
        s,t = state.defect_labels()
        return self.cells[t][0],self.cells[s][1]

    def repair(self, state):
        state = self.validate_state(state, require_defect=True)
        s,t = state.defect_labels()
        values = list(state.row_view)
        values[t] -= 1
        crossing = self.locations.get((self.cells[t][0],self.cells[s][1]))
        if crossing is not None:
            values[crossing] += 1
        return self.validate_state(PhysicalState(tuple(values),tuple(values)))

    def _completion(self, request, completion):
        if not isinstance(completion,(tuple,list)):
            raise TypeError("completion must be a finite tuple/list table")
        if request.empty:
            if completion != ():
                raise ValueError("empty rectangle completion must be ()")
            return ()
        nr,nc = len(request.row_sums),len(request.column_sums)
        if len(completion) != nr:
            raise ValueError("completion has the wrong shape")
        rows = []
        for i in range(nr):
            row = completion[i]
            if not isinstance(row,(tuple,list)):
                raise TypeError("completion rows must be finite tuples or lists")
            if len(row) != nc:
                raise ValueError("completion has the wrong shape")
            values = tuple(_integer(row[j],"completion entry") for j in range(nc))
            if any(v > request.capacity for v in values):
                raise ValueError("completion exceeds source capacity")
            rows.append(values)
        table = tuple(rows)
        if tuple(map(sum,table)) != request.row_sums or tuple(sum(row[j] for row in table)
                for j in range(len(request.column_sums))) != request.column_sums:
            raise ValueError("completion has the wrong margins")
        return table

    def _draw_completion(self, state, execution):
        request = self.completion_request(state)
        if request.empty:
            return ()
        context = CompletionContext(execution,self.oracle_contract)
        execution.calls += 1
        try:
            completion = self.oracle.draw(request,context)
        finally:
            context._close()
        execution.work += context.work_units
        if completion is None:
            execution.failures += 1
            return None
        return self._completion(request,completion)

    def draw_completion(self, state, rng: FairBitSource | None = None):
        execution = _Execution(rng if rng is not None else random.SystemRandom(), self.oracle_contract.max_fair_bits)
        completion = self._draw_completion(self.validate_state(state),execution)
        return CompletionDraw(completion,execution.bits,execution.work,execution.calls)

    def source_accepts(self, source, target, completion):
        source,target = self.validate_state(source),self.validate_state(target)
        r0,c0 = self._residual_margins(source)
        r1,c1 = self._residual_margins(target)
        completion = self._completion(CompletionRequest(r0,c0,self.large_capacity),completion)
        if self.unit_branch:
            return True
        dr,dc = tuple(b-a for a,b in zip(r0,r1)),tuple(b-a for a,b in zip(c0,c1))
        return all(v + (dr[0]-sum(dc[1:]) if i==j==0 else dc[j] if i==0 else dr[i] if j==0 else 0) >= 0
                   for i,row in enumerate(completion) for j,v in enumerate(row))

    def proposal_descriptors(self, state):
        """O(p) sparse descriptor list, with O(1) candidate feasibility checks.

        Every actual neighbor occurs once. List order may depend on the state;
        proposal mass remains the GLOBAL beta for every neighbor in either
        direction. No degree-sized list of full profiles is constructed.
        """
        state = self.validate_state(state,require_defect=True)
        s,t = state.defect_labels()
        row_used,column_used = [0]*self.m,[0]*self.n
        for (i,j),x,q in zip(self.cells,state.row_view,state.column_view):
            row_used[i] += x; column_used[j] += q
        profile = state.row_view+tuple(self.U-v for v in state.column_view)
        descriptors = []

        def consider(receiver,donor):
            if profile[donor]==0 or profile[receiver]==self.U:
                return
            rd,cd = {},{}
            for coordinate,sign in ((receiver,1),(donor,-1)):
                i,j = self.cells[coordinate % self.p]
                if coordinate < self.p: rd[i] = rd.get(i,0)+sign
                else: cd[j] = cd.get(j,0)-sign
            for i,change in rd.items():
                used = row_used[i]+change
                if used > self.problem.row_sums[i] or (i not in self.large_row_locations and used != self.problem.row_sums[i]):
                    return
            for j,change in cd.items():
                used = column_used[j]+change
                if used > self.problem.column_sums[j] or (j not in self.large_column_locations and used != self.problem.column_sums[j]):
                    return
            descriptors.append((receiver,donor))

        for receiver_view in range(2):
            for donor_view in range(2):
                for donor in range(self.p):
                    if donor != s:
                        consider(receiver_view*self.p+s,donor_view*self.p+donor)
        for donor_view in range(2):
            for receiver_view in range(2):
                for receiver in range(self.p):
                    if receiver not in (s,t):  # overlap owned by the first family
                        consider(receiver_view*self.p+receiver,donor_view*self.p+t)
        crossing = self.locations.get((self.cells[t][0],self.cells[s][1]))
        if crossing is not None and crossing not in (s,t):
            descriptors.append(None)  # non-exchange designated repair
        if len(descriptors) > self.Q:
            raise ArithmeticError("actual defect degree exceeds global shape bound")
        return tuple(descriptors)

    def proposal(self, state, slot: int):
        """One compact global-Q slot; unused slots and labels >=Q hold."""
        state = self.validate_state(state,require_defect=True)
        _integer(slot,"slot")
        if slot >= self.Q:
            return None
        descriptors = self.proposal_descriptors(state)
        if slot >= len(descriptors):
            return None
        descriptor = descriptors[slot]
        if descriptor is None:
            return self.repair(state)
        receiver,donor = descriptor
        x,q = list(state.row_view),list(state.column_view)
        if receiver < self.p: x[receiver] += 1
        else: q[receiver-self.p] -= 1
        if donor < self.p: x[donor] -= 1
        else: q[donor-self.p] += 1
        return self.validate_state(PhysicalState(tuple(x),tuple(q)))

    def step(self, state, rng: FairBitSource | None = None):
        state = self.validate_state(state,require_defect=True)
        execution = _Execution(rng if rng is not None else random.SystemRandom(),self.max_fair_bits)
        slot = execution.word(self.proposal_bits)
        target = self.proposal(state,slot)
        trials = 0

        def finish(endpoint,outcome):
            return GeneralDefectStep(endpoint,outcome,slot,trials,execution.bits,execution.calls,
                                     execution.work,execution.failures,self.error)

        if target is None:
            return finish(state,"proposal_hold")
        completion = self._draw_completion(state,execution)
        if completion is None:
            return finish(state,"oracle_failure")
        if not self.source_accepts(state,target,completion):
            return finish(state,"initial_rejection")
        if not target.balanced:
            return finish(target,"direct")
        catalog = BalancedNeighborCatalog(self.problem.row_sums,self.problem.column_sums,target,
                                           U=self.U,L=self.L,large_capacity=self.large_capacity)
        if not catalog.degree:
            raise ArithmeticError("visited balanced center has no neighbors")
        for trials in range(1,self.star_trials+1):
            word = execution.word(self.geometry_bits)
            neighbor = catalog.unrank(catalog.degree*word//(1 << self.geometry_bits))
            completion = self._draw_completion(target,execution)
            if completion is not None and self.source_accepts(target,neighbor,completion):
                return finish(neighbor,"star_exit")
        return finish(state,"star_cap")
