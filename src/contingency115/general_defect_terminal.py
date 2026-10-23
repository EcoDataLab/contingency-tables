"""Bounded joint repair-and-accept terminal for the weighted defect trace.

At a weighted stationary defect endpoint, an exact fresh uniform conditional
completion makes the ideal joint law uniform. The ideal correction then gives
equal unconditional mass to each ordinary table. Finite words perturb that
terminal law; this module asserts neither walk mixing nor conditional uniformity
of its finite-word accepted outputs. Oracle accuracy and conditional fair words
are premises, including after every past transcript.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
import random
from typing import Callable, Literal

from .general_defect_chain import (CompletionOracleContract, GeneralDefectChain)
from .ideal_chain import PhysicalState
from .repair_accept import FairBitSource
from .tables import ComputationBudgetExceeded, Table, _integer


@dataclass(frozen=True)
class GeneralTerminalError:
    completion_oracle: F
    acceptance_rounding: F

    @property
    def total_variation_bound(self) -> F:
        """Per-attempt TV versus the ideal terminal at the SAME endpoint law."""
        return min(F(1), self.completion_oracle + self.acceptance_rounding)


@dataclass(frozen=True)
class GeneralTerminalResult:
    table: Table | None
    outcome: Literal["accepted", "acceptance_rejection", "unpadding_rejection", "oracle_failure"]
    fiber_size: int | None
    acceptance_threshold: int | None
    fair_bits: int
    oracle_calls: int
    oracle_work: int
    error: GeneralTerminalError


@dataclass(frozen=True)
class _OracleSnapshot:
    contract: CompletionOracleContract
    draw: Callable


@dataclass(frozen=True, init=False)
class GeneralRepairTerminal:
    """One terminal attempt; no profile/table/completion enumeration.

    The constructor copies the canonical source geometry and contract. The
    callback's cooperative cost and TV guarantees remain declared premises,
    rather than runtime-certified CPU bounds or probability guarantees.
    ``max_fair_bits`` caps the planned completion-plus-acceptance allowance
    before any oracle/RNG use, even if a particular draw would reject early.
    """
    _chain: GeneralDefectChain
    acceptance_bits: int
    max_fair_bits: int
    planned_fair_bits: int
    fiber_lower_bound: int
    _small_rows: int
    _small_columns: int
    _row_sizes: tuple[int, ...]
    _column_sizes: tuple[int, ...]
    error: GeneralTerminalError

    def __init__(self, chain: GeneralDefectChain, *, acceptance_bits: int,
                 max_fair_bits: int | None = None):
        if not isinstance(chain, GeneralDefectChain):
            raise TypeError("chain must be a GeneralDefectChain")
        _integer(acceptance_bits, "acceptance_bits")
        cap = chain.budget.max_fair_bits if max_fair_bits is None else max_fair_bits
        _integer(cap, "max_fair_bits")
        if any(v <= 0 for v in chain.problem.row_sums + chain.problem.column_sums):
            raise ValueError("joint terminal requires positive ordinary margins")
        # Rebuild from the source inputs instead of trusting mutable layout
        # attributes or sharing them with a caller's future edits.
        contract = chain.oracle_contract
        oracle = _OracleSnapshot(CompletionOracleContract(
            contract.tv_error, contract.max_fair_bits, contract.max_work_units), chain.oracle.draw)
        snapshot = GeneralDefectChain(chain.problem, U=chain.U, L=chain.L, oracle=oracle,
                                      geometry_bits=chain.geometry_bits, star_trials=chain.star_trials,
                                      budget=chain.budget)
        planned = acceptance_bits + (0 if snapshot.unit_branch else contract.max_fair_bits)
        if planned > cap:
            raise ComputationBudgetExceeded("general terminal exceeded max_fair_bits")
        a, b = snapshot.m-len(snapshot.large_rows), snapshot.n-len(snapshot.large_columns)
        c0 = max(a*(snapshot.n*a-1), b*(snapshot.m*b-1))
        if snapshot.unit_branch:
            c0 = max(c0, (snapshot.p-1)*max(snapshot.m, snapshot.n))
        if c0 <= 0:
            raise ValueError("joint terminal requires small cells and a positive fiber lower bound")
        values = dict(_chain=snapshot, acceptance_bits=acceptance_bits, max_fair_bits=cap,
                      planned_fair_bits=planned, fiber_lower_bound=c0,
                      _small_rows=a, _small_columns=b,
                      _row_sizes=tuple(b if i in snapshot.large_row_locations else snapshot.n
                                       for i in range(snapshot.m)),
                      _column_sizes=tuple(a if j in snapshot.large_column_locations else snapshot.m
                                          for j in range(snapshot.n)),
                      error=GeneralTerminalError(F(0) if snapshot.unit_branch else contract.tv_error,
                                                F(1, 1 << acceptance_bits)))
        for name, value in values.items():
            object.__setattr__(self, name, value)

    def _successful_joint_fiber(self, repaired: PhysicalState) -> int:
        chain = self._chain
        row_used, column_used = [0]*chain.m, [0]*chain.n
        d0 = 0
        for (i, j), value in zip(chain.cells, repaired.row_view):
            row_used[i] += value
            column_used[j] += value
            if value:
                d0 += self._row_sizes[i]*self._column_sizes[j]-1
        u = sum(row_used[i] < chain.problem.row_sums[i] for i in chain.large_rows)
        v = sum(column_used[j] < chain.problem.column_sums[j] for j in chain.large_columns)
        ell = d0 + self._small_rows*self._small_columns*u*v
        if not self.fiber_lower_bound <= ell <= chain.p*(chain.p-1):
            raise ArithmeticError("successful joint fiber violates its proved bounds")
        return ell

    def terminal(self, state: PhysicalState, rng: FairBitSource | None = None) -> GeneralTerminalResult:
        """Repair a fresh completion, unpad when possible, then use a finite word.

        Failure has explicit None mass, covered by the completion-TV contract.
        The same RNG advances through completion and correction; its shape and
        returned words are checked, its fairness/independence are not certified.
        """
        chain = self._chain
        state = chain.validate_state(state, require_defect=True)
        source = rng if rng is not None else random.SystemRandom()
        if not callable(getattr(source, "getrandbits", None)):
            raise TypeError("rng must provide getrandbits")
        draw = chain.draw_completion(state, source)

        def finish(table, outcome, ell=None, threshold=None, extra_bits=0):
            return GeneralTerminalResult(table, outcome, ell, threshold,
                                         draw.fair_bits+extra_bits, draw.oracle_calls,
                                         draw.work_units, self.error)

        if draw.completion is None:
            return finish(None, "oracle_failure")
        repaired = chain.repair(state)
        dense = [list(row) for row in draw.completion]
        crossing = chain.repair_crossing(state)
        if crossing not in chain.locations:
            i, j = crossing
            dense[chain.large_row_locations[i]][chain.large_column_locations[j]] += 1
        if any(value < chain.L for row in dense for value in row):
            return finish(None, "unpadding_rejection")
        # The support/slack formula is valid on these successful pairs only.
        ell = self._successful_joint_fiber(repaired)
        threshold = (self.fiber_lower_bound << self.acceptance_bits)//ell
        word = _integer(source.getrandbits(self.acceptance_bits), "fair-bit word") if self.acceptance_bits else 0
        if word >= 1 << self.acceptance_bits:
            raise ValueError("fair-bit source returned a word outside its range")
        if word >= threshold:
            return finish(None, "acceptance_rejection", ell, threshold, self.acceptance_bits)
        table = [[0]*chain.n for _ in range(chain.m)]
        for (i, j), value in zip(chain.cells, repaired.row_view):
            table[i][j] = value
        for ri, i in enumerate(chain.large_rows):
            for cj, j in enumerate(chain.large_columns):
                table[i][j] = dense[ri][cj]-chain.L
        return finish(chain.problem.validate_table(table), "accepted", ell, threshold, self.acceptance_bits)
