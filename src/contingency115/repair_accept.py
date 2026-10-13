"""Bounded repair-and-accept output for the existing all-small physical walker.

The ideal stationary terminal rule is exact. Fixed-bit rational thresholds and
finite walks are not exact uniform sampling; both have explicit allowances. This
reuses the exponential ``IdealPhysicalChain`` reference backend, not a new
scalable sampler or a compiled implementation of the paper's algorithm.
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from fractions import Fraction
import random
from typing import Literal, Protocol

from .ideal_chain import IdealPhysicalChain
from .tables import ComputationBudgetExceeded, Table, _integer, _rational


class FairBitSource(Protocol):
    """Words uniform in range(2**bits), independently conditional on past calls.

    Seeded ``random.Random`` is available for reproducible diagnostics. Its
    pseudorandom stream is not a mathematical certificate of this assumption.
    """

    def getrandbits(self, bits: int) -> int: ...


@dataclass(frozen=True)
class RepairAcceptBudget:
    max_attempts: int = 1_000
    max_physical_steps: int = 1_000_000
    max_fair_bits: int = 10_000_000

    def __post_init__(self):
        for field in fields(self):
            _integer(getattr(self, field.name), field.name, positive=True)


@dataclass(frozen=True)
class TerminalResult:
    repaired_table: Table
    fiber_size: int
    outcome: Literal["accepted", "rejected"]
    acceptance_threshold: int
    fair_bits: int

    @property
    def table(self) -> Table | None:
        return self.repaired_table if self.outcome == "accepted" else None


@dataclass(frozen=True)
class RepairAcceptResult:
    table: Table | None
    endpoint_state_index: int
    attempts: int
    physical_steps: int
    fair_bits: int
    rejected_attempts: int
    fallback_used: bool = False

    @property
    def exhausted(self) -> bool:
        return self.table is None or self.fallback_used


@dataclass(frozen=True)
class RepairAcceptError:
    stationary_exhaustion: Fraction
    endpoint_coupling: Fraction
    acceptance_rounding: Fraction

    @property
    def total_variation_bound(self) -> Fraction:
        return min(Fraction(1), self.stationary_exhaustion +
                   self.endpoint_coupling + self.acceptance_rounding)


class _Words:
    """Count fresh words and adapt dyadic draws to the existing step contract."""

    def __init__(self, source: FairBitSource):
        self.source, self.bits = source, 0

    def word(self, bits: int) -> int:
        if not bits:
            return 0
        value = _integer(self.source.getrandbits(bits), "fair-bit word")
        if value >= 1 << bits:
            raise ValueError("fair-bit source returned a word outside its range")
        self.bits += bits
        return value

    def randrange(self, stop: int) -> int:
        if stop <= 0 or stop & (stop - 1):
            raise ValueError("physical walker requested a non-dyadic draw")
        return self.word(stop.bit_length() - 1)


class RepairAcceptRule:
    """Terminal rule restricted to ordinary, positive, strictly all-small margins.

    ``chain`` must be the existing unit-weight reference chain. An arbitrary
    replacement graph/matrix is not certified by this wrapper. Construction
    checks the exposed scope assumptions; it does not repeat the chain builder.
    """

    def __init__(self, chain: IdealPhysicalChain):
        problem = chain.problem
        m, n = problem.shape
        if not m or not n:
            raise ValueError("requires at least one row and one column")
        if any(value <= 0 or value >= chain.U
               for value in problem.row_sums + problem.column_sums):
            raise ValueError("requires positive margins strictly below U")
        if sum(problem.row_sums) != sum(problem.column_sums):
            raise ValueError("requires equal row and column totals")
        if any(problem.lower_bounds[i][j] or
               problem.upper_bounds[i][j] != min(problem.row_sums[i], problem.column_sums[j])
               for i in range(m) for j in range(n)):
            raise ValueError("requires ordinary margins without extra cell bounds")
        if chain.large_rows or chain.large_columns or chain.small_cells != tuple(
                (i, j) for i in range(m) for j in range(n)):
            raise ValueError("requires every physical cell to be small")
        size = len(chain.states)
        if not size or chain.completions != (((),),) * size or chain.stationary != (
                Fraction(1, size),) * size:
            raise ValueError("requires the ordinary unit-weight physical chain")
        if chain.beta.numerator != 1 or chain.beta.denominator & (chain.beta.denominator - 1):
            raise ValueError("requires the existing dyadic physical proposal")
        self.chain = chain
        p = m * n
        self.fiber_lower_bound = 1 + (p - 1) * max(m, n)
        self.fiber_upper_bound = 1 + (p - 1) * min(p, sum(problem.row_sums))
        self.inverse_success_allowance = Fraction(self.fiber_upper_bound, self.fiber_lower_bound)

    def _index(self, state_index: int) -> int:
        _integer(state_index, "state_index")
        if state_index >= len(self.chain.states):
            raise IndexError("state index outside the physical chain")
        return state_index

    def repair(self, state_index: int) -> Table:
        """Apply the designated crossing repair; validate the returned margins."""
        state = self.chain.states[self._index(state_index)]
        m, n = self.chain.problem.shape
        if len(state.row_view) != m * n or len(state.column_view) != m * n:
            raise ValueError("physical state has the wrong shape")
        values = list(state.row_view)
        if not state.balanced:
            labels = state.defect_labels()
            if labels is None:
                raise ValueError("physical state has no single ordered defect")
            s, t = labels
            values[t] -= 1
            values[(t // n) * n + s % n] += 1
        return self.chain.problem.validate_table(tuple(
            tuple(values[i * n:(i + 1) * n]) for i in range(m)))

    def fiber_size(self, table: Table) -> int:
        table = self.chain.problem.validate_table(table)
        p = self.chain.problem.shape[0] * self.chain.problem.shape[1]
        return 1 + (p - 1) * sum(value > 0 for row in table for value in row)

    def _terminal(self, state_index: int, acceptance_bits: int, words: _Words) -> TerminalResult:
        table = self.repair(state_index)
        ell = self.fiber_size(table)
        threshold = (self.fiber_lower_bound << acceptance_bits) // ell
        value = words.word(acceptance_bits)
        outcome = "accepted" if value < threshold else "rejected"
        return TerminalResult(table, ell, outcome, threshold, acceptance_bits)

    def terminal(self, state_index: int, *, acceptance_bits: int,
                 rng: FairBitSource | None = None) -> TerminalResult:
        """One fresh k-bit word; accept rank < floor(2**k*c/ell).

        Its acceptance probability is rounded down from c/ell by less than
        2**(-k). Zero bits are valid: accept exactly when c=ell. Conditional
        stationary output need not be uniform after rounding.
        """
        self._index(state_index)
        _integer(acceptance_bits, "acceptance_bits")
        return self._terminal(state_index, acceptance_bits,
                              _Words(rng if rng is not None else random.SystemRandom()))

    def stationary_output_law(self, *, acceptance_bits: int | None = None):
        """Exact diagnostic: (successful table masses, rejection mass).

        None describes the ideal rational c/ell coin without executing an
        unbounded integer draw. An integer describes this backend's finite
        threshold law; that conditional output law can be biased.
        """
        if acceptance_bits is not None:
            _integer(acceptance_bits, "acceptance_bits")
        law, rejected = {}, Fraction(0)
        for index, mass in enumerate(self.chain.stationary):
            table = self.repair(index)
            ell = self.fiber_size(table)
            success = (Fraction(self.fiber_lower_bound, ell) if acceptance_bits is None
                       else Fraction((self.fiber_lower_bound << acceptance_bits) // ell,
                                     1 << acceptance_bits))
            law[table] = law.get(table, Fraction(0)) + mass * success
            rejected += mass * (1 - success)
        return dict(sorted(law.items())), rejected

    def error_bound(self, *, attempts: int, acceptance_bits: int,
                    endpoint_tv: int | Fraction) -> RepairAcceptError:
        """TV allowance given an endpoint-mixing bound, after feasible fallback.

        Independently restarted endpoints must have TV <= endpoint_tv from the
        uniform physical law. No finite-walk mixing bound is inferred here.
        Exhaustion is mapped to a fixed feasible fallback. This does not bound
        the law conditioned on acceptance under the finite-bit sampler.
        """
        _integer(attempts, "attempts", positive=True)
        _integer(acceptance_bits, "acceptance_bits")
        delta = _rational(endpoint_tv, "endpoint_tv")
        if delta > 1:
            raise ValueError("endpoint_tv must lie between zero and one")
        return RepairAcceptError(
            (1 - Fraction(self.fiber_lower_bound, self.fiber_upper_bound)) ** attempts,
            attempts * delta, Fraction(attempts, 1 << acceptance_bits))

    def run(self, *, attempts: int, steps_per_attempt: int, acceptance_bits: int,
            start_index: int = 0, rng: FairBitSource | None = None,
            seed: int | None = None, budget: RepairAcceptBudget | None = None,
            fallback: Table | None = None) -> RepairAcceptResult:
        """Restart the existing walker; return first acceptance or explicit exhaustion.

        One stream advances across all walks, terminal words, and attempts;
        restarts reset only the physical state. Never reseed inside an attempt.
        A supplied rng must meet FairBitSource's conditional independence
        contract. Seed is an exclusive reproducibility option, not exact entropy.
        Preflight caps reject excessive schedules before consuming randomness.
        """
        self._index(start_index)
        _integer(attempts, "attempts", positive=True)
        _integer(acceptance_bits, "acceptance_bits")
        _integer(steps_per_attempt, "steps_per_attempt")
        if rng is not None and seed is not None:
            raise ValueError("supply rng or seed, not both")
        if seed is not None:
            _integer(seed, "seed")
        if fallback is not None:
            fallback = self.chain.problem.validate_table(fallback)
        limits = budget if budget is not None else RepairAcceptBudget()
        walk_bits = self.chain.beta.denominator.bit_length() - 1
        planned_bits = attempts * (steps_per_attempt * walk_bits + acceptance_bits)
        for value, cap, name in ((attempts, limits.max_attempts, "max_attempts"),
                                 (attempts * steps_per_attempt, limits.max_physical_steps, "max_physical_steps"),
                                 (planned_bits, limits.max_fair_bits, "max_fair_bits")):
            if value > cap:
                raise ComputationBudgetExceeded(f"repair acceptance exceeded {name}")
        source = rng if rng is not None else (random.Random(seed) if seed is not None else random.SystemRandom())
        words = _Words(source)
        rejected = steps = 0
        for attempt in range(1, attempts + 1):
            index = start_index
            for _ in range(steps_per_attempt):
                index = self.chain.step(index, words)
                steps += 1
            result = self._terminal(index, acceptance_bits, words)
            if result.table is not None:
                return RepairAcceptResult(result.table, index, attempt, steps, words.bits, rejected)
            rejected += 1
        return RepairAcceptResult(fallback, index, attempts, steps, words.bits, rejected,
                                  fallback is not None)
