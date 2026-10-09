"""Exact adjacent-lattice codec for ordinary fixed-margin completions.

This is a deterministic integer codec and scale planner, not a completion
sampler. The geometric count comparison attached to dense plans is a reviewed
mathematical argument, not a Python or Lean proof. No oracle is implemented.
Only nonempty row/column index sets, as supported by TableProblem, are accepted.
"""

from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

from .tables import ComputationBudgetExceeded, Table, TableProblem, _integer


def _ordinary(problem: TableProblem) -> None:
    if not isinstance(problem, TableProblem):
        raise TypeError("problem must be a TableProblem")
    a, b = problem.shape
    if sum(problem.row_sums) != sum(problem.column_sums):
        raise ValueError("ordinary row and column totals must agree")
    if any(problem.lower_bounds[i][j] != 0 or
           problem.upper_bounds[i][j] != min(problem.row_sums[i], problem.column_sums[j])
           for i in range(a) for j in range(b)):
        raise ValueError("the codec requires semantically unrestricted cell bounds")


def _offsets(values: Sequence[Sequence[int]], a: int, b: int, k: int) -> Table:
    if len(values) != a-1 or any(len(row) != b-1 for row in values):
        raise ValueError(f"offsets must have shape {a-1} by {b-1}")
    result = tuple(tuple(_integer(x, "offset") for x in row) for row in values)
    if any(x >= k for row in result for x in row):
        raise ValueError("each offset must be less than k")
    return result


def _prefix(table: Table) -> Table:
    """Full prefix array: index (i,j) sums the first i rows and j columns."""
    a, b = len(table), len(table[0])
    values = [[0]*(b+1) for _ in range(a+1)]
    for i in range(a):
        for j in range(b):
            values[i+1][j+1] = (table[i][j] + values[i][j+1]
                                + values[i+1][j] - values[i][j])
    return tuple(tuple(row) for row in values)


def _second_difference(prefix: Table) -> Table:
    return tuple(tuple(prefix[i+1][j+1] - prefix[i][j+1]
                       - prefix[i+1][j] + prefix[i][j]
                       for j in range(len(prefix[0])-1))
                 for i in range(len(prefix)-1))


@dataclass(frozen=True)
class LatticeCompletionPlan:
    original: TableProblem
    fine: TableProblem
    k: int

    def __post_init__(self) -> None:
        _ordinary(self.original)
        _ordinary(self.fine)
        _integer(self.k, "k", positive=True)
        a, b = self.original.shape
        if (self.fine.row_sums != tuple(self.k*(x+2*b) for x in self.original.row_sums)
                or self.fine.column_sums != tuple(self.k*(x+2*a) for x in self.original.column_sums)):
            raise ValueError("fine margins do not match the dilation and padding")

    @property
    def dimension(self) -> int:
        a, b = self.original.shape
        return (a-1)*(b-1)

    @property
    def preimages_per_table(self) -> int:
        return self.k**self.dimension


def plan_lattice_completion(problem: TableProblem, k: int) -> LatticeCompletionPlan:
    """Construct k*(R+2b), k*(P+2a), for any positive integer k."""
    _ordinary(problem)
    k = _integer(k, "k", positive=True)
    a, b = problem.shape
    fine = TableProblem(tuple(k*(r+2*b) for r in problem.row_sums),
                        tuple(k*(p+2*a) for p in problem.column_sums))
    return LatticeCompletionPlan(problem, fine, k)


@dataclass(frozen=True)
class DecodedCompletion:
    candidate: Table
    offsets: Table
    accepted: bool
    rounding_errors: tuple[tuple[Fraction, ...], ...]

    @property
    def table(self) -> Table | None:
        """Accepted original table; rejected candidates can contain negatives."""
        return self.candidate if self.accepted else None


def encode_completion(plan: LatticeCompletionPlan, table: Sequence[Sequence[int]],
                      offsets: Sequence[Sequence[int]]) -> Table:
    """Encode one original table and one interior prefix-offset assignment.

    The offset prefix has zero first and last rows/columns. Its second
    differences are added to k*(X+2J). Each cell is nonnegative because its
    perturbation is at least -2*(k-1), and its base is at least 2*k.
    """
    if not isinstance(plan, LatticeCompletionPlan):
        raise TypeError("plan must be a LatticeCompletionPlan")
    table = plan.original.validate_table(table)
    a, b = plan.original.shape
    offsets = _offsets(offsets, a, b, plan.k)
    boundary = tuple(tuple(offsets[i-1][j-1] if 0 < i < a and 0 < j < b else 0
                           for j in range(b+1)) for i in range(a+1))
    difference = _second_difference(boundary)
    result = tuple(tuple(plan.k*(table[i][j]+2)+difference[i][j]
                         for j in range(b)) for i in range(a))
    return plan.fine.validate_table(result)


def decode_completion(plan: LatticeCompletionPlan,
                      table: Sequence[Sequence[int]]) -> DecodedCompletion:
    """Round all prefixes down after division by k, then unpad each cell.

    The rounded candidate retains exactly the original margins, including
    zero margins. Acceptance means precisely that all candidate cells are
    nonnegative. Interior prefix residues recover the unique offset data.
    The error in each rounded expanded cell is strictly below 2 in absolute
    value when k>1; k=1 has zero error.
    """
    if not isinstance(plan, LatticeCompletionPlan):
        raise TypeError("plan must be a LatticeCompletionPlan")
    table = plan.fine.validate_table(table)
    prefix = _prefix(table)
    rounded_prefix = tuple(tuple(x//plan.k for x in row) for row in prefix)
    expanded = _second_difference(rounded_prefix)
    a, b = plan.original.shape
    candidate = tuple(tuple(x-2 for x in row) for row in expanded)
    offsets = tuple(tuple(prefix[i][j] % plan.k for j in range(1, b))
                    for i in range(1, a))
    errors = tuple(tuple(Fraction(table[i][j], plan.k)-expanded[i][j]
                         for j in range(b)) for i in range(a))
    accepted = all(x >= 0 for row in candidate for x in row)
    if accepted:
        plan.original.validate_table(candidate)
    return DecodedCompletion(candidate, offsets, accepted, errors)


@dataclass(frozen=True)
class DenseCompletionPlan:
    codec: LatticeCompletionPlan
    d: int
    L: int
    geometric_count_ratio_upper_bound: Fraction

    @property
    def conditional_acceptance_lower_bound(self) -> Fraction:
        """Conditional on the reviewed geometric count argument and uniform input."""
        return 1/self.geometric_count_ratio_upper_bound


def geometric_count_envelope(rows: int, columns: int, d: int, k: int, *,
                             max_bound_bits: int = 1_000_000) -> Fraction:
    """Exact arithmetic for alpha=((3d+2+2/k)/(3d-2))^e.

    Preconditions d>=10+(a+1)(b+1), k>=2d imply alpha<4. Interpreting
    alpha as N_fine/(k^e N_original) additionally requires the reviewed
    universal volume/count argument and incident original margins at least
    3bd and 3ad. This function checks arithmetic, not that universal theorem.
    """
    a = _integer(rows, "rows", positive=True)
    b = _integer(columns, "columns", positive=True)
    d = _integer(d, "d", positive=True)
    k = _integer(k, "k", positive=True)
    max_bound_bits = _integer(max_bound_bits, "max_bound_bits", positive=True)
    if d < 10+(a+1)*(b+1):
        raise ValueError("d must be at least 10+(rows+1)*(columns+1)")
    if k < 2*d:
        raise ValueError("the envelope requires k>=2d")
    e = (a-1)*(b-1)
    # This conservative check happens before either potentially large power.
    if e*(d.bit_length()+k.bit_length()+4) > max_bound_bits:
        raise ComputationBudgetExceeded("exact geometric envelope exceeds max_bound_bits")
    return Fraction(k*(3*d+2)+2, k*(3*d-2))**e


def plan_dense_completion(problem: TableProblem, d: int | None = None, *,
                          max_bound_bits: int = 1_000_000) -> DenseCompletionPlan:
    """Plan actual k=d^12 completion input without enumerating either fiber.

    Ambient d may exceed the minimal shape allowance. Original residual
    margins must obey R_i>=3bd and P_j>=3ad. Uniform fine-table draws would
    accept with conditional probability >=1/alpha>1/4; no draw routine,
    independence guarantee, or machine-cost theorem is supplied here.
    """
    _ordinary(problem)
    a, b = problem.shape
    d = 10+(a+1)*(b+1) if d is None else _integer(d, "d", positive=True)
    max_bound_bits = _integer(max_bound_bits, "max_bound_bits", positive=True)
    if 12*d.bit_length() > max_bound_bits:
        raise ComputationBudgetExceeded("d^12 exceeds max_bound_bits")
    k = d**12
    envelope = geometric_count_envelope(a, b, d, k, max_bound_bits=max_bound_bits)
    if any(r < 3*b*d for r in problem.row_sums) or any(p < 3*a*d for p in problem.column_sums):
        raise ValueError("dense residual margins require R_i>=3bd and P_j>=3ad")
    return DenseCompletionPlan(plan_lattice_completion(problem, k), d, 3*d, envelope)
