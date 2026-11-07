"""Finite-word uniform completion for 2x2 and unique thin rectangles.

No fiber is enumerated. For a fiber of N tables, a k-bit word maps to rank
floor(N*word/2**k). Its exact conditional TV is ``integer_draw_tv(N, k)``;
the declared global contract uses the monotone envelope N/(4*2**k).
Fresh conditional fair words remain a premise of CompletionContext. Work
units count bounded logical stages/cells, not CPU time or bit operations.
"""

from dataclasses import dataclass, field
from fractions import Fraction as F

from .defect_chain import integer_draw_tv
from .general_defect_chain import (
    CompletionContext, CompletionOracleContract, CompletionRequest,
)
from .tables import ComputationBudgetExceeded, InfeasibleTableError, Table, _integer


@dataclass(frozen=True)
class SmallCompletionOracle:
    """Bounded completion backend for <=2x2, or one row/column of any length.

    ``max_margin`` bounds each requested margin; ``max_input_bits`` bounds
    their combined bit lengths plus capacity. ``max_cells`` also bounds each
    axis, including empty rectangles. Input rejection occurs before RNG use.
    The global error allowance includes every feasible supported request;
    ``request_tv_error`` supplies its sharper exact finite-word error.

    Accounting: one dispatch unit, 1+m+n validation units, and 16+m*n
    arithmetic/output units, each charged before its stage. Each arithmetic
    operation has bounded operands but its machine cost is not one unit.
    """

    max_margin: int
    word_bits: int
    max_input_bits: int = 100_000
    max_cells: int = 100_000
    max_word_bits: int = 100_000
    contract: CompletionOracleContract = field(init=False)

    def __post_init__(self):
        _integer(self.max_margin, "max_margin")
        _integer(self.word_bits, "word_bits")
        _integer(self.max_input_bits, "max_input_bits", positive=True)
        _integer(self.max_cells, "max_cells", positive=True)
        _integer(self.max_word_bits, "max_word_bits")
        if self.word_bits > self.max_word_bits:
            raise ComputationBudgetExceeded("small completion exceeded max_word_bits")
        if self.max_margin.bit_length() > self.max_input_bits:
            raise ComputationBudgetExceeded("small completion max_margin exceeded max_input_bits")
        error = (F(0) if not self.max_margin else
                 min(F(1), F(self.max_margin+1, 4 << self.word_bits)))
        object.__setattr__(self, "contract", CompletionOracleContract(
            error, self.word_bits, 18+3*self.max_cells))

    def _prepare(self, request, context=None):
        if not isinstance(request, CompletionRequest):
            raise TypeError("request must be a CompletionRequest")
        if not isinstance(request.row_sums, (tuple, list)) or not isinstance(
                request.column_sums, (tuple, list)):
            raise TypeError("completion margins must be tuples or lists")
        m, n = len(request.row_sums), len(request.column_sums)
        if max(m, n, m*n) > self.max_cells:
            raise ComputationBudgetExceeded("small completion exceeded max_cells")
        if m > 1 and n > 1 and (m > 2 or n > 2):
            raise ValueError("small completion supports only <=2x2 or a single row/column")
        if context is not None:
            context.charge(1+m+n)
        rows = tuple(_integer(v, "row margin") for v in request.row_sums)
        columns = tuple(_integer(v, "column margin") for v in request.column_sums)
        capacity = _integer(request.capacity, "capacity")
        if any(v > self.max_margin for v in rows+columns):
            raise ComputationBudgetExceeded("small completion exceeded max_margin")
        if sum(v.bit_length() for v in rows+columns)+(capacity.bit_length()) > self.max_input_bits:
            raise ComputationBudgetExceeded("small completion exceeded max_input_bits")
        if sum(rows) != sum(columns):
            raise InfeasibleTableError("completion margin totals differ")
        if context is not None:
            context.charge(16+m*n)
        if not m or not n:
            # Equal nonnegative totals force all extant margins to be zero.
            return rows, columns, 0, 0
        if m == 1 or n == 1:
            entries = columns if m == 1 else rows
            if any(v > capacity for v in entries):
                raise InfeasibleTableError("unique completion exceeds capacity")
            return rows, columns, 0, 0
        r0, r1 = rows
        c0, _ = columns
        low = max(0, r0-capacity, c0-capacity, c0-r1)
        high = min(capacity, r0, c0, capacity+c0-r1)
        if low > high:
            raise InfeasibleTableError("2x2 completion fiber is empty under capacity")
        return rows, columns, low, high

    def request_tv_error(self, request: CompletionRequest) -> F:
        """Exact conditional TV for this request; rejects unsupported inputs."""
        rows, columns, low, high = self._prepare(request)
        if len(rows) < 2 or len(columns) < 2:
            return F(0)
        return integer_draw_tv(high-low+1, self.word_bits)

    def draw(self, request: CompletionRequest, context: CompletionContext) -> Table:
        """Return a feasible completion using at most one fixed-length word.

        Well-formed infeasible requests raise InfeasibleTableError; malformed
        or out-of-contract requests raise rather than produce a failed draw.
        Feasible draws never return None and never use rejection sampling.
        The empty-rectangle convention is (), matching GeneralDefectChain.
        """
        context.charge(1)
        rows, columns, low, high = self._prepare(request, context)
        if not rows or not columns:
            return ()
        if len(rows) == 1:
            return (columns,)
        if len(columns) == 1:
            return tuple((v,) for v in rows)
        size = high-low+1
        word = context.word(self.word_bits) if size > 1 and self.word_bits else 0
        word = _integer(word, "fair-bit word")
        if word >= 1 << self.word_bits:
            raise ValueError("fair-bit source returned a word outside its range")
        x = low+(size*word >> self.word_bits)
        return ((x, rows[0]-x), (columns[0]-x, rows[1]-columns[0]+x))
