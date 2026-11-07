"""Reviewed shape-dependent scales for a prescribed completion-block size.

These are scalar consequences of the source padding and accepted-edge bounds,
not a compiled physical theorem or a complete sampler runtime certificate.
Classification is checked at the computed cutoff; it is not assumed merely
because a caller requests a particular dense-block size.
"""

from dataclasses import dataclass
from fractions import Fraction

from .general_defect_chain import defect_degree_bound
from .tables import TableProblem, _integer


@dataclass(frozen=True)
class CompletionBlockScales:
    U: int
    L: int
    small_cells: int
    effective_width: int
    degree_bound: int
    proposal_bits: int
    rational_inverse_gap: int
    dyadic_inverse_gap: int
    stationary_success_lower_bound: Fraction
    completion_margin_bound: int
    local_completion_dimension: int | None


def _scales(problem, large_row_count, large_column_count, padding, local_dimension,
            *, refined_growth=False):
    m, n = problem.shape
    rows, columns = problem.row_sums, problem.column_sums
    if m < 2 or n < 2 or m*n == large_row_count*large_column_count:
        raise ValueError("requires m,n >= 2 and at least one small cell")
    if not 1 <= large_row_count <= m or not 1 <= large_column_count <= n:
        raise ValueError("completion block dimensions must fit the table")
    if any(value <= 0 for value in rows+columns):
        raise ValueError("requires positive ordinary margins")
    if sum(rows) != sum(columns):
        raise ValueError("requires equal margin totals")
    if any(problem.lower_bounds[i][j] or problem.upper_bounds[i][j] != min(rows[i], columns[j])
           for i in range(m) for j in range(n)):
        raise ValueError("requires ordinary unrestricted margins")
    e = (m-1)*(n-1)
    g = large_row_count*large_column_count
    # The reciprocal zero-cell comparison gives the alternative full-table
    # growth parameter m+n-2. Historical helpers retain their old cutoff.
    growth = min(e, m+n-2) if refined_growth else e
    cutoff = max(2, 2*padding, (47*g*padding*growth+31)//32-1)
    large_rows = tuple(i for i, r in enumerate(rows) if r >= cutoff)
    large_columns = tuple(j for j, c in enumerate(columns) if c >= cutoff)
    if len(large_rows) != large_row_count or len(large_columns) != large_column_count:
        raise ValueError("computed cutoff does not leave the requested completion block")
    lr, lc = set(large_rows), set(large_columns)
    p = m*n-g
    width = max(2, 1+max(min(rows[i], columns[j]) for i in range(m) for j in range(n)
                        if i not in lr or j not in lc))
    a, b = m-large_row_count, n-large_column_count
    degree = defect_degree_bound(m, n, a, b)
    bits = (2*degree-1).bit_length()
    # Actual balanced children are <= V-1: their supported path diameter is
    # at most V-1. Apply retained-stencil transport, then square-root repair.
    # The global physical/encoded assembly remains open.
    quarter_width = (width+1)**2//4
    transversal = (width-1)*width + 2*(p-1)*quarter_width
    coefficient = 2*p*p*transversal
    lower_fiber = max(a*(n*a-1), b*(m*b-1))
    margin_bound = max(max(rows)+large_column_count*padding,
                       max(columns)+large_row_count*padding)
    return CompletionBlockScales(
        cutoff, padding, p, width, degree, bits,
        4*degree*coefficient, 2*(1 << bits)*coefficient,
        Fraction(lower_fiber, 2*p*p), margin_bound, local_dimension)


def two_by_two_core_scales(problem: TableProblem) -> CompletionBlockScales:
    """Check and bound the positive ordinary class with exactly two large lines.

    Set L=3 and U=max(6,ceil(141*(m-1)*(n-1)/8)-1). The ordinary
    sequential-padding certificate gives padded/original count ratio <=2;
    the 2x2 completion has e=1, so L=3 meets directed half acceptance.
    Exactly two rows AND two columns must reach this cutoff, with at least
    one small cell. A direct finite-word SmallCompletionOracle can supply the
    remaining completion calls; its precision and costs must still be charged.

    Returned inverse-gap allowances use the reviewed effective-width and
    shape-degree arguments. No walk, random draw or state enumeration occurs.
    """
    return _scales(problem, 2, 2, 3, None)


def reduced_completion_scales(problem: TableProblem, *, large_row_count: int,
                              large_column_count: int) -> CompletionBlockScales:
    """Choose the smaller sufficient completion padding from two proofs.

    For a nonempty R-by-C block, set
    L=min(7,max(1,ceil(3*(R-1)*(C-1)/min(R,C)))). Every residual row is at
    least C*L and every residual column at least R*L. The compiled directed
    acceptance theorem therefore supplies the same half-acceptance premise
    at the block-dependent padding. The compiled weighted-switch/convolution
    and physical reference-move proofs supply half acceptance at L=7 for
    any nonempty block size. For the full table's dimensions m,n and g=R*C,
    set U=max(2,2L,ceil(47*g*L*min((m-1)*(n-1),m+n-2)/32)-1).
    This uses the smaller of the original donor-pair growth comparison and
    the reviewed reciprocal zero-cell comparison. Classification is checked
    at this new cutoff; a classification at an older cutoff is insufficient.
    The global retained-stencil gap assembly remains open.

    These are ideal-oracle inverse-gap allowances. The existing generic
    completion program requires stronger floors; this helper does not certify
    its use. A SmallCompletionOracle supports blocks up to 2-by-2 directly.
    """
    _integer(large_row_count, "large_row_count", positive=True)
    _integer(large_column_count, "large_column_count", positive=True)
    smaller = min(large_row_count, large_column_count)
    donors = (large_row_count-1)*(large_column_count-1)
    padding = min(7, max(1, (3*donors+smaller-1)//smaller))
    return _scales(problem, large_row_count, large_column_count, padding, None,
                   refined_growth=True)


def local_completion_scales(problem: TableProblem, *, large_row_count: int,
                            large_column_count: int) -> CompletionBlockScales:
    """Use the compiled generic completion interface at its local dimension.

    d'=max(14,R,C,(R-1)(C-1)+1), L=3d', and
    U=max(2L,ceil(47*R*C*L*(m-1)*(n-1)/32)-1). The actual margins
    must have exactly R large rows and C large columns at this U. Residual
    rows/columns then meet the generic completion program's 3d' floors.

    This computes and checks the scalar inputs. A physical reindexing adapter,
    finite-word completion precision and encoded general-trace composition
    remain separate; this function does not execute the compiled program.
    """
    _integer(large_row_count, "large_row_count", positive=True)
    _integer(large_column_count, "large_column_count", positive=True)
    dimension = max(14, large_row_count, large_column_count,
                    (large_row_count-1)*(large_column_count-1)+1)
    return _scales(problem, large_row_count, large_column_count, 3*dimension, dimension)
