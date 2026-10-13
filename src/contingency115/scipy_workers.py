"""Optional SciPy Patefield backend for the ordinary conditional-worker law.

This targets inverse cell-factorial probabilities, not uniform aggregate
tables. The exact integer-urn reference and its contracts remain in workers.
NumPy and SciPy are imported only when constructing this optional sampler.
"""
from __future__ import annotations

from dataclasses import dataclass
import importlib
from typing import Sequence

from .tables import ComputationBudgetExceeded, Table, _integer
from .workers import _margins


def _scipy_backend():
    try:
        np = importlib.import_module("numpy")
        random_table = importlib.import_module("scipy.stats").random_table
    except (ImportError, AttributeError) as error:
        raise ImportError(
            "ScipyWorkerSampler requires optional NumPy and SciPy >= 1.10 "
            "with scipy.stats.random_table; install SciPy in the environment "
            "running this sampler"
        ) from error
    return np, random_table


@dataclass(frozen=True, init=False)
class ScipyWorkerSampler:
    """Draw ordinary unrestricted fixed-margin tables with SciPy Patefield.

    Accepts plain nonnegative integer margin vectors only. All cells are
    permitted; there are no bounds, structural-zero or interaction arguments.
    The target law is proportional to 1/product(factorial(cell)).

    ``seed`` creates a private NumPy Generator using PCG64; ``rng`` accepts an
    existing NumPy Generator, which is used and advanced in place. Specify at
    most one. Neither option uses NumPy's legacy global RNG. Without either,
    a private Generator is initialized from operating-system entropy. Results
    depend on the NumPy/SciPy versions as well as seed and call sequence.

    Patefield is selected explicitly to avoid Boyett's O(total) scratch space.
    Limits bound dense output size, not native work or random-bit calls. This
    backend uses SciPy's numerical algorithm, without the exact integer-urn
    proof or work counters of OrdinaryWorkerSampler.
    """

    row_sums: tuple[int, ...]
    column_sums: tuple[int, ...]
    max_output_cells: int
    _distribution: object
    _rng: object
    _positive_rows: tuple[int, ...]
    _positive_columns: tuple[int, ...]
    _deterministic_table: Table | None

    def __init__(
        self,
        row_sums: Sequence[int],
        column_sums: Sequence[int],
        *,
        seed: int | None = None,
        rng: object | None = None,
        max_cells: int = 1_000_000,
        max_output_cells: int = 1_000_000,
    ) -> None:
        cell_limit = _integer(max_cells, "max_cells")
        output_limit = _integer(max_output_cells, "max_output_cells")
        rows, columns = _margins(row_sums, column_sums)
        if seed is not None:
            _integer(seed, "seed")
        if seed is not None and rng is not None:
            raise ValueError("specify seed or rng, not both")
        cells = len(rows) * len(columns)
        if cells > cell_limit:
            raise ComputationBudgetExceeded(
                f"output needs {cells} cells, exceeding max_cells={cell_limit}"
            )
        # SciPy's public backend represents margins and totals with int64.
        if sum(rows) > 2**63 - 1:
            raise ValueError("SciPy worker total must fit a signed 64-bit integer")
        np, random_table = _scipy_backend()
        if rng is not None and not isinstance(rng, np.random.Generator):
            raise TypeError("rng must be a NumPy Generator")
        source = rng if rng is not None else np.random.Generator(np.random.PCG64(seed))
        object.__setattr__(self, "row_sums", rows)
        object.__setattr__(self, "column_sums", columns)
        object.__setattr__(self, "max_output_cells", output_limit)
        object.__setattr__(self, "_rng", source)
        positive_rows = tuple(i for i, value in enumerate(rows) if value)
        positive_columns = tuple(j for j, value in enumerate(columns) if value)
        deterministic = None
        if len(positive_rows) <= 1 or len(positive_columns) <= 1:
            if len(positive_rows) <= 1:
                deterministic = tuple(tuple(columns[j] if i in positive_rows else 0
                                            for j in range(len(columns)))
                                      for i in range(len(rows)))
            else:
                deterministic = tuple(tuple(rows[i] if j in positive_columns else 0
                                            for j in range(len(columns)))
                                      for i in range(len(rows)))
        object.__setattr__(self, "_positive_rows", positive_rows)
        object.__setattr__(self, "_positive_columns", positive_columns)
        object.__setattr__(self, "_deterministic_table", deterministic)
        object.__setattr__(self, "_distribution", None if deterministic is not None else
                           random_table(tuple(rows[i] for i in positive_rows),
                                        tuple(columns[j] for j in positive_columns)))

    def sample(self) -> Table:
        """Draw one table as immutable tuples of Python integers."""
        return self.samples(1)[0]

    def samples(self, count: int) -> tuple[Table, ...]:
        """Draw a batch, rejecting excessive output before consuming randomness.

        A zero-sized batch returns (). Every native output is checked for
        shape, integer values, nonnegativity and both fixed margin vectors.
        Invalid library output raises rather than resampling.
        """
        count = _integer(count, "count")
        m, n = len(self.row_sums), len(self.column_sums)
        cells = count * m * n
        if cells > self.max_output_cells:
            raise ComputationBudgetExceeded(
                f"batch needs {cells} cells, exceeding "
                f"max_output_cells={self.max_output_cells}"
            )
        if count == 0:
            return ()
        if self._deterministic_table is not None:
            return (self._deterministic_table,) * count
        values = self._distribution.rvs(
            size=count, method="patefield", random_state=self._rng
        )
        pm, pn = len(self._positive_rows), len(self._positive_columns)
        if values.shape != (count, pm, pn) or values.dtype.kind not in "iu":
            raise RuntimeError("SciPy returned wrong-shaped or noninteger tables")
        tables = []
        for native in values:
            table = [[0]*n for _ in range(m)]
            for i, source_row in enumerate(self._positive_rows):
                for j, source_column in enumerate(self._positive_columns):
                    table[source_row][source_column] = int(native[i, j])
            tables.append(tuple(map(tuple, table)))
        tables = tuple(tables)
        if any(any(value < 0 for row in table for value in row)
               or tuple(map(sum, table)) != self.row_sums
               or tuple(map(sum, zip(*table))) != self.column_sums
               for table in tables):
            raise RuntimeError("SciPy returned a table violating the fixed margins")
        return tables
