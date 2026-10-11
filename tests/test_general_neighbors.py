"""Cross-check exact aggregate ranks against the existing physical graph."""

from collections import Counter
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

from contingency115.ideal_chain import PhysicalState, build_rescaled_ideal_chain
from contingency115.tables import ComputationBudgetExceeded, TableProblem
from contingency115.general_neighbors import BalancedNeighborCatalog

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("general_trace_check", ROOT / "experiments/general_defect_trace.py")
experiment = importlib.util.module_from_spec(spec)
spec.loader.exec_module(experiment)


class Ranks:
    def __init__(self, rank):
        self.rank, self.stops = rank, []

    def randrange(self, stop):
        self.stops.append(stop)
        return self.rank


class GeneralNeighborsTests(unittest.TestCase):
    def test_complete_ranks_match_independent_families_and_actual_graph(self):
        seen = set()
        boundary_x = boundary_q = zero_row_slack = zero_col_slack = weighted = False
        cases = experiment.CASES + (((4, 4, 1), (6, 3), 4, 1),
                                    ((6, 3), (4, 4, 1), 4, 1),
                                    ((2, 0, 0), (2, 0, 0), 2, 1))
        for rows, columns, cutoff, padding in cases:
            chain = build_rescaled_ideal_chain(TableProblem(rows, columns), U=cutoff, L=padding)
            lookup = {state: i for i, state in enumerate(chain.states)}
            weighted |= len(set(chain.completion_counts)) > 1
            for index, state in enumerate(chain.states):
                if not state.balanced:
                    continue
                catalog = BalancedNeighborCatalog.from_problem(chain.problem, state, U=cutoff, L=padding,
                                                               large_capacity=chain.large_capacity)
                self.assertEqual(catalog.cells, chain.small_cells)
                record = experiment.balanced_families(chain, index, lookup)
                self.assertEqual(catalog.counts, record["closed_form_N0_to_N4"])
                transposed_values = tuple(catalog.values[catalog.locations[j, i]]
                                          for i in range(len(columns))
                                          for j in (range(len(rows)) if columns[i] < cutoff else
                                                    tuple(k for k, value in enumerate(rows) if value < cutoff)))
                transposed = BalancedNeighborCatalog(columns, rows,
                                                       PhysicalState(transposed_values, transposed_values),
                                                       U=cutoff, L=padding)
                self.assertEqual(transposed.counts, (catalog.counts[0], catalog.counts[1],
                                                     catalog.counts[3], catalog.counts[2], catalog.counts[4]))
                zero_row_slack |= bool(record["zero_large_row_slacks"])
                zero_col_slack |= bool(record["zero_large_column_slacks"])
                expected = {chain.states[j] for j in chain.neighbors[index]}
                generated = []
                for rank in range(catalog.degree):
                    target = catalog.unrank(rank)
                    self.assertEqual(catalog.rank(target), rank)
                    generated.append(target)
                    self.assertIsNotNone(target.defect_labels())
                    self.assertTrue(all(0 <= value <= cutoff for value in target.row_view + target.column_view))
                    boundary_x |= cutoff in target.row_view
                    boundary_q |= cutoff in target.column_view
                self.assertEqual(set(generated), expected)
                self.assertEqual(len(generated), len(expected))  # no multiplicity
                seen |= {family for family, count in enumerate(catalog.counts) if count}
        self.assertEqual(seen, set(range(5)))
        self.assertTrue(boundary_x and boundary_q)
        self.assertTrue(zero_row_slack and zero_col_slack)
        self.assertTrue(weighted)

    def test_uniform_geometry_sampler_has_one_exact_rank_draw(self):
        chain = build_rescaled_ideal_chain(TableProblem((4, 4, 1), (4, 4, 1)), U=4, L=1)
        state = next(state for state in chain.states if state.balanced and any(state.row_view))
        catalog = BalancedNeighborCatalog.from_problem(chain.problem, state, U=4, L=1)
        counts = Counter()
        for rank in range(catalog.degree):
            rng = Ranks(rank)
            counts[catalog.sample(rng)] += 1
            self.assertEqual(rng.stops, [catalog.degree])
        self.assertEqual(set(counts.values()), {1})
        # Sampling geometry uses no completion count even when weights vary.
        with patch("contingency115.tables.ExactTableSampler", side_effect=AssertionError("oracle forbidden")), \
             patch("contingency115.ideal_chain.build_rescaled_ideal_chain", side_effect=AssertionError("oracle forbidden")):
            rebuilt = BalancedNeighborCatalog.from_problem(chain.problem, state, U=4, L=1)
            self.assertEqual(rebuilt.sample(Ranks(0)), catalog.unrank(0))

    def test_quadratic_neighbor_degree_uses_linear_catalog_storage(self):
        # One small row and column; the crossing has 10000-1 inverse labels.
        rows = (100,) * 99 + (1,)
        columns = rows
        cells = tuple((i, j) for i in range(100) for j in (range(100) if i == 99 else (99,)))
        values = tuple(int((i, j) == (99, 99)) for i, j in cells)
        catalog = BalancedNeighborCatalog(rows, columns, PhysicalState(values, values), U=100)
        self.assertEqual(catalog.p, 199)
        self.assertEqual(catalog.counts, (9999, 9801, 0, 0, 0))
        self.assertEqual(catalog.degree, 19800)
        self.assertEqual(len(catalog.origins), 1)
        self.assertEqual(len(catalog.sl_active) + len(catalog.ls_active), 198)
        for rank in (0, 9998, 9999, 19799):
            self.assertEqual(catalog.rank(catalog.unrank(rank)), rank)
        self.assertIs(catalog.rows, rows)  # immutable input tuples are shared

    def test_empty_catalog_and_malformed_scope_are_explicit(self):
        empty = BalancedNeighborCatalog((2, 2), (2, 2), PhysicalState((), ()), U=2)
        self.assertEqual((empty.p, empty.degree, empty.counts), (0, 0, (0, 0, 0, 0, 0)))
        with self.assertRaises(ValueError):
            empty.sample(Ranks(0))
        with self.assertRaises(IndexError):
            empty.unrank(0)
        for problem in (TableProblem((2, 2), (2, 2), structural_zeros=[(0, 0)]),
                        TableProblem((2, 2), (2, 2), lower_bounds=((1, 0), (0, 0)))):
            with self.assertRaises(ValueError):
                BalancedNeighborCatalog.from_problem(problem, PhysicalState((1, 1, 1, 1), (1, 1, 1, 1)), U=3)
        for rows, columns, state in [((1,), (1, 0), PhysicalState((1, 0), (1, 0))),
                                      ((2, 2), (2, 1), PhysicalState((1, 1, 1, 1), (1, 1, 1, 1))),
                                      ((1, 1), (1, 1), PhysicalState((2, 0, 0, 0), (2, 0, 0, 0))),
                                      ((1, 1), (1, 1), PhysicalState((1, 0, 0, 1), (0, 1, 1, 0)))]:
            with self.assertRaises(ValueError):
                BalancedNeighborCatalog(rows, columns, state, U=3)
        with self.assertRaises(ComputationBudgetExceeded):
            BalancedNeighborCatalog((1, 1), (1, 1), PhysicalState((1, 0, 0, 1), (1, 0, 0, 1)),
                                    U=3, max_small_cells=3)

    def test_invalid_ranks_targets_and_source_capacity(self):
        chain = build_rescaled_ideal_chain(TableProblem((4, 4, 1), (4, 4, 1)), U=4, L=1)
        state = next(state for state in chain.states if state.balanced)
        catalog = BalancedNeighborCatalog.from_problem(chain.problem, state, U=4)
        for rank in (-1, True, 1.5, catalog.degree):
            with self.assertRaises((TypeError, ValueError, IndexError)):
                catalog.unrank(rank)
        with self.assertRaises(ValueError):
            catalog.rank(state)
        valid = catalog.unrank(0)
        bad = PhysicalState(tuple(True if i == 0 else value for i, value in enumerate(valid.row_view)), valid.column_view)
        with self.assertRaises(TypeError):
            catalog.rank(bad)
        with self.assertRaises(ValueError):
            BalancedNeighborCatalog.from_problem(chain.problem, state, U=4, large_capacity=1)

    def test_profile_snapshot_and_both_view_integer_validation(self):
        row_view = [1, 0, 0, 1]
        column_view = [1, 0, 0, 1]
        catalog = BalancedNeighborCatalog((1, 1), (1, 1),
                                           PhysicalState(row_view, column_view), U=2)
        before = tuple(catalog.unrank(rank) for rank in range(catalog.degree))
        row_view[:] = [0, 0, 0, 0]
        column_view[:] = [0, 0, 0, 0]
        self.assertEqual(catalog.state, PhysicalState((1, 0, 0, 1), (1, 0, 0, 1)))
        self.assertIsInstance(catalog.state.row_view, tuple)
        self.assertIsInstance(catalog.state.column_view, tuple)
        self.assertEqual(tuple(catalog.unrank(rank) for rank in range(catalog.degree)), before)
        for rank, target in enumerate(before):
            self.assertEqual(catalog.rank(target), rank)
            self.assertTrue(all(value >= 0 for value in target.row_view + target.column_view))
        for column_view in ((True, False, False, True), (1.0, 0.0, 0.0, 1.0)):
            with self.assertRaises(TypeError):
                BalancedNeighborCatalog((1, 1), (1, 1),
                                          PhysicalState((1, 0, 0, 1), column_view), U=2)


if __name__ == "__main__":
    unittest.main()
