"""Optional real-library law, shape, RNG and ordinary-support checks."""
from collections import Counter
from fractions import Fraction
import math
import random
import unittest
from unittest.mock import patch

from contingency115.scipy_workers import ScipyWorkerSampler
from contingency115.tables import ComputationBudgetExceeded, InfeasibleTableError, TableProblem
from contingency115.workers import OrdinaryWorkerSampler
from test_workers import independent_table_law

try:
    import numpy as np
    from scipy.stats import random_table
except (ImportError, AttributeError):
    np = random_table = None


class ScipyWorkerPreflightTests(unittest.TestCase):
    def test_missing_dependency_is_explicit_and_module_import_is_optional(self):
        with patch("contingency115.scipy_workers.importlib.import_module",
                   side_effect=ModuleNotFoundError("numpy")):
            with self.assertRaisesRegex(ImportError, "optional NumPy and SciPy"):
                ScipyWorkerSampler((2,2),(2,2))

    def test_invalid_margins_budgets_and_excluded_constraints_before_import(self):
        with patch("contingency115.scipy_workers._scipy_backend",
                   side_effect=AssertionError("preflight must precede dependency loading")):
            for rows,columns in [([], [0]), ([0], []), ([True],[1]),
                                 ([1.0],[1]), ([-1],[-1])]:
                with self.subTest(rows=rows,columns=columns):
                    with self.assertRaises((ValueError,TypeError)):
                        ScipyWorkerSampler(rows,columns)
            with self.assertRaises(InfeasibleTableError):
                ScipyWorkerSampler((2,),(3,))
            with self.assertRaises(ComputationBudgetExceeded):
                ScipyWorkerSampler((2,2),(2,2),max_cells=3)
            with self.assertRaisesRegex(ValueError,"signed 64-bit"):
                ScipyWorkerSampler((2**63,),(2**63,))
            for seed in (-1,True,1.0):
                with self.assertRaises((ValueError,TypeError)):
                    ScipyWorkerSampler((2,2),(2,2),seed=seed)
            with self.assertRaisesRegex(ValueError,"not both"):
                ScipyWorkerSampler((2,2),(2,2),seed=1,rng=object())
            with self.assertRaises(TypeError):
                ScipyWorkerSampler(TableProblem((2,2),(2,2)))
            for argument in ("structural_zeros","upper_bounds","lower_bounds","activities"):
                with self.assertRaises(TypeError):
                    ScipyWorkerSampler((2,2),(2,2),**{argument:[]})


@unittest.skipIf(random_table is None,"optional SciPy random_table unavailable")
class ScipyWorkerLibraryTests(unittest.TestCase):
    def test_public_backend_pmf_matches_independent_inverse_factorial_law(self):
        for rows,columns in [((2,2),(2,2)),((2,2,2),(2,2,2)),
                             ((2,0,3),(0,2,3)),((0,0),(0,0,0))]:
            law=independent_table_law(rows,columns)
            for table,probability in law.items():
                self.assertAlmostEqual(float(random_table.pmf(table,rows,columns)),
                                       float(probability),places=12)
        law=independent_table_law((2,2),(2,2))
        self.assertEqual({t[0][0]:p for t,p in law.items()},
                         {0:Fraction(1,6),1:Fraction(2,3),2:Fraction(1,6)})

    def test_wrapper_delegates_seeded_batch_to_public_patefield_api(self):
        rows,columns=(4,3,3),(4,2,2,2)
        expected=random_table(rows,columns).rvs(size=12,method="patefield",
                 random_state=np.random.Generator(np.random.PCG64(115)))
        sampler=ScipyWorkerSampler(rows,columns,seed=115)
        self.assertEqual(sampler.samples(12),tuple(tuple(tuple(map(int,row)) for row in t)
                                                  for t in expected))
        duplicate=ScipyWorkerSampler(rows,columns,seed=115)
        duplicate.samples(12)
        self.assertEqual(sampler.samples(5),duplicate.samples(5))

    def test_actual_samples_have_nonuniform_worker_frequencies(self):
        counts=Counter(t[0][0] for t in ScipyWorkerSampler((2,2),(2,2),seed=115).samples(12000))
        for value,p in [(0,1/6),(1,2/3),(2,1/6)]:
            self.assertLess(abs(counts[value]-12000*p),7*math.sqrt(12000*p*(1-p)))
        self.assertGreater(counts[1],2*max(counts[0],counts[2]))

    def test_shapes_zero_margins_and_singleton_axes(self):
        for rows,columns in [((0,0),(0,0,0)),((0,3),(0,1,2)),
                             ((3,),(1,2)),((1,2),(3,)),((0,1,2),(2,0,1))]:
            sampler=ScipyWorkerSampler(rows,columns,seed=7)
            tables=(sampler.sample(),)+sampler.samples(7)
            for table in tables:
                self.assertEqual(tuple(map(sum,table)),rows)
                self.assertEqual(tuple(map(sum,zip(*table))),columns)
                self.assertTrue(all(type(v) is int and v>=0 for row in table for v in row))
            if sum(v>0 for v in rows)<2 or sum(v>0 for v in columns)<2:
                self.assertEqual(len(set(tables)),1)

    def test_deterministic_axes_preserve_rng_and_zero_axes_restore_shape(self):
        rng=np.random.default_rng(115)
        before=rng.bit_generator.state
        sampler=ScipyWorkerSampler((0,3),(0,1,2),rng=rng)
        self.assertEqual(sampler.samples(3),(((0,0,0),(0,1,2)),)*3)
        self.assertEqual(rng.bit_generator.state,before)
        original=ScipyWorkerSampler((0,2,0,3),(0,2,3,0),seed=115).samples(8)
        compressed=ScipyWorkerSampler((2,3),(2,3),seed=115).samples(8)
        self.assertEqual(tuple(tuple(tuple(t[i][j] for j in (1,2)) for i in (1,3))
                               for t in original),compressed)

    def test_rng_is_shared_and_budget_rejection_and_empty_batch_do_not_advance_it(self):
        rng=np.random.default_rng(115)
        sampler=ScipyWorkerSampler((2,2),(2,2),rng=rng,max_output_cells=8)
        state=rng.bit_generator.state
        self.assertEqual(sampler.samples(0),())
        with self.assertRaises(ComputationBudgetExceeded):sampler.samples(3)
        self.assertEqual(rng.bit_generator.state,state)
        sampler.samples(2)
        self.assertNotEqual(rng.bit_generator.state,state)
        with self.assertRaises(TypeError):
            ScipyWorkerSampler((2,2),(2,2),rng=random.Random(115))
        with self.assertRaises(TypeError):
            ScipyWorkerSampler((2,2),(2,2),rng=np.random.RandomState(115))

    def test_snapshots_margins_and_keeps_exact_reference_available(self):
        rows,columns=[2,2],[2,2]
        sampler=ScipyWorkerSampler(rows,columns,seed=7)
        rows[0]=columns[0]=999
        self.assertEqual(sampler.row_sums,(2,2))
        self.assertEqual(sampler.column_sums,(2,2))
        with self.assertRaises(AttributeError):sampler.row_sums=(999,999)
        self.assertIsInstance(OrdinaryWorkerSampler((2,2),(2,2)).sample(random.Random(115)),tuple)

    def test_invalid_library_outputs_raise_without_resampling(self):
        sampler=ScipyWorkerSampler((2,2),(2,2),seed=7)
        for output in (np.zeros((2,2),dtype=int), np.zeros((1,2,2),dtype=float),
                       np.array([[[-1,3],[3,-1]]]), np.zeros((1,2,2),dtype=int)):
            with self.subTest(output=output):
                with patch.object(sampler._distribution,"rvs",return_value=output) as draw:
                    with self.assertRaises(RuntimeError):sampler.sample()
                    self.assertEqual(draw.call_count,1)


if __name__=="__main__":unittest.main()
