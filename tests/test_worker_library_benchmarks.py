import importlib.util
from fractions import Fraction
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

path = Path(__file__).resolve().parents[1] / "experiments/worker_library_benchmarks.py"
spec = importlib.util.spec_from_file_location("worker_library_benchmarks", path)
b = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = b
spec.loader.exec_module(b)


class WorkerLibraryBenchmarks(unittest.TestCase):
    def test_exact_law_distinguishes_uniform_aggregate_tables(self):
        reference, probabilities = b.exact_reference(b.cases()[0])
        self.assertEqual({t[0][0]: p for t, p in probabilities.items()},
                         {0: Fraction(1, 6), 1: Fraction(2, 3), 2: Fraction(1, 6)})
        self.assertEqual(reference["first_cell_mean"], "1")
        self.assertEqual(reference["first_cell_variance"], "1/3")

    def test_nonseparable_moment_formula_matches_fiber_enumeration(self):
        case = b.cases()[1]
        reference, probabilities = b.exact_reference(case)
        q = b.coefficients(case)
        mean = sum(p*b.observations([t], q)[0][0] for t, p in probabilities.items())
        variance = sum(p*(b.observations([t], q)[0][0]-mean)**2 for t, p in probabilities.items())
        self.assertEqual(Fraction(reference["metric_mean"]), mean)
        self.assertEqual(Fraction(reference["metric_variance"]), variance)

    def test_margin_validation_checks_shape_integer_and_totals(self):
        case = b.Case("tiny", "test", (2, 2), (2, 2), 1)
        self.assertEqual(b.validate_tables([((1, 1), (1, 1))], case), [((1, 1), (1, 1))])
        for table in (((2, 1), (0, 1)), ((1.5, .5), (.5, 1.5)), ((2, 0),), ((3, -1), (-1, 3))):
            with self.assertRaises(RuntimeError):
                b.validate_tables([table], case)

    def test_work_caps_preserve_skewed_large_total_shortcut(self):
        large = b.cases()[-1]
        self.assertIsNone(b.skip_reason(large, "worker_urn", 1))
        self.assertIn("Boyett", b.skip_reason(large, "scipy_boyett", 1))
        balanced = b.Case("too_large", "test", (10**9,)*2, (10**9,)*2, 1)
        self.assertIsNotNone(b.skip_reason(balanced, "worker_urn", 1))
        self.assertIn("log-factorials", b.skip_reason(balanced, "r_patefield", 1))
        self.assertIn("log-factorials", b.skip_reason(large, "r_patefield", 1))
        overflow = b.Case("r_overflow", "test", (2**31,)*2, (2**31,)*2, 1)
        self.assertIsNotNone(b.skip_reason(overflow, "r_patefield", 1))

    def test_optional_dependencies_are_skipped_with_reasons(self):
        deps = {"scipy": {"status": "unavailable", "reason": "test SciPy absent"},
                "r": {"status": "unavailable", "reason": "test R absent"}}
        case = b.Case("tiny", "test", (2, 2), (2, 2), 4)
        with patch.object(b, "discover_dependencies", return_value=(None, None, deps)):
            report = b.run([case], warmup=0, repetitions=2, hardware={"cpu": "test"})
        methods = {m["method"]: m for m in report["cases"][0]["methods"]}
        self.assertEqual(methods["worker_urn"]["status"], "completed")
        self.assertEqual([r["seed"] for r in methods["worker_urn"]["runs"]], [b.SEED, b.SEED+1])
        for name in b.METHODS[1:]:
            self.assertEqual(methods[name]["status"], "skipped")
            self.assertIn("absent", methods[name]["reason"])
        self.assertFalse(report["finding_115_uniform_sampler_executed"])

    def test_configuration_rejects_excess_output_and_invalid_counts(self):
        for draws, warmup, repetitions in ((0, 0, 1), (1, -1, 1), (1, 0, 6)):
            with self.assertRaises(ValueError):
                b.validate_configuration(b.Case("test", "test", (2, 2), (2, 2), draws), warmup, repetitions)
        with self.assertRaises(ValueError):
            b.validate_configuration(b.Case("bad", "test", (1,), (2,), 1), 0, 1)

    def test_measured_phases_are_recorded_separately(self):
        case = b.Case("tiny", "test", (2, 2), (2, 2), 8)
        ref, probabilities = b.exact_reference(case)
        method = b.python_method(case, "worker_urn", 1, 1, 5, None, ref, probabilities)
        run = method["runs"][0]
        self.assertEqual(run["setup_plus_draw_seconds"], run["setup_seconds"]+run["draw_seconds"])
        self.assertEqual(run["setup_warmup_draw_seconds"], run["setup_plus_draw_seconds"]+run["warmup_seconds"])
        self.assertEqual(run["completed_outputs"], 8)
        self.assertTrue(run["margins_verified"])
        self.assertGreater(run["work"]["random_draws"], 0)

    def test_seed_overflow_rejected_before_dependency_discovery(self):
        selected = b.cases()
        repetitions = 5
        upper = b.R_MAX_INTEGER - 100*(len(selected)-1) - (repetitions-1)
        with patch.object(b, "discover_dependencies") as discover:
            with self.assertRaisesRegex(ValueError, "every case and repetition"):
                b.run(selected, repetitions=repetitions, seed=upper+1)
            discover.assert_not_called()

    def test_last_case_last_repetition_accepts_exact_r_seed_boundary(self):
        _, executable, _ = b.discover_dependencies()
        if executable is None:
            self.skipTest("optional Rscript unavailable")
        case = b.Case("tiny", "test", (2, 2), (2, 2), 2)
        report = b.run([case, case], warmup=0, repetitions=2,
                       seed=b.R_MAX_INTEGER-101, methods=("r_patefield",),
                       hardware={"cpu": "seed boundary regression"})
        last = report["cases"][-1]["methods"][0]
        self.assertEqual(last["status"], "completed")
        self.assertEqual(last["runs"][-1]["seed"], b.R_MAX_INTEGER)

    def test_scipy_all_small_fiber_probabilities(self):
        modules, _, _ = b.discover_dependencies()
        if modules is None:
            self.skipTest("optional SciPy not installed")
        check = b.scipy_law_check(modules)
        self.assertEqual(check["status"], "completed")
        self.assertEqual(check["cases"][0]["tables_checked"], 3)
        self.assertGreater(check["cases"][1]["tables_checked"], 3)

    def test_r_real_api_and_small_fiber_readback(self):
        _, executable, _ = b.discover_dependencies()
        if executable is None:
            self.skipTest("optional Rscript unavailable")
        case = b.Case("tiny", "exact_small_law", (2, 2), (2, 2), 8)
        reference, probabilities = b.exact_reference(case)
        result = b.r_method(case, 1, 2, 5, executable, reference, probabilities)
        self.assertEqual(result["status"], "completed")
        summary = result["summary"]
        self.assertEqual(summary["metric"]["sample_count"], 16)
        self.assertEqual(sum(t["observed_count"] for t in summary["small_fiber"]["frequency_comparison"]), 16)
        self.assertTrue(all(r["margins_verified"] for r in result["runs"]))


if __name__ == "__main__":
    unittest.main()
