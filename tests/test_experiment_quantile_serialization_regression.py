"""Scientific report regressions derived from exact tiny algebra and native R."""

from fractions import Fraction
from math import comb
import shutil
import unittest
from unittest.mock import patch

from experiments import commuting_backtest as backtest
from experiments import worker_library_benchmarks as benchmark


class WorkerQuantileRegressionTests(unittest.TestCase):
    def test_upper_quantile_exact_cdf_tie_and_neighboring_totals(self):
        # With two draws and three successes P(X=2)=3/comb(N,2).
        # At N=16 this is exactly 1/40, so the least 39/40 quantile is 1.
        # N=15 lies below the threshold; N=17 lies above it.
        for total, expected_upper in ((15, 2), (16, 1), (17, 1)):
            with self.subTest(total=total):
                prediction = backtest.predict_from_margins((2, total - 2), (3, total - 3))
                actual = prediction["ordinary_conditional_worker"]
                self.assertEqual(actual["interval"][1], expected_upper)
                self.assertEqual(actual["numerical_evidence"]["quantile_method"],
                                 "exact_integer_combinatorial_cdf")

    def test_small_quantiles_against_integer_combinatorial_cdf(self):
        # Derive the target from integer event counts, avoiding rounded PMFs.
        for total in (0, 1, 16, 21, 32):
            for draws in range(total + 1):
                for successes in range(total + 1):
                    rows, columns = (draws, total - draws), (successes, total - successes)
                    lower = max(0, draws + successes - total)
                    upper = min(draws, successes)
                    denominator = comb(total, draws)
                    for p in (Fraction(1, 40), Fraction(39, 40)):
                        cumulative = 0
                        for x in range(lower, upper + 1):
                            cumulative += comb(successes, x) * comb(total - successes, draws - x)
                            if cumulative * p.denominator >= p.numerator * denominator:
                                expected = x
                                break
                        lo, probabilities, *_ = backtest.worker_distribution(rows, columns)
                        self.assertEqual(backtest.worker_quantile(rows, columns, lo, probabilities, p), expected)

    def test_larger_domain_keeps_explicit_numerical_path(self):
        total = backtest.EXACT_QUANTILE_MAX_TOTAL + 1
        with patch.object(backtest, "numerical_quantile", return_value=0) as numeric:
            prediction = backtest.predict_from_margins((0, total), (0, total))
        self.assertEqual(numeric.call_count, 2)
        self.assertEqual(prediction["ordinary_conditional_worker"]["numerical_evidence"]["quantile_method"],
                         "binary64_full_support_cdf")


@unittest.skipUnless(shutil.which("Rscript"), "optional native R runtime unavailable")
class RIntegerSerializationRegressionTests(unittest.TestCase):
    def test_deterministic_native_observations_preserve_supported_integers(self):
        # These values are printed in scientific notation by R's default paste,
        # which cannot be parsed by Python int. No large sampling benchmark:
        # each case has one deterministic table and one measured output.
        cases = (
            benchmark.Case("metric_100000", "synthetic", (100000, 0), (0, 100000), 1),
            benchmark.Case("first_100000", "synthetic", (100000, 0), (100000, 0), 1),
            benchmark.Case("metric_supported_max", "synthetic", (0,) * 6 + (1000000,),
                           (1000000, 0, 0, 0, 0), 1),
        )
        for case in cases:
            with self.subTest(case=case.name):
                benchmark.validate_configuration(case, 0, 1)
                self.assertIsNone(benchmark.skip_reason(case, "r_patefield", 0))
                reference, probabilities = benchmark.exact_reference(case)
                result = benchmark.r_method(case, 0, 1, 1, shutil.which("Rscript"),
                                            reference, probabilities)
                self.assertEqual(result["status"], "completed")
                for name in ("metric", "first_cell"):
                    summary = result["summary"][name]
                    self.assertEqual(summary["sample_count"], 1)
                    self.assertEqual(summary["empirical_mean"], float(Fraction(reference[name + "_mean"])))


if __name__ == "__main__":
    unittest.main()
