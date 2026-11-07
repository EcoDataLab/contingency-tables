"""Independent score identity, discrete propriety, and retained-panel guards."""
from copy import deepcopy
from fractions import Fraction
import json
import unittest

from experiments import commuting_interval_score as scoring


class CommutingIntervalScoreTests(unittest.TestCase):
    def test_score_matches_independent_pair_of_quantile_losses(self):
        # 2/alpha times the sum of pinball losses at alpha/2 and 1-alpha/2.
        # Covers both tails, exact endpoint hits, and singleton intervals.
        for alpha in (Fraction(1, 20), Fraction(1, 5), Fraction(1, 2)):
            for lower in range(5):
                for upper in range(lower, 7):
                    for observed in range(10):
                        losses = []
                        for quantile, endpoint in ((alpha / 2, lower), (1 - alpha / 2, upper)):
                            residual = observed - endpoint
                            losses.append(residual * (quantile - int(residual < 0)))
                        expected = 2 * sum(losses) / alpha
                        actual = scoring.interval_score(lower, upper, observed, alpha)
                        self.assertEqual(Fraction(actual["interval_score_jobs_exact"]), expected)
        self.assertEqual(scoring.interval_score(3, 7, 3)["interval_score_jobs"], 4)
        self.assertEqual(scoring.interval_score(3, 7, 7)["interval_score_jobs"], 4)
        self.assertEqual(scoring.interval_score(3, 7, 8)["interval_score_jobs"], 44)

    def test_exact_discrete_quantiles_minimize_expected_score(self):
        # Independent finite-support laws include an atom exactly at a tail.
        # Quantiles need not be unique, hence proper rather than strictly proper.
        for probabilities in ((Fraction(1, 40), Fraction(38, 40), Fraction(1, 40)),
                              (Fraction(1, 2), Fraction(1, 4), Fraction(1, 4)),
                              (Fraction(1, 3),) * 3):
            support = (0, 3, 8)
            cumulative = [sum(probabilities[:i + 1]) for i in range(3)]
            lower = next(x for x, cdf in zip(support, cumulative) if cdf >= scoring.ALPHA / 2)
            upper = next(x for x, cdf in zip(support, cumulative) if cdf >= 1 - scoring.ALPHA / 2)
            def expected(lo, hi):
                return sum(p * Fraction(scoring.interval_score(lo, hi, x)["interval_score_jobs_exact"])
                           for p, x in zip(probabilities, support))
            optimum = expected(lower, upper)
            self.assertTrue(all(optimum <= expected(lo, hi)
                                for lo in range(10) for hi in range(lo, 10)))

    def test_invalid_score_arguments_fail(self):
        for arguments in ((7, 3, 4), (True, 3, 4), (1, 3, -1), (1.0, 3, 4)):
            with self.assertRaises(ValueError):
                scoring.interval_score(*arguments)
        for alpha in (Fraction(0), Fraction(1), Fraction(-1), 0.05):
            with self.assertRaises(ValueError):
                scoring.interval_score(1, 3, 4, alpha)

    def test_report_scores_and_means_recomputed_without_scoring_function(self):
        source = json.loads(scoring.DEFAULT_INPUT.read_text())
        result = scoring.build_report()
        self.assertEqual(result["included_cases"], 100)
        self.assertEqual(result["verification"]["endpoints_checked"], 400)
        for law in scoring.backtest.LAWS:
            oracle = []
            normalized = []
            for original, scored in zip(source["cases"], result["cases"]):
                primary = original["laws"][law]["cells_row_major"][0]
                lo, hi = primary["interval"]
                y = primary["published_count"]
                # Distance from a closed interval gives an independent formula.
                distance = min(abs(y - lo), abs(y - hi)) if not lo <= y <= hi else 0
                expected = hi - lo + 40 * distance
                oracle.append(expected)
                normalized.append(Fraction(expected, original["case_jobs"]))
                self.assertEqual(Fraction(scored["laws"][law]["interval_score_jobs_exact"]), expected)
            summary = result["summary"][law]
            self.assertEqual(Fraction(summary["mean_interval_score_jobs_exact"]), Fraction(sum(oracle), 100))
            self.assertEqual(Fraction(summary["mean_score_fraction_of_case_total_exact"]), sum(normalized) / 100)
        json.dumps(result, allow_nan=False)

    def test_retained_metadata_endpoints_and_observation_corruption_rejected(self):
        source = json.loads(scoring.DEFAULT_INPUT.read_text())
        for key, value in (("nominal_model_interval_mass", "9/10"),
                           ("tail_probabilities", ["1/20", "19/20"]),
                           ("protocol_sha256", "0" * 64)):
            altered = deepcopy(source)
            altered[key] = value
            with self.assertRaises(ValueError):
                scoring.validate_retained_panel(altered)
        for field in ("published_count", "interval"):
            altered = deepcopy(source)
            primary = altered["cases"][0]["laws"][scoring.backtest.LAWS[0]]["cells_row_major"][0]
            if field == "interval":
                primary[field][0] += 1
            else:
                primary[field] += 1
            with self.assertRaises(ValueError):
                scoring.validate_retained_panel(altered)


if __name__ == "__main__":
    unittest.main()
