"""Law, leakage, provenance, and numerical checks for the public hold-out panel."""
from fractions import Fraction
import gzip
import hashlib
import json
import math
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from experiments import commuting_backtest as backtest


class PublicCommutingBacktestTests(unittest.TestCase):
    def test_every_small_worker_law_against_independent_exact_combinatorics(self):
        evidence = backtest.numerical_crosscheck(12)
        self.assertEqual(evidence["margin_cases"], sum((n + 1)**2 for n in range(13)))
        self.assertEqual(evidence["central_interval_endpoint_mismatches"], 0)
        self.assertLess(evidence["maximum_probability_absolute_error"], 2e-15)

    def test_uniform_quantiles_and_moments_against_enumerated_integer_support(self):
        for lower in range(5):
            for size in range(1, 30):
                upper = lower + size - 1
                values = range(lower, upper + 1)
                mean = sum(values, Fraction(0)) / size
                variance = sum((x - mean)**2 for x in values) / size
                self.assertEqual(mean, Fraction(lower + upper, 2))
                self.assertEqual(variance, Fraction(size * size - 1, 12))
                for p in (backtest.TAIL, Fraction(1, 2), 1 - backtest.TAIL, Fraction(1)):
                    expected = next(x for i, x in enumerate(values)
                                    if Fraction(i + 1, size) >= p)
                    self.assertEqual(backtest.uniform_quantile(lower, upper, p), expected)

    def test_worker_large_symmetric_support_mean_and_endpoint_symmetry(self):
        lower, probabilities, mean, variance, evidence = backtest.worker_distribution(
            (100_000, 100_000), (100_000, 100_000))
        self.assertEqual(mean, 50_000)
        self.assertGreater(variance, 0)
        lo = backtest.numerical_quantile(lower, probabilities, backtest.TAIL)
        hi = backtest.numerical_quantile(lower, probabilities, 1 - backtest.TAIL)
        self.assertEqual(lo + hi, 100_000)
        self.assertGreater(evidence["zero_relative_weights_due_to_underflow"], 0)
        self.assertLess(evidence["normalization_residual"], 2e-15)
        self.assertLess(evidence["mean_error_against_exact_formula"], 1e-8)
        self.assertLess(evidence["variance_relative_error_against_exact_formula"], 1e-10)

    def test_joint_changes_scoring_but_cannot_change_margin_prediction(self):
        rows = columns = (10, 10)
        prediction = backtest.predict_from_margins(rows, columns)
        case = backtest.MarginCase("fixture", ("44001", "44003"),
                                   ("44001", "44003"), rows, columns)
        first = backtest.score_case(case, prediction, ((4, 6), (6, 4)))
        second = backtest.score_case(case, prediction, ((8, 2), (2, 8)))
        for law in backtest.LAWS:
            left = first["laws"][law]["cells_row_major"][0]
            right = second["laws"][law]["cells_row_major"][0]
            self.assertEqual(left["mean_exact"], right["mean_exact"])
            self.assertEqual(left["interval"], right["interval"])
            self.assertNotEqual(left["signed_error"], right["signed_error"])
            self.assertEqual(first["laws"][law]["intercounty_jobs"]["interval"],
                             second["laws"][law]["intercounty_jobs"]["interval"])

    def test_invalid_or_over_budget_margins_fail_without_partial_result(self):
        for rows, columns in [((1, 2), (2, 2)), ((-1, 1), (0, 0)),
                              ((True, 1), (1, 1)), ((1, 2, 3), (3, 3))]:
            with self.assertRaises(ValueError):
                backtest.predict_from_margins(rows, columns)
        with self.assertRaises(ValueError):
            backtest.worker_distribution((10, 10), (10, 10), max_support=10)
        deterministic = backtest.predict_from_margins((0, 10), (4, 6))
        for law in backtest.LAWS:
            self.assertEqual(deterministic[law]["interval"], (0, 0))

    def test_public_snapshot_is_complete_pinned_and_exhaustively_selected(self):
        joint, manifest = backtest.load_snapshot()
        cases, held_out, excluded = backtest.case_frame(joint)
        self.assertEqual(len(joint), 25)
        self.assertEqual(len(cases) + len(excluded), 100)
        self.assertEqual(len(cases), len(held_out))
        self.assertEqual(sum(joint.values()), manifest["aggregation"]["published_jobs"])
        self.assertTrue(manifest["official_checksum_verified"])
        self.assertEqual(manifest["protocol_sha256"], hashlib.sha256(
            (backtest.DATA / "protocol.json").read_bytes()).hexdigest())
        self.assertEqual([case.name for case in cases], sorted(case.name for case in cases))

    def test_snapshot_corruption_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp)
            for name in ("ri-2023-county-od.csv", "source-manifest.json", "protocol.json",
                         "version.txt", "census-checksum.txt"):
                (target / name).write_bytes((backtest.DATA / name).read_bytes())
            with (target / "ri-2023-county-od.csv").open("ab") as file:
                file.write(b"corruption\n")
            with patch.object(backtest, "DATA", target):
                with self.assertRaisesRegex(ValueError, "integrity"):
                    backtest.load_snapshot()

    def test_source_aggregation_orientation_and_zero_completion(self):
        header = "w_geocode,h_geocode,S000,SA01,SA02,SA03,SE01,SE02,SE03,SI01,SI02,SI03,createdate\n"
        data = header + "440030001001000,440010001001000,7,0,0,0,0,0,0,0,0,0,20251201\n"
        data += "440030001001001,440010001001001,3,0,0,0,0,0,0,0,0,0,20251201\n"
        joint, summary = backtest.aggregate_source(gzip.compress(data.encode()))
        self.assertEqual(joint["44001", "44003"], 10)
        self.assertEqual(joint["44003", "44001"], 0)
        self.assertEqual(summary["published_jobs"], 10)
        self.assertEqual(summary["source_records"], 2)
        with self.assertRaisesRegex(ValueError, "unexpected county"):
            backtest.aggregate_source(gzip.compress(data.replace("440030", "250010").encode()))

    def test_official_checksum_match_must_be_unambiguous(self):
        name = backtest.SOURCE_URL.rsplit("/", 1)[1].removesuffix(".gz")
        entry = "a" * 64 + "  od/" + name + "\n"
        self.assertEqual(backtest.census_checksum(entry.encode()), "a" * 64)
        for data in (b"", (entry + entry).encode()):
            with self.assertRaises(ValueError):
                backtest.census_checksum(data)

    def test_report_denominators_distinguish_repeated_cells_and_fixed_metric(self):
        report = backtest.build_report()
        self.assertEqual(report["candidate_cases"], 100)
        self.assertTrue(report["joint_hidden_during_prediction"])
        self.assertTrue(report["same_margin_fiber_for_both_laws"])
        self.assertEqual(report["included_cases"], 100)
        self.assertEqual(report["excluded_cases"], [])
        self.assertEqual(report["metric_identified_by_margins_cases"], 30)
        for law in backtest.LAWS:
            summaries = report["summary"][law]
            primary = summaries["primary_fips_first_cell"]
            cells = summaries["all_cells_repeated_case_indicators"]
            metric = summaries["intercounty_metric_not_identified_by_margins"]
            self.assertEqual(primary["denominator"], 100)
            self.assertEqual(cells["denominator"], 400)
            self.assertEqual(cells["covered"], 4 * primary["covered"])
            self.assertEqual(metric["denominator"], 70)
            self.assertGreaterEqual(primary["minimum_interval_model_mass"], 0.95 - 2e-15)
        json.dumps(report, allow_nan=False)


if __name__ == "__main__":
    unittest.main()
