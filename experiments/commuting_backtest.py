"""Public LODES hold-out check of two laws on identical 2x2 margin fibers.

Default execution is offline and uses the small, checksum-pinned county table.
--verify-source downloads only the fixed public Census inputs and verifies that
they reproduce that table. There is no fitting, trajectory sampling, private
input, full-fiber enumeration, or optional numerical-library dependency.
"""
from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from datetime import datetime, timezone
from fractions import Fraction
import gzip
import hashlib
import io
from itertools import combinations
import json
import math
from pathlib import Path
import platform
import time
import urllib.request


ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data/public-commuting"
COUNTIES = ("44001", "44003", "44005", "44007", "44009")
SOURCE_URL = "https://lehd.ces.census.gov/data/lodes/LODES8/ri/od/ri_od_main_JT00_2023.csv.gz"
VERSION_URL = "https://lehd.ces.census.gov/data/lodes/LODES8/ri/version.txt"
CHECKSUM_URL = "https://lehd.ces.census.gov/data/lodes/LODES8/ri/lodes_ri.sha256sum"
TECHDOC_URL = "https://lehd.ces.census.gov/doc/help/onthemap/LODESTechDoc.pdf"
MAX_DOWNLOAD_BYTES = 8_000_000
MAX_UNCOMPRESSED_BYTES = 150_000_000
MAX_SOURCE_RECORDS = 1_000_000
MAX_SUPPORT = 1_000_000
TAIL = Fraction(1, 40)
LAWS = ("uniform_aggregate_tables", "ordinary_conditional_worker")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fetch_public(url: str, limit: int = MAX_DOWNLOAD_BYTES) -> tuple[bytes, dict]:
    """Bounded acquisition from a fixed allowlist; do not save response cookies."""
    if url not in (SOURCE_URL, VERSION_URL, CHECKSUM_URL, TECHDOC_URL):
        raise ValueError("only the fixed public Census inputs may be downloaded")
    with urllib.request.urlopen(url, timeout=45) as response:
        if response.geturl() != url:
            raise ValueError("unexpected source redirect")
        data = response.read(limit + 1)
        if len(data) > limit:
            raise ValueError("public input exceeds the acquisition budget")
        metadata = {
            "url": url,
            "accessed_utc": datetime.now(timezone.utc).isoformat(),
            "last_modified": response.headers.get("Last-Modified"),
            "bytes": len(data),
            "sha256": sha256(data),
        }
    return data, metadata


def census_checksum(checksums: bytes) -> str:
    # Census publishes checksums of the decompressed .csv, not the .csv.gz.
    filename = SOURCE_URL.rsplit("/", 1)[1].removesuffix(".gz")
    matches = []
    for line in checksums.decode("utf-8").splitlines():
        fields = line.split()
        if len(fields) == 2 and fields[1].lstrip("*").rsplit("/", 1)[-1] == filename:
            matches.append(fields[0])
    if (len(matches) != 1 or len(matches[0]) != 64
            or any(c not in "0123456789abcdef" for c in matches[0])):
        raise ValueError("source must have one unambiguous Census SHA256 entry")
    return matches[0]


def aggregate_source(compressed: bytes) -> tuple[dict[tuple[str, str], int], dict]:
    """Read the full selected intrastate file; counties use 2020 block prefixes."""
    joint = {(home, work): 0 for home in COUNTIES for work in COUNTIES}
    count = total = 0
    createdates = set()
    with gzip.GzipFile(fileobj=io.BytesIO(compressed)) as raw:
        with io.TextIOWrapper(raw, encoding="utf-8", newline="") as source:
            reader = csv.DictReader(source)
            if reader.fieldnames != ["w_geocode", "h_geocode", "S000", "SA01", "SA02",
                                     "SA03", "SE01", "SE02", "SE03", "SI01",
                                     "SI02", "SI03", "createdate"]:
                raise ValueError("unexpected public OD schema")
            for row in reader:
                count += 1
                if count > MAX_SOURCE_RECORDS:
                    raise ValueError("source exceeds record budget")
                codes = row["h_geocode"], row["w_geocode"]
                if any(len(code) != 15 or not code.isascii() or not code.isdigit()
                       for code in codes):
                    raise ValueError("invalid published block identifier")
                key = codes[0][:5], codes[1][:5]
                if key not in joint:
                    raise ValueError("unexpected county in the selected intrastate file")
                value = row["S000"]
                if not value.isascii() or not value.isdigit():
                    raise ValueError("published S000 must be a nonnegative integer")
                jobs = int(value)
                joint[key] += jobs
                total += jobs
                createdates.add(row["createdate"])
    if count == 0 or total == 0:
        raise ValueError("empty public source")
    return joint, {"source_records": count, "published_jobs": total,
                   "createdates": sorted(createdates), "county_cells": len(joint)}


def subset_bytes(joint: dict[tuple[str, str], int]) -> bytes:
    output = io.StringIO(newline="")
    writer = csv.writer(output, lineterminator="\n")
    writer.writerow(("h_county", "w_county", "S000"))
    for home in COUNTIES:
        for work in COUNTIES:
            writer.writerow((home, work, joint[home, work]))
    return output.getvalue().encode("utf-8")


def acquire_snapshot() -> tuple[bytes, dict, bytes, bytes]:
    """Acquire before scoring; callers decide where to preserve the small result."""
    checksums, checksum_meta = fetch_public(CHECKSUM_URL)
    version, version_meta = fetch_public(VERSION_URL)
    compressed, source_meta = fetch_public(SOURCE_URL)
    expected = census_checksum(checksums)
    with gzip.GzipFile(fileobj=io.BytesIO(compressed)) as raw:
        uncompressed = raw.read(MAX_UNCOMPRESSED_BYTES + 1)
    if len(uncompressed) > MAX_UNCOMPRESSED_BYTES:
        raise ValueError("decompressed source exceeds acquisition budget")
    if sha256(uncompressed) != expected:
        raise ValueError("download differs from the Census checksum")
    source_meta["uncompressed_csv_sha256"] = expected
    source_meta["uncompressed_csv_bytes"] = len(uncompressed)
    del uncompressed
    joint, totals = aggregate_source(compressed)
    subset = subset_bytes(joint)
    entry = f"{expected}  {SOURCE_URL.rsplit('/', 1)[1].removesuffix('.gz')}\n".encode()
    manifest = {
        "schema_version": 1,
        "citation": "U.S. Census Bureau, ri_od_main_JT00_2023, LEHD Origin-Destination Employment Statistics, format 8.4, data vintage 20251202_1657.",
        "source": source_meta,
        "official_checksum_verified": True,
        "official_checksum_scope": "decompressed CSV bytes; the compressed download SHA256 is recorded separately",
        "official_checksum_file": checksum_meta,
        "official_checksum_entry_sha256": sha256(entry),
        "version_file": version_meta,
        "version_text": version.decode("utf-8"),
        "documentation_url": TECHDOC_URL,
        "protocol_sha256": sha256((DATA / "protocol.json").read_bytes()),
        "subset": {"path": "data/public-commuting/ri-2023-county-od.csv",
                   "sha256": sha256(subset), "bytes": len(subset),
                   "orientation": "rows = home county; columns = workplace county"},
        "aggregation": totals,
        "data_status": "Publicly released Census counts after processing and disclosure avoidance. Validation observations, not confidential person-level ground truth.",
        "retention": "Only the 25-cell aggregation, selected checksum entry, exact version text, protocol, and manifest are retained; the block-level download is not vendored.",
    }
    return subset, manifest, version, entry


def load_snapshot() -> tuple[dict[tuple[str, str], int], dict]:
    manifest = json.loads((DATA / "source-manifest.json").read_text())
    subset = (DATA / "ri-2023-county-od.csv").read_bytes()
    integrity = ((subset, manifest["subset"]["sha256"]),
                 ((DATA / "protocol.json").read_bytes(), manifest["protocol_sha256"]),
                 ((DATA / "version.txt").read_bytes(), manifest["version_file"]["sha256"]),
                 ((DATA / "census-checksum.txt").read_bytes(),
                  manifest["official_checksum_entry_sha256"]))
    if any(sha256(data) != expected for data, expected in integrity):
        raise ValueError("snapshot integrity check failed")
    joint = {}
    reader = csv.DictReader(io.StringIO(subset.decode("utf-8")))
    if reader.fieldnames != ["h_county", "w_county", "S000"]:
        raise ValueError("unexpected subset schema")
    for row in reader:
        key = row["h_county"], row["w_county"]
        value = row["S000"]
        if (key in joint or any(code not in COUNTIES for code in key)
                or not value.isascii() or not value.isdigit()):
            raise ValueError("invalid or duplicated subset cell")
        joint[key] = int(value)
    if set(joint) != {(h, w) for h in COUNTIES for w in COUNTIES}:
        raise ValueError("subset must contain every county pair")
    if sum(joint.values()) != manifest["aggregation"]["published_jobs"]:
        raise ValueError("subset total differs from its manifest")
    return joint, manifest


def verify_source(manifest: dict, subset: bytes) -> dict:
    """Re-download without replacing the pinned observation or its manifest."""
    fresh, metadata, version, entry = acquire_snapshot()
    if (metadata["source"]["sha256"] != manifest["source"]["sha256"]
            or fresh != subset or version != (DATA / "version.txt").read_bytes()
            or entry != (DATA / "census-checksum.txt").read_bytes()):
        raise ValueError("public source changed; do not silently replace the backtest")
    return {"source_sha256_matches": True, "official_checksum_matches": True,
            "subset_bytes_match": True, "version_bytes_match": True,
            "accessed_utc": metadata["source"]["accessed_utc"]}


def feasible_range(rows, columns) -> tuple[int, int]:
    if len(rows) != 2 or len(columns) != 2:
        raise ValueError("the backtest requires 2x2 margins")
    if any(isinstance(v, bool) or not isinstance(v, int) or v < 0
           for v in (*rows, *columns)):
        raise ValueError("margins must be nonnegative integers")
    if sum(rows) != sum(columns):
        raise ValueError("row and column totals must match")
    return max(0, rows[0] - columns[1]), min(rows[0], columns[0])


def uniform_quantile(lower: int, upper: int, probability: Fraction) -> int:
    """Integer inverse CDF, computed exactly (least x with F(x) >= p)."""
    if not 0 < probability <= 1:
        raise ValueError("quantile probability must be in (0, 1]")
    count = upper - lower + 1
    rank = (probability.numerator * count + probability.denominator - 1) // probability.denominator
    return lower + rank - 1


def worker_distribution(rows, columns, *, max_support=MAX_SUPPORT):
    """Hypergeometric full-support binary64 recurrence, centered at its mode.

    Relative mode weight = 1 avoids factorial overflow and endpoint underflow.
    Every support point is visited. Remote weights may underflow to zero; this
    is recorded, never hidden by a convergence or tail truncation heuristic.
    This numerical routine is not a certified arbitrary-precision evaluator.
    """
    lower, upper = feasible_range(rows, columns)
    size = upper - lower + 1
    if size > max_support:
        raise ValueError("2x2 support exceeds the numerical budget")
    total, draws, successes = sum(rows), rows[0], columns[0]
    mode = min(upper, max(lower, (draws + 1) * (successes + 1) // (total + 2)))
    weights = [0.0] * size
    weights[mode - lower] = 1.0
    for x in range(mode, upper):
        ratio = ((successes - x) * (draws - x)
                 / ((x + 1) * (total - successes - draws + x + 1)))
        weights[x + 1 - lower] = weights[x - lower] * ratio
    for x in range(mode, lower, -1):
        ratio = (x * (total - successes - draws + x)
                 / ((successes - x + 1) * (draws - x + 1)))
        weights[x - 1 - lower] = weights[x - lower] * ratio
    normalizer = math.fsum(weights)
    probabilities = [value / normalizer for value in weights]
    exact_mean = Fraction(draws * successes, total) if total else Fraction(0)
    exact_variance = (Fraction(draws * successes * (total - draws) * (total - successes),
                               total * total * (total - 1)) if total > 1 else Fraction(0))
    numeric_mean = math.fsum((lower + i) * p for i, p in enumerate(probabilities))
    numeric_variance = math.fsum(((lower + i) - float(exact_mean))**2 * p
                                for i, p in enumerate(probabilities))
    evidence = {
        "support_points_visited": size, "mode": mode,
        "zero_relative_weights_due_to_underflow": sum(w == 0 for w in weights),
        "smallest_positive_relative_weight": min(w for w in weights if w > 0),
        "relative_weight_normalizer": normalizer,
        "normalization_residual": abs(math.fsum(probabilities) - 1),
        "mean_error_against_exact_formula": abs(numeric_mean - float(exact_mean)),
        "variance_relative_error_against_exact_formula": (
            abs(numeric_variance - float(exact_variance)) / float(exact_variance)
            if exact_variance else abs(numeric_variance)),
        "tail_handling": "Full support visited; no tail cutoff, Monte Carlo, or normal approximation. Binary64 underflow is recorded; rounding is not formally bounded.",
    }
    return lower, probabilities, exact_mean, exact_variance, evidence


def numerical_quantile(lower: int, probabilities: list[float], p: Fraction) -> int:
    target = float(p)
    cumulative = compensation = 0.0
    for i, probability in enumerate(probabilities):
        adjusted = probability - compensation
        updated = cumulative + adjusted
        compensation = (updated - cumulative) - adjusted
        cumulative = updated
        if cumulative >= target:
            return lower + i
    # p=1 can exceed a rounded normalized sum by one ulp.
    if p == 1:
        return lower + len(probabilities) - 1
    raise ArithmeticError("normalized CDF did not reach the requested quantile")


def predict_from_margins(rows: tuple[int, int], columns: tuple[int, int]) -> dict:
    """The prediction API has no joint-table or published-cell argument."""
    lower, upper = feasible_range(rows, columns)
    size = upper - lower + 1
    if size > MAX_SUPPORT:
        raise ValueError("2x2 support exceeds the numerical budget")
    a = uniform_quantile(lower, upper, TAIL)
    b = uniform_quantile(lower, upper, 1 - TAIL)
    uniform = {"mean": Fraction(lower + upper, 2),
               "variance": Fraction(size * size - 1, 12),
               "interval": (a, b), "interval_model_mass": (b - a + 1) / size}
    lo, probabilities, mean, variance, evidence = worker_distribution(rows, columns)
    a = numerical_quantile(lo, probabilities, TAIL)
    b = numerical_quantile(lo, probabilities, 1 - TAIL)
    worker = {"mean": mean, "variance": variance, "interval": (a, b),
              "interval_model_mass": math.fsum(probabilities[a - lo:b - lo + 1]),
              "numerical_evidence": evidence}
    return {"support": (lower, upper), "support_size": size,
            "uniform_aggregate_tables": uniform, "ordinary_conditional_worker": worker}


@dataclass(frozen=True)
class MarginCase:
    name: str
    home: tuple[str, str]
    work: tuple[str, str]
    rows: tuple[int, int]
    columns: tuple[int, int]


def case_frame(joint):
    """Separate margins from held-out joints before any prediction is called."""
    inputs, held_out, excluded = [], {}, []
    for home in combinations(COUNTIES, 2):
        for work in combinations(COUNTIES, 2):
            table = tuple(tuple(joint[h, w] for w in work) for h in home)
            rows = tuple(map(sum, table))
            columns = tuple(map(sum, zip(*table)))
            name = "_".join(home) + "__" + "_".join(work)
            case = MarginCase(name, home, work, rows, columns)
            if feasible_range(rows, columns)[0] == feasible_range(rows, columns)[1]:
                excluded.append({"case": name, "row_sums": rows, "column_sums": columns,
                                 "reason": "singleton feasible fiber"})
            else:
                inputs.append(case)
                held_out[name] = table
    return inputs, held_out, excluded


def score_linear(model: dict, slope: int, intercept: int, published: int, total: int) -> dict:
    mean = slope * model["mean"] + intercept
    endpoints = [slope * x + intercept for x in model["interval"]]
    interval = min(endpoints), max(endpoints)
    error = mean - published
    return {"published_count": published, "mean": float(mean), "mean_exact": str(mean),
            "signed_error": float(error), "absolute_error": float(abs(error)),
            "squared_error": float(error * error),
            "error_fraction_of_case_total": float(error / total) if total else 0,
            "interval": interval, "interval_width": interval[1] - interval[0],
            "width_fraction_of_case_total": (interval[1] - interval[0]) / total if total else 0,
            "covered": interval[0] <= published <= interval[1],
            "interval_model_mass": model["interval_model_mass"] if slope else 1.0}


def score_case(case: MarginCase, prediction: dict, table: tuple) -> dict:
    total = sum(case.rows)
    transforms = ((1, 0), (-1, case.rows[0]),
                  (-1, case.columns[0]), (1, case.rows[1] - case.columns[0]))
    coefficients = [int(h != w) for h in case.home for w in case.work]
    metric_slope = sum(c * slope for c, (slope, _) in zip(coefficients, transforms))
    metric_intercept = sum(c * offset for c, (_, offset) in zip(coefficients, transforms))
    flat = [value for row in table for value in row]
    result = {"case": case.name, "home_counties": case.home, "work_counties": case.work,
              "row_sums": case.rows, "column_sums": case.columns, "case_jobs": total,
              "held_out_published_joint": table, "feasible_x_range": prediction["support"],
              "feasible_tables": prediction["support_size"],
              "intercounty_metric_identified_by_margins": metric_slope == 0, "laws": {}}
    for law in LAWS:
        model = prediction[law]
        cells = [score_linear(model, slope, offset, value, total)
                 for (slope, offset), value in zip(transforms, flat)]
        if len({cell["covered"] for cell in cells}) != 1:
            raise AssertionError("2x2 cell coverage must agree")
        result["laws"][law] = {
            "cells_row_major": cells,
            "whole_table_covered": cells[0]["covered"],
            "intercounty_jobs": score_linear(model, metric_slope, metric_intercept,
                                             sum(c * x for c, x in zip(coefficients, flat)), total),
        }
        if "numerical_evidence" in model:
            result["laws"][law]["numerical_evidence"] = model["numerical_evidence"]
    return result


def summarize_scores(scores: list[dict]) -> dict:
    count = len(scores)
    if not count:
        return {"denominator": 0, "covered": 0, "coverage_fraction": None}
    return {
        "denominator": count, "covered": sum(s["covered"] for s in scores),
        "coverage_fraction": sum(s["covered"] for s in scores) / count,
        "mean_interval_width_jobs": math.fsum(s["interval_width"] for s in scores) / count,
        "mean_width_fraction_of_case_total": math.fsum(s["width_fraction_of_case_total"] for s in scores) / count,
        "mean_signed_error_jobs": math.fsum(s["signed_error"] for s in scores) / count,
        "mean_absolute_error_jobs": math.fsum(s["absolute_error"] for s in scores) / count,
        "root_mean_squared_error_jobs": math.sqrt(math.fsum(s["squared_error"] for s in scores) / count),
        "mean_signed_error_fraction_of_case_total": math.fsum(s["error_fraction_of_case_total"] for s in scores) / count,
        "mean_absolute_error_fraction_of_case_total": math.fsum(abs(s["error_fraction_of_case_total"]) for s in scores) / count,
        "minimum_interval_model_mass": min(s["interval_model_mass"] for s in scores),
        "maximum_interval_model_mass": max(s["interval_model_mass"] for s in scores),
    }


def numerical_crosscheck(max_total: int = 12) -> dict:
    """Independent combinatorial rational oracle on every small margin pair."""
    cases = mismatches = 0
    maximum_probability_error = 0.0
    for total in range(max_total + 1):
        for row in range(total + 1):
            for column in range(total + 1):
                lower, probabilities, _, _, _ = worker_distribution((row, total - row),
                                                                  (column, total - column))
                oracle = [Fraction(math.comb(column, x) * math.comb(total - column, row - x),
                                   math.comb(total, row))
                          for x in range(lower, lower + len(probabilities))]
                maximum_probability_error = max(maximum_probability_error,
                                                max(abs(p - float(q)) for p, q in zip(probabilities, oracle)))
                for p in (TAIL, 1 - TAIL):
                    cumulative = Fraction(0)
                    for offset, mass in enumerate(oracle):
                        cumulative += mass
                        if cumulative >= p:
                            exact_quantile = lower + offset
                            break
                    mismatches += numerical_quantile(lower, probabilities, p) != exact_quantile
                cases += 1
    if mismatches:
        raise AssertionError("worker quantiles differ from the exact small-case oracle")
    return {"oracle": "Exact rational comb(c1,x)*comb(N-c1,r1-x)/comb(N,r1)",
            "all_margins_total_at_most": max_total, "margin_cases": cases,
            "central_interval_endpoint_mismatches": mismatches,
            "maximum_probability_absolute_error": maximum_probability_error}


def scipy_panel_crosscheck(results: list[dict]) -> dict:
    """Optional independent numerical implementation; never used for fitting."""
    import scipy
    from scipy.stats import hypergeom

    mismatches = []
    maximum_mass_difference = 0.0
    for case in results:
        total, draws, successes = sum(case["row_sums"]), case["row_sums"][0], case["column_sums"][0]
        model = case["laws"]["ordinary_conditional_worker"]["cells_row_major"][0]
        lower, upper = model["interval"]
        endpoints = tuple(int(hypergeom.ppf(float(p), total, successes, draws))
                          for p in (TAIL, 1 - TAIL))
        if tuple(model["interval"]) != endpoints:
            mismatches.append(case["case"])
        mass = float(hypergeom.cdf(upper, total, successes, draws)
                     - hypergeom.cdf(lower - 1, total, successes, draws))
        maximum_mass_difference = max(maximum_mass_difference,
                                      abs(mass - model["interval_model_mass"]))
    if mismatches:
        raise AssertionError(f"worker interval endpoints differ from SciPy in {mismatches}")
    return {"library": "SciPy", "version": scipy.__version__, "case_denominator": len(results),
            "central_interval_endpoints_checked": 2 * len(results),
            "central_interval_endpoint_mismatches": len(mismatches),
            "maximum_interval_mass_absolute_difference": maximum_mass_difference,
            "method": "scipy.stats.hypergeom.ppf and cdf, using only each case's fixed margins",
            "documentation": "https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.hypergeom.html"}


def build_report(*, verify_download: bool = False, crosscheck_scipy: bool = False) -> dict:
    started = time.perf_counter()
    joint, manifest = load_snapshot()
    cases, held_out, excluded = case_frame(joint)
    del joint
    # Construct every law prediction before scoring accesses any held-out table.
    predictions = {case.name: predict_from_margins(case.rows, case.columns) for case in cases}
    prediction_seconds = time.perf_counter() - started
    results = [score_case(case, predictions[case.name], held_out[case.name]) for case in cases]
    summaries = {}
    for law in LAWS:
        all_cells = [score for case in results for score in case["laws"][law]["cells_row_major"]]
        summaries[law] = {
            "primary_fips_first_cell": summarize_scores([c["laws"][law]["cells_row_major"][0] for c in results]),
            "all_cells_repeated_case_indicators": summarize_scores(all_cells),
            "intercounty_metric_all_cases": summarize_scores([c["laws"][law]["intercounty_jobs"] for c in results]),
            "intercounty_metric_not_identified_by_margins": summarize_scores([
                c["laws"][law]["intercounty_jobs"] for c in results
                if not c["intercounty_metric_identified_by_margins"]]),
        }
    evidence = [c["laws"][LAWS[1]]["numerical_evidence"] for c in results]
    report = {
        "schema_version": 1, "experiment": "public_lodes_county_joint_holdout",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "environment": {"python": platform.python_version(), "platform": platform.platform(),
                        "optional_libraries": [], "random_draws": 0},
        "protocol_sha256": manifest["protocol_sha256"],
        "source_manifest_sha256": sha256((DATA / "source-manifest.json").read_bytes()),
        "experiment_source_sha256": sha256(Path(__file__).read_bytes()),
        "source": manifest["source"], "subset": manifest["subset"],
        "dataset": manifest["aggregation"],
        "scope": "2023 LODES main JT00 S000: jobs with both home and workplace in Rhode Island; rows=home, columns=workplace, 2020 Census county prefixes.",
        "counts_are": "Public validation observations after Census processing/disclosure avoidance; all jobs, not unique commuters or daily commute trips.",
        "candidate_cases": 100, "included_cases": len(cases), "excluded_cases": excluded,
        "metric_identified_by_margins_cases": sum(c["intercounty_metric_identified_by_margins"] for c in results),
        "nominal_model_interval_mass": "19/20", "tail_probabilities": ["1/40", "39/40"],
        "joint_hidden_during_prediction": True,
        "same_margin_fiber_for_both_laws": True,
        "prediction_seconds_including_local_source_validation": prediction_seconds,
        "numerical_validation": numerical_crosscheck(),
        "numerical_panel_evidence": {
            "total_support_points_visited": sum(e["support_points_visited"] for e in evidence),
            "largest_support": max(e["support_points_visited"] for e in evidence),
            "total_relative_weights_underflowed_to_zero": sum(e["zero_relative_weights_due_to_underflow"] for e in evidence),
            "maximum_normalization_residual": max(e["normalization_residual"] for e in evidence),
            "maximum_mean_error_against_exact_formula": max(e["mean_error_against_exact_formula"] for e in evidence),
            "maximum_variance_relative_error_against_exact_formula": max(e["variance_relative_error_against_exact_formula"] for e in evidence),
            "precision_status": "Binary64 full-support recurrence, exact analytic means, exact small-case oracle; no formal large-case rounding/tail error certificate.",
        },
        "summary": summaries,
        "coverage_interpretation": "Descriptive inclusion fraction over 100 overlapping cases from one released 5x5 joint. No independence assumption, calibration confidence interval, frequentist 95% guarantee, or application-wide validity claim.",
        "case_reuse": "County cells recur in many cases; each 2x2 has one free cell, so its four coverage indicators coincide. The 400-cell summary is not 400 independent observations.",
        "limitations": [
            "Selection is exhaustive within this one deliberately small state/year, not representative of the United States or other years.",
            "The case's margins are derived within its selected two-home/two-work-county universe, not full-state RAC/WAC margins.",
            "Neither law models geography, distance, sector, job availability interactions, or individual preferences; no fitted model is compared.",
            "Central predictive mass under an assumed law is not a confidence interval for an arbitrary fixed published table.",
            "The released OD has statistical disclosure protection and other processing uncertainty, which this margin-only experiment does not propagate.",
            "Uniform law on each 2x2 restricted table need not be the marginal of a uniform law on the full 5x5 table.",
            "No mode/distance/VMT/emissions prediction or private production application is tested.",
        ],
        "cases": results,
        "reproduce": "python3 experiments/commuting_backtest.py --output reports/commuting-backtest.json",
        "verify_public_source": "python3 experiments/commuting_backtest.py --verify-source --output /private/tmp/commuting-backtest-reverified.json",
    }
    if verify_download:
        report["live_source_verification"] = verify_source(manifest, (DATA / "ri-2023-county-od.csv").read_bytes())
    if crosscheck_scipy:
        crosscheck = scipy_panel_crosscheck(results)
        report["optional_scipy_crosscheck"] = crosscheck
        report["environment"]["optional_libraries"] = [{"name": "SciPy", "version": crosscheck["version"]}]
        report["reproduce_with_optional_crosscheck"] = (
            "python3 experiments/commuting_backtest.py --crosscheck-scipy --output reports/commuting-backtest.json")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-source", action="store_true")
    parser.add_argument("--crosscheck-scipy", action="store_true",
                        help="also check all worker interval endpoints against an installed SciPy")
    args = parser.parse_args()
    report = build_report(verify_download=args.verify_source, crosscheck_scipy=args.crosscheck_scipy)
    encoded = json.dumps(report, indent=2, sort_keys=True, allow_nan=False) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
