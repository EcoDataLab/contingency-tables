"""Post hoc proper interval scores for the frozen public commuting panel.

Offline, standard-library-only supplement. It reads the retained report and
checks its primary quantiles against the pinned margins. It never overwrites
the original experiment, protocol, observation, or report.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

try:  # Support both repository-root CLI execution and unittest imports.
    from experiments import commuting_backtest as backtest
except ModuleNotFoundError:
    import commuting_backtest as backtest


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = ROOT / "reports/commuting-backtest.json"
ALPHA = Fraction(1, 20)
SCORE_REFERENCE = "https://sites.stat.washington.edu/people/raftery/Research/PDF/Gneiting2007jasa.pdf"


def interval_score(lower: int, upper: int, observed: int,
                   alpha: Fraction = ALPHA) -> dict:
    """Exact, negatively oriented score; endpoint hits incur zero miss penalty."""
    if any(type(x) is not int or x < 0 for x in (lower, upper, observed)):
        raise ValueError("interval endpoints and published count must be nonnegative integers")
    if lower > upper:
        raise ValueError("interval endpoints must be ordered")
    if not isinstance(alpha, Fraction) or not 0 < alpha < 1:
        raise ValueError("alpha must be an exact Fraction strictly between zero and one")
    width = upper - lower  # Count-valued intervals still use u-l, not u-l+1.
    below = max(lower - observed, 0)
    above = max(observed - upper, 0)
    lower_penalty = 2 * below / alpha
    upper_penalty = 2 * above / alpha
    score = width + lower_penalty + upper_penalty
    return {"interval_width_jobs": width,
            "miss_below_jobs": below, "miss_above_jobs": above,
            "lower_miss_penalty_jobs_exact": str(lower_penalty),
            "upper_miss_penalty_jobs_exact": str(upper_penalty),
            "interval_score_jobs_exact": str(score),
            "interval_score_jobs": float(score)}


def validate_retained_panel(report: dict) -> tuple[list[dict], dict]:
    """Reject wrong alpha semantics, altered outcomes, or altered primary bounds."""
    if (report.get("experiment") != "public_lodes_county_joint_holdout"
            or report.get("nominal_model_interval_mass") != "19/20"
            or report.get("tail_probabilities") != ["1/40", "39/40"]):
        raise ValueError("requires the frozen central 95% quantile interval contract")
    joint, manifest = backtest.load_snapshot()
    cases, held_out, excluded = backtest.case_frame(joint)
    if (report.get("protocol_sha256") != manifest["protocol_sha256"]
            or report.get("source_manifest_sha256") != backtest.sha256(
                (backtest.DATA / "source-manifest.json").read_bytes())
            or report.get("subset") != manifest["subset"]):
        raise ValueError("retained report provenance differs from the pinned public snapshot")
    records = report.get("cases", [])
    if (report.get("included_cases") != len(cases)
            or report.get("excluded_cases") != excluded
            or [r["case"] for r in records] != [c.name for c in cases]):
        raise ValueError("retained report does not match the exhaustive ordered case frame")
    # These are margin-only predictions, used only to verify existing intervals.
    predictions = {c.name: backtest.predict_from_margins(c.rows, c.columns) for c in cases}
    for case, record in zip(cases, records):
        table = [list(row) for row in held_out[case.name]]
        if (record["held_out_published_joint"] != table
                or record["row_sums"] != list(case.rows)
                or record["column_sums"] != list(case.columns)
                or record["case_jobs"] != sum(case.rows)):
            raise ValueError("retained case observations or margins differ from the pinned snapshot")
        for law in backtest.LAWS:
            primary = record["laws"][law]["cells_row_major"][0]
            lower, upper = primary["interval"]
            if (primary["published_count"] != table[0][0]
                    or primary["interval"] != list(predictions[case.name][law]["interval"])
                    or primary["interval_width"] != upper - lower):
                raise ValueError("primary retained outcome or quantile endpoints differ from replay")
    return records, manifest


def build_report(input_path: Path = DEFAULT_INPUT) -> dict:
    source_bytes = input_path.read_bytes()
    source = json.loads(source_bytes)
    records, manifest = validate_retained_panel(source)
    cases = []
    sums = {law: {"score": Fraction(0), "width": 0, "penalty": Fraction(0),
                  "normalized": Fraction(0)} for law in backtest.LAWS}
    for record in records:
        result = {"case": record["case"], "case_jobs": record["case_jobs"], "laws": {}}
        for law in backtest.LAWS:
            primary = record["laws"][law]["cells_row_major"][0]
            lower, upper = primary["interval"]
            score = interval_score(lower, upper, primary["published_count"])
            exact = Fraction(score["interval_score_jobs_exact"])
            normalized = exact / record["case_jobs"]
            score.update({"published_count": primary["published_count"],
                          "interval": [lower, upper],
                          "score_fraction_of_case_total_exact": str(normalized),
                          "score_fraction_of_case_total": float(normalized)})
            result["laws"][law] = score
            sums[law]["score"] += exact
            sums[law]["width"] += upper - lower
            sums[law]["penalty"] += exact - (upper - lower)
            sums[law]["normalized"] += normalized
        cases.append(result)
    count = len(cases)
    summary = {}
    for law, totals in sums.items():
        mean = totals["score"] / count
        normalized = totals["normalized"] / count
        summary[law] = {
            "denominator": count,
            "mean_interval_score_jobs_exact": str(mean),
            "mean_interval_score_jobs": float(mean),
            "mean_interval_width_jobs": float(Fraction(totals["width"], count)),
            "mean_miss_penalty_jobs": float(totals["penalty"] / count),
            "mean_score_fraction_of_case_total_exact": str(normalized),
            "mean_score_fraction_of_case_total": float(normalized),
        }
    return {
        "schema_version": 1, "experiment": "public_lodes_posthoc_interval_score",
        "analysis_status": "Post hoc scoring supplement; not a change to the frozen selection or primary coverage protocol.",
        "source_report": {"path": "reports/commuting-backtest.json",
                          "sha256": hashlib.sha256(source_bytes).hexdigest()},
        "experiment_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "protocol_sha256": manifest["protocol_sha256"],
        "subset": manifest["subset"],
        "score_definition": {
            "name": "Negatively oriented central interval score (Winkler score)",
            "formula": "(u-l)+(2/alpha)*(l-y)*1[y<l]+(2/alpha)*(y-u)*1[y>u]",
            "alpha_exact": str(ALPHA), "nominal_interval_mass_exact": "19/20",
            "quantile_probabilities_exact": ["1/40", "39/40"],
            "miss_penalty_multiplier_exact": str(2 / ALPHA),
            "direction": "Lower is better; score units are published jobs.",
            "reference": {"authors": "Gneiting and Raftery", "year": 2007,
                          "section": "6.2", "equation": 43, "url": SCORE_REFERENCE},
            "discreteness": "Use nominal alpha=1/20, not one minus the achieved model interval mass. Width is u-l; endpoints are included.",
        },
        "scored_target": "FIPS-first home/work cell, one primary score per retained 2x2 case. Other affine-transformed cells and intercounty metrics are not scored in this supplement.",
        "verification": {"pinned_snapshot_validated": True,
                         "all_primary_intervals_replayed_from_only_margins": True,
                         "endpoints_checked": count * len(backtest.LAWS) * 2},
        "aggregation": "Unweighted descriptive case means; normalized scores divide by each case's known margin total before averaging.",
        "dependence": "100 overlapping cases from one released 5x5 table, not independent replications. No binomial confidence interval, calibration guarantee, or significance test.",
        "interpretation": "Propriety concerns expected loss for the specified quantiles. A lower realized mean on this dependent case frame does not establish empirical calibration or application-wide model validity.",
        "new_data": "None; only the original checksum-pinned public county table and existing held-out report are used.",
        "candidate_cases": source["candidate_cases"], "included_cases": count,
        "summary": summary, "cases": cases,
        "reproduce": "python3 experiments/commuting_interval_score.py --output .local/reports/commuting-interval-score-replay.json",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    encoded = json.dumps(build_report(), indent=2, sort_keys=True, allow_nan=False) + "\n"
    if args.output:
        # Even an accidental --output argument must preserve historical evidence.
        protected = [DEFAULT_INPUT, ROOT / "experiments/commuting_backtest.py"]
        destination = args.output.resolve()
        if destination in [p.resolve() for p in protected] or destination.is_relative_to(backtest.DATA.resolve()):
            parser.error("output must not overwrite the historical backtest or public snapshot")
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(encoded)
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
