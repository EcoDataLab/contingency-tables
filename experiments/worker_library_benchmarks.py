"""Bounded same-law classical urn/SciPy/R fixed-margin sampling benchmarks.

Optional SciPy and R are discovered, never installed by this script. Each method
returns unrestricted nonnegative integer tables with inverse-factorial mass.
This does not execute the uniform-table sampler in Finding #115.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import importlib
import json
import math
import os
from pathlib import Path
import platform
import random
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

from contingency115.tables import (ComputationBudgetExceeded, ExactTableSampler,
                                  ProductWeights, TableProblem)
from contingency115.workers import OrdinaryWorkerSampler, worker_linear_moments

ROOT = Path(__file__).resolve().parents[1]
SEED = 115202610
MAX_CELLS = 100_000
MAX_OUTPUT_CELLS = 2_000_000
MAX_URN_RANDOM_DRAWS = 1_000_000
MAX_URN_RUN_DRAWS = 3_000_000
MAX_BOYETT_TOTAL = 1_000_000
MAX_R_LOG_FACTORIAL_TOTAL = 1_000_000
R_MAX_INTEGER = 2**31 - 1
METHODS = ("worker_urn", "scipy_auto", "scipy_boyett", "scipy_patefield", "r_patefield")
THREAD_VARIABLES = ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
                    "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS")


@dataclass(frozen=True)
class Case:
    name: str
    family: str
    rows: tuple[int, ...]
    columns: tuple[int, ...]
    draws: int


def split_total(total, count):
    quotient, remainder = divmod(total, count)
    return tuple(quotient + (i < remainder) for i in range(count))


def cases():
    result = [Case("law_2x2_n4", "exact_small_law", (2, 2), (2, 2), 1024),
              Case("law_3x3_n6", "exact_small_law", (2, 2, 2), (2, 2, 2), 1024)]
    for total, draws in ((1_000, 32), (10_000, 16), (100_000, 4), (1_000_000, 2)):
        result.append(Case(f"total_20x5_n{total}", "numeric_total_scale",
                           split_total(total, 20), split_total(total, 5), draws))
    for row_count in (5, 100, 1000):
        result.append(Case(f"rows_{row_count}x5_n10000", "row_dimension_scale",
                           split_total(10_000, row_count), (2000,) * 5, 8))
    for column_count in (20, 100):
        result.append(Case(f"columns_100x{column_count}_n10000", "column_dimension_scale",
                           (100,) * 100, split_total(10_000, column_count), 8))
    result.append(Case("skewed_3x5_n1000000000", "large_total_small_urn_work",
                       (999_999_990, 6, 4), (200_000_000,) * 5, 32))
    return result


def validate_configuration(case, warmup, repetitions):
    if (not case.rows or not case.columns or
            any(type(x) is not int or x < 0 for x in case.rows + case.columns) or
            sum(case.rows) != sum(case.columns)):
        raise ValueError("cases require matching nonnegative integer margin vectors")
    if not 1 <= case.draws <= 2048 or not 0 <= warmup <= 32 or not 1 <= repetitions <= 5:
        raise ValueError("draws must be 1..2048, warmup 0..32, repetitions 1..5")
    cells = len(case.rows) * len(case.columns)
    if cells > MAX_CELLS or cells * max(case.draws, warmup) > MAX_OUTPUT_CELLS:
        raise ValueError("benchmark dense-output budget exceeded")


def coefficients(case):
    # Deliberately nonseparable, small integers; this is an abstract observable.
    return tuple(tuple((i % 7 - j % 5)**2 for j in range(len(case.columns)))
                 for i in range(len(case.rows)))


def exact_reference(case):
    q = coefficients(case)
    started = time.perf_counter()
    moments = worker_linear_moments(case.rows, case.columns, q)
    n, r, c = sum(case.rows), case.rows[0], case.columns[0]
    first_variance = Fraction(r*c*(n-r)*(n-c), n*n*(n-1)) if n > 1 else Fraction(0)
    result = {"metric_mean": str(moments.mean), "metric_variance": str(moments.variance),
              "first_cell_mean": str(Fraction(r*c, n)) if n else "0",
              "first_cell_variance": str(first_variance),
              "moment_seconds": time.perf_counter() - started,
              "full_covariance_used": True,
              "metric": "sum((row_index % 7 - column_index % 5)^2 * cell_count)"}
    probabilities = None
    if case.family == "exact_small_law":
        tables = tuple(ExactTableSampler(TableProblem(case.rows, case.columns)).tables(max_tables=2000))
        weights = ProductWeights([[1] * len(case.columns) for _ in case.rows], factorial_weight=True)
        masses = [weights.table_weight(t) for t in tables]
        normalizer = sum(masses, Fraction())
        probabilities = dict(zip(tables, (mass / normalizer for mass in masses)))
        # Independent combinatorial factorial normalization, not a sampler fit.
        prefactor = Fraction(math.prod(math.factorial(x) for x in case.rows + case.columns),
                             math.factorial(n))
        if any(p != prefactor * weights.table_weight(t) for t, p in probabilities.items()):
            raise RuntimeError("small-fiber oracle disagrees with normalized factorial law")
        result["exact_fiber"] = [{"table": t, "probability": str(p)} for t, p in probabilities.items()]
    return result, probabilities


def validate_tables(tables, case):
    normalized = []
    for table in tables:
        t = tuple(tuple(int(x) for x in row) for row in table)
        if (len(t) != len(case.rows) or any(len(row) != len(case.columns) for row in t)
                or any(x < 0 for row in t for x in row)
                or any(int(x) != x for row in table for x in row)
                or tuple(map(sum, t)) != case.rows
                or tuple(map(sum, zip(*t))) != case.columns):
            raise RuntimeError("sample violated shape, integrality, nonnegativity or fixed margins")
        normalized.append(t)
    if len(normalized) != case.draws:
        raise RuntimeError("sampler did not return requested output count")
    return normalized


def observations(tables, q):
    return ([sum(q[i][j]*x for i, row in enumerate(t) for j, x in enumerate(row)) for t in tables],
            [t[0][0] for t in tables])


def diagnostic(values, mean, variance):
    exact_mean, exact_variance = Fraction(mean), Fraction(variance)
    empirical_mean = statistics.fmean(values)
    se = math.sqrt(float(exact_variance) / len(values))
    return {"sample_count": len(values), "empirical_mean": empirical_mean,
            "empirical_variance_unbiased": statistics.variance(values) if len(values) > 1 else None,
            "exact_mean": str(exact_mean), "exact_variance": str(exact_variance),
            "iid_mean_standard_error": se,
            "mean_error_in_standard_errors": (empirical_mean-float(exact_mean))/se if se else None,
            "interpretation": "finite-sample diagnostic, not a proof of the sampling law"}


def summarize(runs, reference, probabilities, metric_values, first_values, counts):
    result = {"metric": diagnostic(metric_values, reference["metric_mean"], reference["metric_variance"]),
              "first_cell": diagnostic(first_values, reference["first_cell_mean"], reference["first_cell_variance"]),
              "median_draw_seconds_per_table": statistics.median(r["draw_seconds"]/r["completed_outputs"] for r in runs),
              "median_setup_plus_draw_seconds_per_table": statistics.median(r["setup_plus_draw_seconds"]/r["completed_outputs"] for r in runs)}
    if probabilities is not None:
        size = len(metric_values)
        tv = sum(abs(Fraction(counts[t], size)-p) for t, p in probabilities.items())/2
        result["small_fiber"] = {"empirical_total_variation": str(tv), "distinct_tables": len(counts),
            "frequency_comparison": [{"table": t, "exact_probability": str(p), "observed_count": counts[t]}
                                      for t, p in probabilities.items()]}
    return result


def skip_reason(case, method, warmup):
    if method == "scipy_boyett" and sum(case.rows) > MAX_BOYETT_TOTAL:
        return "Boyett O(N) scratch storage preflight exceeds configured total cap"
    if method == "r_patefield" and (len(case.rows) < 2 or len(case.columns) < 2 or sum(case.rows) > R_MAX_INTEGER):
        return "R requires at least two margins on each axis and this harness restricts total to signed 32-bit integer"
    if method == "r_patefield" and sum(case.rows) > MAX_R_LOG_FACTORIAL_TOTAL:
        return "R r2dtable API prepares N+1 log-factorials per call; total exceeds configured scratch/work cap"
    if method == "worker_urn":
        try:
            plan = OrdinaryWorkerSampler(case.rows, case.columns, max_draws=MAX_URN_RANDOM_DRAWS,
                                         max_cells=MAX_CELLS).plan
        except ComputationBudgetExceeded as error:
            return str(error)
        if plan.maximum_random_draws * (case.draws + warmup) > MAX_URN_RUN_DRAWS:
            return "conservative urn draw count across one run exceeds configured work cap"
    return None


def python_method(case, method, warmup, repetitions, seed, scipy_modules, reference, probabilities):
    runs, all_metric, all_first, counts = [], [], [], Counter()
    q = coefficients(case)
    for repeat in range(repetitions):
        run_seed = seed + repeat
        started = time.perf_counter()
        if method == "worker_urn":
            sampler = OrdinaryWorkerSampler(case.rows, case.columns, max_draws=MAX_URN_RANDOM_DRAWS,
                                            max_cells=MAX_CELLS)
            rng = random.Random(run_seed)
            def draw(size):
                receipts = [sampler.sample_with_stats(rng) for _ in range(size)]
                return [x.table for x in receipts], {"random_draws": sum(x.random_draws for x in receipts),
                    "fenwick_steps": sum(x.fenwick_steps for x in receipts),
                    "deterministically_assigned_workers": sum(x.deterministically_assigned_workers for x in receipts)}
            rng_name = "Python random.Random / MT19937"
        else:
            np, scipy, random_table = scipy_modules
            rng = np.random.Generator(np.random.PCG64(run_seed))
            sampler = random_table(case.rows, case.columns)
            scipy_method = None if method == "scipy_auto" else method.removeprefix("scipy_")
            def draw(size):
                return sampler.rvs(size=size, method=scipy_method, random_state=rng), None
            rng_name = "NumPy Generator / PCG64"
        setup = time.perf_counter() - started
        started = time.perf_counter()
        if warmup:
            draw(warmup)
        warming = time.perf_counter() - started
        started = time.perf_counter()
        tables, work = draw(case.draws)
        drawing = time.perf_counter() - started
        started = time.perf_counter()
        normalized = validate_tables(tables, case)
        metrics, firsts = observations(normalized, q)
        all_metric.extend(metrics)
        all_first.extend(firsts)
        if probabilities is not None:
            if any(t not in probabilities for t in normalized):
                raise RuntimeError("sample outside independently enumerated support")
            counts.update(normalized)
        validation = time.perf_counter() - started
        runs.append({"repeat": repeat, "seed": run_seed, "rng": rng_name,
                     "setup_seconds": setup, "warmup_seconds": warming, "draw_seconds": drawing,
                     "setup_plus_draw_seconds": setup+drawing,
                     "setup_warmup_draw_seconds": setup+warming+drawing,
                     "validation_and_observation_seconds": validation,
                     "completed_outputs": case.draws, "margins_verified": True, "work": work})
    return {"method": method, "status": "completed", "runs": runs,
            "summary": summarize(runs, reference, probabilities, all_metric, all_first, counts)}


def r_script(case, warmup, repetitions, seed):
    vector = lambda xs: "c(" + ",".join(map(str, xs)) + ")"
    # All inserted values are validated integers. Base R only; no jsonlite.
    return f'''
options(digits=17)
clock <- function() as.numeric(Sys.time())
for (k in seq_len({repetitions})) {{
  started <- clock()
  r <- as.integer({vector(case.rows)})
  cc <- as.integer({vector(case.columns)})
  RNGkind("Mersenne-Twister", "Inversion", "Rejection")
  set.seed({seed} + k - 1L)
  setup <- clock() - started
  started <- clock()
  if ({warmup} > 0) invisible(stats::r2dtable({warmup}, r, cc))
  warming <- clock() - started
  started <- clock()
  draws <- stats::r2dtable({case.draws}, r, cc)
  drawing <- clock() - started
  started <- clock()
  q <- outer((seq_along(r)-1L) %% 7L, (seq_along(cc)-1L) %% 5L, function(i,j) (i-j)^2)
  ok <- all(vapply(draws, function(x) all(rowSums(x)==r) && all(colSums(x)==cc) && all(x>=0), logical(1)))
  if (!ok || length(draws) != {case.draws}) stop("R output violated fixed margins")
  metrics <- vapply(draws, function(x) sum(q*x), numeric(1))
  first <- vapply(draws, function(x) x[1,1], numeric(1))
  validation <- clock() - started
  cat("RUN", k-1L, {seed}+k-1L, setup, warming, drawing, validation, sep="\\t")
  cat("\\nMETRIC\\t", paste(metrics, collapse=","), "\\nFIRST\\t", paste(first, collapse=","), "\\n", sep="")
  if ({str(case.family == "exact_small_law").upper()}) {{
    cat("TABLES\\t", paste(vapply(draws, function(x) paste(as.vector(t(x)), collapse=","), character(1)), collapse=";"), "\\n", sep="")
  }}
}}
'''


def r_method(case, warmup, repetitions, seed, executable, reference, probabilities):
    started = time.perf_counter()
    with tempfile.TemporaryDirectory(prefix="worker-library-r-") as folder:
        source = Path(folder) / "benchmark.R"
        source.write_text(r_script(case, warmup, repetitions, seed))
        proc = subprocess.run([executable, "--vanilla", str(source)], capture_output=True,
                              text=True, timeout=60)
    process_wall = time.perf_counter() - started
    if proc.returncode:
        return {"method": "r_patefield", "status": "failed", "reason": proc.stderr.strip(),
                "process_wall_seconds": process_wall}
    runs, metrics, firsts, counts = [], [], [], Counter()
    for line in proc.stdout.splitlines():
        fields = line.split("\t")
        if fields[0] == "RUN":
            _, repeat, run_seed, setup, warming, drawing, validation = fields
            setup, warming, drawing, validation = map(float, (setup, warming, drawing, validation))
            runs.append({"repeat": int(repeat), "seed": int(run_seed),
                "rng": "R Mersenne-Twister / Inversion / Rejection",
                "setup_seconds": setup, "warmup_seconds": warming, "draw_seconds": drawing,
                "setup_plus_draw_seconds": setup+drawing, "setup_warmup_draw_seconds": setup+warming+drawing,
                "validation_and_observation_seconds": validation,
                "completed_outputs": case.draws, "margins_verified": True})
        elif fields[0] == "METRIC":
            metrics.extend(map(int, fields[1].split(",")))
        elif fields[0] == "FIRST":
            firsts.extend(map(int, fields[1].split(",")))
        elif fields[0] == "TABLES":
            for encoded in fields[1].split(";"):
                cells = list(map(int, encoded.split(",")))
                n = len(case.columns)
                table = tuple(tuple(cells[i:i+n]) for i in range(0, len(cells), n))
                if table not in probabilities:
                    raise RuntimeError("R sample outside exact small-fiber support")
                counts[table] += 1
        else:
            raise RuntimeError("unexpected R benchmark output")
    if len(runs) != repetitions or len(metrics) != case.draws*repetitions or len(firsts) != len(metrics):
        raise RuntimeError("R benchmark output incomplete")
    return {"method": "r_patefield", "status": "completed", "runs": runs,
            "process_wall_seconds": process_wall,
            "process_wall_scope": "one fresh R process per case, including startup, all repetitions, validation and text serialization",
            "summary": summarize(runs, reference, probabilities, metrics, firsts, counts)}


def discover_dependencies():
    modules = None
    try:
        np = importlib.import_module("numpy")
        scipy = importlib.import_module("scipy")
        random_table = importlib.import_module("scipy.stats").random_table
        modules = np, scipy, random_table
        scipy_info = {"status": "available", "numpy_version": np.__version__, "scipy_version": scipy.__version__}
    except (ImportError, AttributeError) as error:
        scipy_info = {"status": "unavailable", "reason": str(error)}
    executable = shutil.which("Rscript")
    r_info = {"status": "unavailable", "reason": "Rscript executable not found"}
    if executable:
        try:
            probe = subprocess.run([executable, "--vanilla", "-e",
                'cat(R.version.string, as.character(packageVersion("stats")), R.version$platform, sep="\\n")'],
                capture_output=True, text=True, timeout=20, check=True)
            version, stats_version, r_platform = probe.stdout.splitlines()
            r_info = {"status": "available", "r_version": version, "stats_version": stats_version,
                      "platform": r_platform}
        except (subprocess.SubprocessError, ValueError, OSError) as error:
            executable = None
            r_info = {"status": "unavailable", "reason": str(error)}
    return modules, executable, {"scipy": scipy_info, "r": r_info}


def scipy_law_check(modules):
    if modules is None:
        return {"status": "skipped", "reason": "SciPy unavailable"}
    np, scipy, random_table = modules
    result = []
    for case in cases()[:2]:
        reference, probabilities = exact_reference(case)
        differences = [abs(float(random_table.pmf(t, case.rows, case.columns))-float(p))
                       for t, p in probabilities.items()]
        if max(differences) > 1e-12:
            raise RuntimeError("SciPy PMF differs from independently enumerated inverse-factorial law")
        result.append({"case": case.name, "tables_checked": len(probabilities),
                       "maximum_pmf_absolute_error": max(differences)})
    return {"status": "completed", "check": "every table in two small fibers, not just sampled moments",
            "cases": result}


def hardware_inventory():
    result = {"platform": platform.platform(), "architecture": platform.machine(),
              "logical_cpu_count": os.cpu_count()}
    if sys.platform == "darwin":
        probe = subprocess.run(["sysctl", "hw.model", "hw.memsize", "hw.logicalcpu", "machdep.cpu.brand_string"],
                               capture_output=True, text=True)
        if probe.returncode:
            result["detail_status"] = "unavailable under current permissions"
        else:
            result.update(dict(line.split(": ", 1) for line in probe.stdout.splitlines()))
    return result


def run(selected=None, warmup=1, repetitions=3, seed=SEED, methods=METHODS, hardware=None):
    selected = cases() if selected is None else selected
    if not selected or any(method not in METHODS for method in methods):
        raise ValueError("select at least one case and known methods")
    if type(seed) is not int or seed < 0:
        raise ValueError("seed must be a nonnegative integer usable by all runtimes")
    for case in selected:
        validate_configuration(case, warmup, repetitions)
    maximum_seed_offset = 100 * (len(selected) - 1) + repetitions - 1
    if seed > R_MAX_INTEGER - maximum_seed_offset:
        raise ValueError("seed must leave signed 32-bit range for every case and repetition")
    modules, r_executable, dependencies = discover_dependencies()
    report = {"schema_version": 1, "created_utc": datetime.now(timezone.utc).isoformat(),
        "target_law": "unrestricted_fixed_margin_probability_proportional_to_inverse_cell_factorials",
        "finding_115_uniform_sampler_executed": False,
        "data_classification": "synthetic", "python_version": platform.python_version(),
        "operating_system": platform.platform(),
        "optional_dependency_recipe": [
            "python3 -m venv .local/worker-library-benchmark-venv",
            ".local/worker-library-benchmark-venv/bin/python -m pip install scipy==1.18.1 numpy==2.5.3",
            "Rscript was already installed; this experiment installs no R packages"],
        "dependencies": dependencies, "hardware": hardware or hardware_inventory(),
        "execution": {"processes_parallelized": False, "sampler_threads_requested": 1,
                      "thread_environment": {key: os.environ.get(key, "unset") for key in THREAD_VARIABLES},
                      "note": "sequential sampling APIs; thread environment recorded, actual native thread count not instrumented",
                      "seed_base": seed, "warmup_draws_per_repeat": warmup, "repetitions": repetitions,
                      "api_mode": "one batch call per phase for SciPy/R, Python loop returning the same number of tables for urn",
                      "timing_scope": "setup includes margin processing/sampler and RNG construction; native per-call scratch setup stays in draw cost; imports excluded",
                      "python_timer": "time.perf_counter, monotonic high-resolution elapsed clock",
                      "r_timer": "as.numeric(Sys.time()), wall elapsed clock; small batches amortize timer granularity",
                      "shared_host_activity": "not isolated or instrumented; timings are observations on one shared host"},
        "budgets": {"max_cells": MAX_CELLS, "max_output_cells": MAX_OUTPUT_CELLS,
                    "max_urn_draws_per_table": MAX_URN_RANDOM_DRAWS,
                    "max_urn_draws_per_run": MAX_URN_RUN_DRAWS,
                    "max_boyett_total": MAX_BOYETT_TOTAL,
                    "max_r_log_factorial_total": MAX_R_LOG_FACTORIAL_TOTAL},
        "scipy_exact_pmf_crosscheck": scipy_law_check(modules),
        "source_sha256": {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in
                          ("experiments/worker_library_benchmarks.py", "src/contingency115/workers.py", "src/contingency115/tables.py")},
        "documentation": ["https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.random_table.html",
                          "https://stat.ethz.ch/R-manual/R-devel/library/stats/html/r2dtable.html",
                          "https://github.com/wch/r-source/blob/R-4-5-branch/src/library/stats/src/random.c"],
        "cases": []}
    for index, case in enumerate(selected):
        reference, probabilities = exact_reference(case)
        result = {**asdict(case), "dimensions": [len(case.rows), len(case.columns)],
                  "total": sum(case.rows), "reference": reference, "methods": []}
        for method in methods:
            reason = skip_reason(case, method, warmup)
            if method.startswith("scipy_") and modules is None:
                reason = dependencies["scipy"]["reason"]
            if method == "r_patefield" and r_executable is None:
                reason = dependencies["r"]["reason"]
            if reason:
                measured = {"method": method, "status": "skipped", "reason": reason}
            elif method == "r_patefield":
                try:
                    measured = r_method(case, warmup, repetitions, seed+index*100, r_executable, reference, probabilities)
                except subprocess.TimeoutExpired:
                    measured = {"method": method, "status": "timeout", "reason": "R process exceeded 60 seconds"}
            else:
                measured = python_method(case, method, warmup, repetitions, seed+index*100,
                                         modules, reference, probabilities)
            result["methods"].append(measured)
        report["cases"].append(result)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT/"reports/worker-library-benchmarks.json")
    parser.add_argument("--warmup", type=int, default=1)
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--seed", type=int, default=SEED)
    parser.add_argument("--case", action="append", dest="case_names")
    parser.add_argument("--hardware-json", type=Path, help="verified public hardware description JSON, without hostnames or serials")
    args = parser.parse_args()
    selected = [c for c in cases() if args.case_names is None or c.name in args.case_names]
    if args.case_names and set(args.case_names)-{c.name for c in selected}:
        parser.error("unknown case name")
    hardware = json.loads(args.hardware_json.read_text()) if args.hardware_json else None
    try:
        report = run(selected, args.warmup, args.repetitions, args.seed, hardware=hardware)
    except ValueError as error:
        parser.error(str(error))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"output": str(args.output), "cases": len(report["cases"]),
                      "dependencies": report["dependencies"]}, indent=2))


if __name__ == "__main__":
    main()
