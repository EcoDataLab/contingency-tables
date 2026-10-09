"""Bounded same-law sampling comparison; not a convergence certificate.

Run from the repository root with PYTHONPATH=src. Timings are observations,
not reproducible certificates. The report identifies the code that produced it.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, asdict
from fractions import Fraction
import hashlib
import json
from math import lcm
from pathlib import Path
import platform
import random
import statistics
import time
import tracemalloc

from contingency115.kernels import four_cycles, simple_cycles, line_interval, heat_bath_kernel
from contingency115.chain_diagnostics import stationary_variance
from contingency115.workers import OrdinaryWorkerSampler
from contingency115.ideal_chain import build_ideal_chain, IdealChainBudget
from contingency115.tables import (ComputationBudgetExceeded, ExactTableSampler,
                                   ExactWeightedTableSampler, ProductWeights, TableProblem)

ROOT = Path(__file__).resolve().parents[1]
BUDGET = dict(max_states=20_000, max_transitions=200_000)
ORACLE_MAX_TABLES = 2_000
DIAGNOSTIC_MAX_STATES = 48
DIAGNOSTIC_MAX_BITS = 4096
MAX_WEIGHTED_LINE = 2_000
MAX_DRAW_REQUEST = 10_000
MAX_WARMUP_REQUEST = 2_000
MAX_REPETITIONS = 5
IID_METHODS = ("exact_dp", "worker_urn_iid")
IDEAL_METHODS = ("ideal_direct_return", "ideal_physical_return")
IDEAL_BUDGET = IdealChainBudget(max_physical_states=64, max_solve_size=48,
                               max_solve_work=300_000, max_transition_work=100_000)
MAX_PHYSICAL_STEPS_PER_EXCURSION = 10_000
MAX_PHYSICAL_STEPS_PER_RUN = 100_000


@dataclass(frozen=True)
class Case:
    name: str
    family: str
    problem: TableProblem
    weights: ProductWeights | None = None
    catalogs: tuple[str, ...] = ("rectangles",)


def cases():
    result = [
        Case("rectangle_2x2", "few_modes", TableProblem([2, 2], [2, 2])),
        Case("few_modes_6x3", "few_modes", TableProblem([1] * 6, [2] * 3)),
        Case("dense_3x3", "balanced_dense", TableProblem([2] * 3, [2] * 3)),
        Case("dense_4x4", "balanced_dense", TableProblem([2] * 4, [2] * 4)),
        Case("zero_margins_4x4", "small_sparse_margins", TableProblem([2, 1, 1, 0], [2, 1, 1, 0])),
        Case("unequal_4x3", "unequal_margins", TableProblem([12, 1, 1, 1], [7, 4, 4])),
    ]
    result += [Case(f"unit_{n}x{n}", "both_dimensions_increase", TableProblem([1] * n, [1] * n))
               for n in (3, 4, 5, 6)]
    result.append(Case("sparse_six_cycle", "sparse_support", TableProblem([1] * 3, [1] * 3,
        upper_bounds=[[1, 1, 0], [0, 1, 1], [1, 0, 1]]), catalogs=("rectangles", "all_simple")))
    data = json.loads((ROOT / "examples/synthetic_commute.json").read_text())
    problem = TableProblem(data["row_sums"], data["column_sums"],
                           upper_bounds=data["upper_bounds"], lower_bounds=data["lower_bounds"])
    result.append(Case("commute_uniform", "bounded_sparse_support", problem,
                       catalogs=("rectangles", "all_simple", "pretuned_rectangles", "pretuned_all_simple")))
    result.append(Case("commute_conditional_poisson", "product_weight", problem,
                       ProductWeights(data["activities"], factorial_weight=True),
                       ("rectangles", "all_simple", "pretuned_rectangles", "pretuned_all_simple")))
    for rows, columns in (([2, 2], [2, 2]), ([2, 2, 2], [2, 2, 2]), ([4, 2, 1], [3, 2, 2])):
        result.append(Case(f"ordinary_worker_{len(rows)}x{len(columns)}_{sum(rows)}", "ordinary_inverse_factorial",
                           TableProblem(rows, columns),
                           ProductWeights([[1] * len(columns) for _ in rows], factorial_weight=True)))
    for margin in (1, 2):
        result.append(Case(f"ideal_{margin}_2x2", "literal_ideal_chain_tiny",
                           TableProblem([margin, margin], [margin, margin]),
                           catalogs=("rectangles",) + IDEAL_METHODS))
    return result


def shift(table, cycle, amount):
    return tuple(tuple(x + amount * cycle.signs[i][j] for j, x in enumerate(row))
                 for i, row in enumerate(table))


def rational_choice(masses, rng):
    if not masses or any(mass < 0 for mass in masses):
        raise ValueError("conditional masses must be nonnegative and nonempty")
    denominator = lcm(*(mass.denominator for mass in masses))
    integers = [mass.numerator * (denominator // mass.denominator) for mass in masses]
    total = sum(integers)
    if not total:
        raise ValueError("zero-mass conditional line")
    rank = rng.randrange(total)
    if type(rank) is not int or not 0 <= rank < total:
        raise ValueError("RNG returned an out-of-range rank")
    for index, mass in enumerate(integers):
        if rank < mass:
            return index
        rank -= mass
    raise AssertionError("RNG returned an out-of-range rank")


def step(case, table, catalog, rng, work):
    """Exact full-line heat bath with input-fixed uniform or rational cycle weights."""
    work["transitions"] += 1
    if not catalog:
        work["empty_catalog_holds"] += 1
        work["self_transitions"] += 1
        return table
    if isinstance(catalog, FixedCatalog):
        rank = rng.randrange(catalog.choice_total)
        if type(rank) is not int or not 0 <= rank < catalog.choice_total:
            raise ValueError("RNG returned an out-of-range cycle rank")
        for cycle, mass in zip(catalog.cycles, catalog.choice_masses):
            if rank < mass:
                break
            rank -= mass
        else:
            raise AssertionError("invalid prepared cycle masses")
    else:
        cycle = catalog[rng.randrange(len(catalog))]
    lo, hi = line_interval(case.problem, table, cycle)
    work["line_intervals"] += 1
    work["degenerate_lines"] += int(lo == hi)
    if case.weights is None:
        result = shift(table, cycle, lo + rng.randrange(hi - lo + 1))
    else:
        if hi - lo + 1 > MAX_WEIGHTED_LINE:
            raise ComputationBudgetExceeded("weighted line exceeded MAX_WEIGHTED_LINE")
        targets = [shift(table, cycle, amount) for amount in range(lo, hi + 1)]
        masses = [case.weights.table_weight(target) for target in targets]
        work["line_weight_evaluations"] += len(targets)
        result = targets[rational_choice(masses, rng)] if sum(masses) else table
    work["self_transitions"] += int(result == table)
    return result


def new_work():
    return dict(transitions=0, line_intervals=0, degenerate_lines=0,
                line_weight_evaluations=0, self_transitions=0, empty_catalog_holds=0, worker_random_draws=0, worker_fenwick_steps=0,
                worker_deterministic_assignments=0, physical_steps=0, physical_completed_returns=0,
                failed_excursion_steps=0, direct_censored_draws=0)


def metric(table):
    # Nonseparable coefficients: row/column squared index distance, not physical VMT.
    return sum((i - j) ** 2 * x for i, row in enumerate(table) for j, x in enumerate(row))


def heuristic_ess(values):
    """Initial-positive paired autocorrelations, lag cap 200; diagnostic only."""
    size = len(values)
    if not size:
        return None
    mean = statistics.fmean(values)
    variance = sum((x - mean) ** 2 for x in values) / size
    if not variance or size < 4:
        return None
    centered = [x - mean for x in values]
    tau = 1.0
    for lag in range(1, min(size - 1, 200), 2):
        pair = sum(sum(centered[i] * centered[i + k] for i in range(size - k)) /
                   (size * variance) for k in (lag, lag + 1))
        if pair <= 0:
            break
        tau += 2 * pair
    return min(float(size), size / tau)


def diagnostics(samples, probabilities, seconds, independent=False):
    counts = Counter(samples)
    size = len(samples)
    tv = sum((abs(Fraction(counts[table], size) - p) for table, p in probabilities.items()), Fraction()) / 2
    values = [metric(table) for table in samples]
    target_mean = sum((p * metric(t) for t, p in probabilities.items()), Fraction())
    target_variance = sum((p * (metric(t) - target_mean) ** 2 for t, p in probabilities.items()), Fraction())
    ess = (float(size) if independent else heuristic_ess(values)) if target_variance else None
    return {"empirical_total_variation": str(tv), "empirical_total_variation_float": float(tv),
            "sample_mean": statistics.fmean(values), "distinct_tables": len(counts),
            "ess": ess, "ess_per_sampling_second": ess / seconds if ess is not None and seconds else None,
            "ess_kind": "zero_observable_variance" if not target_variance else ("independent_draw_count" if independent else "heuristic_autocorrelation_estimate")}


def make_dp(case):
    sampler = (ExactTableSampler(case.problem, **BUDGET) if case.weights is None else
               ExactWeightedTableSampler(case.problem, case.weights, **BUDGET))
    normalizer = sampler.count() if case.weights is None else sampler.normalizer()
    if not normalizer:
        raise ValueError("benchmark requires a positive-mass fiber")
    return sampler


@dataclass(frozen=True)
class FixedCatalog:
    cycles: tuple
    probabilities: tuple[Fraction, ...]
    choice_masses: tuple[int, ...]
    choice_total: int

    def __len__(self):
        return len(self.cycles)


def catalog_for(case, name):
    if name not in ("rectangles", "all_simple", "pretuned_rectangles", "pretuned_all_simple"):
        raise ValueError("unknown method")
    rectangles = name.endswith("rectangles")
    catalog = (four_cycles(case.problem) if rectangles else
               simple_cycles(case.problem, max_cycles=1_000, max_search_nodes=100_000))
    if not name.startswith("pretuned"):
        return catalog
    if case.name not in ("commute_uniform", "commute_conditional_poisson"):
        raise ValueError("saved mixture probabilities apply only to the matching fixture")
    data = json.loads((ROOT / "examples/synthetic_commute.json").read_text())
    expected_problem = TableProblem(data["row_sums"], data["column_sums"],
                                    upper_bounds=data["upper_bounds"], lower_bounds=data["lower_bounds"])
    expected_weights = ProductWeights(data["activities"], factorial_weight=True)
    if case.problem != expected_problem or (case.weights is not None and case.weights != expected_weights):
        raise ValueError("saved mixture target input differs")
    report = json.loads((ROOT / "reports/cycle-mixtures.json").read_text())
    if report["fixture_sha256"] != hashlib.sha256((ROOT / "examples/synthetic_commute.json").read_bytes()).hexdigest():
        raise ValueError("saved mixture fixture hash differs")
    for path in ("src/contingency115/tables.py", "src/contingency115/kernels.py"):
        if report["source_sha256"][path] != hashlib.sha256((ROOT / path).read_bytes()).hexdigest():
            raise ValueError("saved mixture sampler source hash differs")
    law = "uniform_tables" if case.weights is None else "conditional_poisson"
    entry = report["laws"][law]["cases"]["tuned_rectangles" if rectangles else "tuned_simple_cycles"]
    signs = [tuple(tuple(row) for row in report["catalog"][i]["signs"]) for i in entry["allowed_cycle_indices"]]
    full_signs = [tuple(tuple(row) for row in cycle["signs"]) for cycle in report["catalog"]]
    supplied = tuple(Fraction(p) for p in entry["cycle_probabilities"])
    if len(full_signs) != len(supplied) or len(set(full_signs)) != len(full_signs) or set(signs) != {cycle.signs for cycle in catalog}:
        raise ValueError("saved mixture cycle catalog differs")
    if any(p for i, p in enumerate(supplied) if i not in entry["allowed_cycle_indices"]):
        raise ValueError("saved mixture assigns mass to excluded cycles")
    by_signs = dict(zip(full_signs, supplied))
    probabilities = tuple(by_signs[cycle.signs] for cycle in catalog)
    if len(probabilities) != len(catalog) or any(p < 0 for p in probabilities) or sum(probabilities) != 1:
        raise ValueError("invalid fixed mixture probabilities")
    denominator = lcm(*(p.denominator for p in probabilities))
    masses = tuple(p.numerator * (denominator // p.denominator) for p in probabilities)
    return FixedCatalog(catalog, probabilities, masses, sum(masses))


def prepare_iid(case, method):
    if method == "exact_dp":
        return make_dp(case)
    if method == "worker_urn_iid" and case.family == "ordinary_inverse_factorial":
        return OrdinaryWorkerSampler(case.problem.row_sums, case.problem.column_sums,
                                     max_draws=2000, max_cells=1000)
    raise ValueError("iid baseline is not eligible for this target law")


@dataclass(frozen=True)
class IdealAdapter:
    chain: object
    table_indices: dict
    censored: object | None
    chain_construction_seconds: float
    algebraic_censoring_seconds: float


def prepare_method(case, method):
    if method in IID_METHODS:
        return prepare_iid(case, method)
    if method in IDEAL_METHODS:
        if case.weights is not None:
            raise ValueError("literal ideal chain has only the ordinary uniform target")
        before = time.perf_counter()
        chain = build_ideal_chain(case.problem, budget=IDEAL_BUDGET)
        construction = time.perf_counter() - before
        mapping = {}
        for index, state in enumerate(chain.states):
            if state.balanced:
                rows, columns = case.problem.shape
                table = [[0] * columns for _ in range(rows)]
                for (i, j), value in zip(chain.small_cells, state.row_view):
                    table[i][j] = value
                mapping[case.problem.validate_table(table)] = index
        before = time.perf_counter()
        censored = chain.all_small_return_kernel() if method == "ideal_direct_return" else None
        censoring = time.perf_counter() - before if censored is not None else 0.
        return IdealAdapter(chain, mapping, censored, construction, censoring)
    return catalog_for(case, method)


def advance(case, method, table, prepared, rng, work, physical_remaining=MAX_PHYSICAL_STEPS_PER_RUN):
    if method == "exact_dp":
        return prepared.sample(rng)
    if method == "worker_urn_iid":
        draw = prepared.sample_with_stats(rng)
        work["worker_random_draws"] += draw.random_draws
        work["worker_fenwick_steps"] += draw.fenwick_steps
        work["worker_deterministic_assignments"] += draw.deterministically_assigned_workers
        return draw.table
    if method == "ideal_direct_return":
        kernel = prepared.censored.kernel
        index = kernel.states.index(table)
        result = kernel.states[rational_choice(kernel.matrix[index], rng)]
        work["direct_censored_draws"] += 1
        work["self_transitions"] += int(result == table)
        return result
    if method == "ideal_physical_return":
        if physical_remaining < 1:
            raise ComputationBudgetExceeded("literal physical run exceeded total step budget")
        cap = min(MAX_PHYSICAL_STEPS_PER_EXCURSION, physical_remaining)
        try:
            returned = prepared.chain.physical_return(prepared.table_indices[table], max_steps=cap, rng=rng)
        except ComputationBudgetExceeded:
            # physical_return executes exactly cap steps before raising.
            work["physical_steps"] += cap
            work["failed_excursion_steps"] += cap
            raise
        work["physical_steps"] += returned.physical_steps
        work["physical_completed_returns"] += 1
        work["self_transitions"] += int(returned.table == table)
        return returned.table
    return step(case, table, prepared, rng, work)


def measured_memory(case, name, start, draws, seed):
    """Separate instrumentation pass: Python allocations, not process RSS."""
    tracemalloc.start()
    try:
        rng, prepared = random.Random(seed), prepare_method(case, name)
        table, samples, work = start, [], new_work()
        for _ in range(draws):
            table = advance(case, name, table, prepared, rng, work,
                            MAX_PHYSICAL_STEPS_PER_RUN - work["physical_steps"])
            samples.append(table)
        _, peak = tracemalloc.get_traced_memory()
        return {"traced_peak_bytes": peak, "draws": len(samples), "warmup": 0,
                "scope": "fresh preparation and retained outputs; excludes oracle/input/start allocations"}
    finally:
        tracemalloc.stop()


def exact_diagnostic(case, states, method):
    """Complete finite-kernel diagnostics outside operational sampling clocks."""
    before = time.perf_counter()
    try:
        if len(states) > DIAGNOSTIC_MAX_STATES:
            raise ComputationBudgetExceeded("fiber exceeds exact diagnostic state cap")
        extra = {}
        if method in IDEAL_METHODS:
            chain = build_ideal_chain(case.problem, budget=IDEAL_BUDGET)
            censored = chain.all_small_return_kernel()
            kernel = censored.kernel
            if kernel.states != states:
                raise ValueError("ideal censored state order differs from the oracle")
            extra = {"stationary_balanced_probability": str(censored.stationary_success_probability),
                     "expected_physical_steps_per_return_at_stationarity": str(censored.expected_physical_steps_per_return),
                     "per_start_expected_physical_steps": [str(x) for x in censored.per_start_expected_physical_steps],
                     "physical_state_count": len(chain.states), "beta": str(chain.beta),
                     "physical_build_work": dict(chain.work_counts),
                     "interpretation": "AV per returned table; Kac mean steps 1/pi(balance) excludes initial transient and warmup"}
        else:
            catalog = catalog_for(case, method)
            kernel = heat_bath_kernel(case.problem, states,
                                     catalog.cycles if isinstance(catalog, FixedCatalog) else catalog,
                                     cycle_probabilities=catalog.probabilities if isinstance(catalog, FixedCatalog) else None,
                                     weights=case.weights,
                                     max_kernel_states=DIAGNOSTIC_MAX_STATES, **BUDGET)
        result = stationary_variance(kernel, [metric(t) for t in states],
                                     max_states=DIAGNOSTIC_MAX_STATES,
                                     max_rational_bits=DIAGNOSTIC_MAX_BITS)
        return {"status": result.status, **extra,
                "stationary_mean": str(result.mean), "stationary_variance": str(result.variance),
                "between_class_mean_variance": str(result.between_class_variance),
                "asymptotic_variance": None if result.asymptotic_variance is None else str(result.asymptotic_variance),
                "variance_inflation_factor": None if result.variance_inflation_factor is None else str(result.variance_inflation_factor),
                "variance_inflation_factor_float": None if result.variance_inflation_factor is None else float(result.variance_inflation_factor),
                "irreducible_on_positive_support": result.irreducible_on_positive_support,
                "positive_support_classes": result.positive_support_classes,
                "component_means": [str(mu) for mu in result.component_means],
                "definition": "stationary-start limit of n*Var(sample mean); includes periodic kernels",
                "diagnostic_seconds": time.perf_counter() - before}
    except ComputationBudgetExceeded as error:
        return {"status": "budget_exceeded", "reason": str(error),
                "diagnostic_seconds": time.perf_counter() - before}


def timed_run(case, method, start, draws, warmup, seed, probabilities):
    """Fresh preparation per run, with partial progress preserved on budget failure."""
    result = {"seed": seed, "start": start, "requested_warmup": warmup,
              "requested_outputs": draws, "completed_outputs": 0,
              "preparation_seconds": 0., "initialization_seconds": 0.,
              "warmup_seconds": 0., "sampling_seconds": 0.}
    warm_work, work, samples = new_work(), new_work(), []
    phase = "preparation"
    before = time.perf_counter()
    prepared = None
    try:
        prepared = prepare_method(case, method)
        result["preparation_seconds"] = time.perf_counter() - before
        phase, before = "initialization", time.perf_counter()
        rng = random.Random(seed)
        table = None if method in IID_METHODS else case.problem.validate_table(start)
        result["initialization_seconds"] = time.perf_counter() - before
        phase, before = "warmup", time.perf_counter()
        for _ in range(warmup):
            table = advance(case, method, table, prepared, rng, warm_work,
                            MAX_PHYSICAL_STEPS_PER_RUN - warm_work["physical_steps"])
        result["warmup_seconds"] = time.perf_counter() - before
        phase, before = "sampling", time.perf_counter()
        for _ in range(draws):
            table = advance(case, method, table, prepared, rng, work,
                            MAX_PHYSICAL_STEPS_PER_RUN - warm_work["physical_steps"] - work["physical_steps"])
            samples.append(table)
        result["sampling_seconds"] = time.perf_counter() - before
        result["status"] = "completed"
    except ComputationBudgetExceeded as error:
        result[phase + "_seconds"] = time.perf_counter() - before
        result.update(status="budget_exceeded", failed_phase=phase, reason=str(error))
    result.update(completed_outputs=len(samples), warmup_work=warm_work, sampling_work=work,
                  dp_stats=prepared.stats if method == "exact_dp" and prepared is not None else None,
                  mh_rejections=None if method == "ideal_physical_return" else 0,
                  total_operational_seconds=sum(result[p + "_seconds"] for p in
                                                ("preparation", "initialization", "warmup", "sampling")))
    if method in IDEAL_METHODS and prepared is not None:
        result.update(chain_construction_seconds=prepared.chain_construction_seconds,
                      algebraic_censoring_seconds=prepared.algebraic_censoring_seconds,
                      runtime_kind="algebraic_direct_draw_bypasses_excursions" if method == "ideal_direct_return" else "literal_physical_steps_including_holds")
    if samples:
        result.update(diagnostics(samples, probabilities, result["sampling_seconds"], method in IID_METHODS))
        exact_mean = sum((p * metric(t) for t, p in probabilities.items()), Fraction())
        result["sample_mean_error"] = str(sum(map(metric, samples), Fraction()) / len(samples) - exact_mean)
        if result["status"] != "completed":
            result["ess"] = None
            result["ess_per_sampling_second"] = None
            result["ess_kind"] = "unavailable_failed_budget_limited_trajectory"
    return result


def run_case(case, draws, warmup, repetitions, seed):
    before = time.perf_counter()
    oracle = ExactTableSampler(case.problem, **BUDGET)
    states = tuple(oracle.tables(max_tables=ORACLE_MAX_TABLES))
    masses = [Fraction(1) if case.weights is None else case.weights.table_weight(t) for t in states]
    normalizer = sum(masses)
    if not normalizer:
        raise ValueError("benchmark requires a positive-mass fiber")
    probabilities = {t: m / normalizer for t, m in zip(states, masses)}
    support = sorted((t for t in states if probabilities[t]), key=lambda t: (metric(t), t))
    # Distinct extreme/intermediate metric starts are independent of seed replication.
    starts = list(dict.fromkeys(support[(len(support) - 1) * i // 2] for i in range(3)))
    oracle_seconds = time.perf_counter() - before
    methods = []
    mean = sum((p * metric(t) for t, p in probabilities.items()), Fraction())
    variance = sum((p * (metric(t) - mean) ** 2 for t, p in probabilities.items()), Fraction())
    eligible_iid = IID_METHODS if case.family == "ordinary_inverse_factorial" else ("exact_dp",)
    for method in eligible_iid + case.catalogs:
        runs = []
        for start in ([None] if method in IID_METHODS else starts):
            for schedule in ([0] if method in IID_METHODS else sorted(set((0, warmup)))):
                for repeat in range(repetitions):
                    runs.append(timed_run(case, method, start, draws, schedule,
                                          seed + repeat, probabilities))
        try:
            memory = measured_memory(case, method, starts[0], min(draws, 100), seed)
        except ComputationBudgetExceeded as error:
            memory = {"status": "budget_exceeded", "reason": str(error)}
        diagnostic = ({"status": "exact_iid", "stationary_mean": str(mean),
                       "stationary_variance": str(variance), "asymptotic_variance": str(variance),
                       "variance_inflation_factor": "1" if variance else None}
                      if method in IID_METHODS else exact_diagnostic(case, states, method))
        completed = [r for r in runs if r["status"] == "completed"]
        try:
            catalog_size = None if method in IID_METHODS + IDEAL_METHODS else len(catalog_for(case, method))
        except ComputationBudgetExceeded:
            catalog_size = None
        for observed in runs:
            observed["ess_interpretation"] = ("independent draw count under the stated RNG contract" if method in IID_METHODS
                                             else "descriptive trajectory heuristic only; no cold-start convergence or accuracy guarantee")
            if diagnostic.get("irreducible_on_positive_support") is False:
                observed["ess_interpretation"] = "reducible target support; any heuristic ESS is not whole-target effective sampling"
        methods.append({"method": method,
                        "law_status": "exact_independent" if method in IID_METHODS else "exact_invariant_law_finite_trajectory",
                        "catalog_size": catalog_size,
                        "runs": runs, "exact_stationary_diagnostic": diagnostic,
                        "mixture_tuning_cost": "not measured; supplied saved fixture weights; original full-fiber optimization excluded" if method.startswith("pretuned") else None,
                        "memory_separate_pass": memory,
                        "measurement_status": "all_requested_runs_completed" if len(completed) == len(runs) else "budget_failures_present",
                        "median_sampling_seconds": statistics.median(r["sampling_seconds"] for r in completed) if completed and len(completed) == len(runs) else None})
    return {"status": "completed", "name": case.name, "family": case.family, "shape": case.problem.shape,
            "rows": case.problem.row_sums, "columns": case.problem.column_sums,
            "lower_bounds": case.problem.lower_bounds, "upper_bounds": case.problem.upper_bounds,
            "activities": None if case.weights is None else [[str(x) for x in row] for row in case.weights.activities],
            "factorial_weight": case.weights.factorial_weight if case.weights else False,
            "target_law": "uniform_tables" if case.weights is None else ("ordinary_inverse_factorial_tables" if case.family == "ordinary_inverse_factorial" else "bounded_activity_weighted_conditional_poisson"),
            "table_count": len(states), "positive_support_count": len(support), "normalizer": str(normalizer),
            "oracle_seconds": oracle_seconds, "oracle_dp_stats": oracle.stats,
            "start_selection": "oracle metric minimum, middle sorted table, maximum; not operational initialization",
            "distinct_starts": len(starts),
            "metric": "sum((row_index-column_index)^2 * cell_count); indices start at zero",
            "exact_metric_mean": str(mean), "exact_metric_variance": str(variance), "methods": methods}


def run(*, smoke=False, draws=500, warmup=200, repetitions=2):
    for name, value, cap in (("draws", draws, MAX_DRAW_REQUEST),
                             ("repetitions", repetitions, MAX_REPETITIONS)):
        if type(value) is not int or not 1 <= value <= cap:
            raise ValueError(f"{name} must be a positive integer at most {cap}")
    if type(warmup) is not int or not 0 <= warmup <= MAX_WARMUP_REQUEST:
        raise ValueError(f"warmup must be an integer between 0 and {MAX_WARMUP_REQUEST}")
    selected = cases()
    if smoke:
        selected = [c for c in selected if c.name in ("rectangle_2x2", "sparse_six_cycle", "commute_conditional_poisson", "ideal_1_2x2")]
    sources = ["experiments/sampler_benchmarks.py", "src/contingency115/tables.py",
               "src/contingency115/kernels.py", "src/contingency115/chain_diagnostics.py", "examples/synthetic_commute.json",
               "reports/cycle-mixtures.json", "src/contingency115/workers.py", "src/contingency115/ideal_chain.py"]
    results = []
    for case in selected:
        before = time.perf_counter()
        try:
            results.append(run_case(case, draws, warmup, repetitions, 115_2026))
        except ComputationBudgetExceeded as error:
            results.append({"name": case.name, "family": case.family, "status": "budget_exceeded",
                            "reason": str(error), "elapsed_seconds": time.perf_counter() - before})
    return {"schema_version": 2, "status": "bounded_smoke_for_review" if smoke else "bounded_panel_for_review",
            "environment": {"python": platform.python_version(), "system": platform.system(),
                            "machine": platform.machine(), "timing_clock": "perf_counter", "isolation": "uncontrolled local development workload"},
            "source_sha256": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sources},
            "configuration": {"draws_per_run": draws, "warmup_schedules": sorted(set((0, warmup))),
                              "seed_repetitions_per_start_and_schedule": repetitions, "max_distinct_starts": 3,
                              "seed_base": 115_2026, "dp_budget": BUDGET, "oracle_max_tables": ORACLE_MAX_TABLES,
                              "diagnostic_max_states": DIAGNOSTIC_MAX_STATES, "diagnostic_max_rational_bits": DIAGNOSTIC_MAX_BITS,
                              "max_weighted_line": MAX_WEIGHTED_LINE,
                              "rational_cap_scope": "post-operation retained rational results; temporary products and sums are not preflight bounded",
                              "ideal_budget": asdict(IDEAL_BUDGET),
                              "max_physical_steps_per_excursion": MAX_PHYSICAL_STEPS_PER_EXCURSION,
                              "max_physical_steps_per_run": MAX_PHYSICAL_STEPS_PER_RUN,
                              "catalog_max_cycles": 1000, "catalog_max_search_nodes": 100000},
            "rng_contract": "each randrange(stop) must be uniform conditional on previous calls; random.Random seeds supply reproducible pseudorandom trajectories only; shared seeds are not matched randomness across methods",
            "literal_115_backend": "literal ideal physical-chain tiny panel and algebraic censored-return diagnostic; complete finite-bit schedule unavailable",
            "pending": ["independent review", "complete finite-bit sampler remains unavailable"],
            "cases": results}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--draws", type=int, default=500)
    parser.add_argument("--warmup", type=int, default=200)
    parser.add_argument("--repetitions", type=int, default=2)
    parser.add_argument("--output", type=Path, default=ROOT / "reports/sampler-benchmarks.json")
    args = parser.parse_args()
    args.output.write_text(json.dumps(run(smoke=args.smoke, draws=args.draws,
        warmup=args.warmup, repetitions=args.repetitions), indent=2) + "\n")
