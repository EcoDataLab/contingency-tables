"""Opt-in finite reference-implementation benchmarks; standard library only.

PYTHONPATH=src python3 experiments/implementation_benchmarks.py --output .local/reports/implementation-benchmarks.json
Baseline code is loaded read-only from Git, never copied into the checkout.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
from time import perf_counter
import tracemalloc
import types
from unittest.mock import patch

import contingency115.kernels as kernels
import contingency115.tables as tables

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "d851f00508840e5182fe5e9328446e65626f6e6b"
SEED, REPETITIONS, DRAWS = 115, 3, 2000


def digest(value):
    return sha256(json.dumps(value, separators=(",", ":")).encode()).hexdigest()


def load_baseline():
    package = types.ModuleType("_implementation_baseline")
    package.__path__ = []
    sys.modules[package.__name__] = package
    modules, hashes = {}, {}
    for name in ("tables", "kernels"):
        path = f"src/contingency115/{name}.py"
        source = subprocess.check_output(["git", "show", f"{BASELINE}:{path}"], cwd=ROOT)
        module = types.ModuleType(f"{package.__name__}.{name}")
        module.__package__ = package.__name__
        sys.modules[module.__name__] = module
        exec(compile(source, f"{BASELINE}:{path}", "exec"), module.__dict__)
        modules[name], hashes[path] = module, sha256(source).hexdigest()
    return modules, hashes


def summarize(spans):
    return {"median_seconds": median(spans), "repetitions_seconds": spans}


def elapsed(action):
    start = perf_counter()
    action()
    return perf_counter() - start


def measure(action):
    return summarize([elapsed(action) for _ in range(REPETITIONS)])


def allocations(action):
    tracemalloc.start()
    try:
        output = action()  # Keep returned output alive through the reading.
        retained, peak = tracemalloc.get_traced_memory()
        return {"retained_traced_bytes": retained, "peak_traced_bytes": peak}
    finally:
        tracemalloc.stop()


class Trace(random.Random):
    def __init__(self):
        super().__init__(SEED)
        self.trace = []

    def randrange(self, stop):
        value = super().randrange(stop)
        self.trace.append((stop, value))
        return value


WEIGHTED = (
    ("rational_factorial_3x3", [6] * 3, [6] * 3,
     [[Fraction(2, 3), 1, 2], [1, Fraction(3, 2), 1], [2, 1, Fraction(4, 3)]], True),
    ("zero_margin_rows", [0] * 3, [0] * 2, [[0, 0]] * 3, True),
    ("deterministic_rational", [1], [1], [[Fraction(3, 7)]], False),
    ("unreduced_integer_masses", [2, 2], [2, 2], [[2, 2], [2, 2]], False),
)


def fresh(module, fixture):
    _, rows, columns, activities, factorial = fixture
    return module.ExactWeightedTableSampler(module.TableProblem(rows, columns),
                                            module.ProductWeights(activities, factorial))


def prepare_all(sampler):
    # Benchmark-only eager preparation; production remains lazy on first visit.
    for state, branches in sampler._engine.branches.items():
        if branches:
            sampler._choices[state] = tables._prepare_rational_choice([branch.mass for branch in branches])
    return sampler._choices


def draw_batch(sampler):
    rng = random.Random(SEED)
    for _ in range(DRAWS):
        sampler.sample(rng)


def weighted_benchmarks(old):
    result = []
    for fixture in WEIGHTED:
        name, rows, columns, activities, factorial = fixture
        entry = {"fixture": name, "row_margins": rows, "column_margins": columns,
                 "activities": [[str(x) for x in row] for row in activities], "factorial_weight": factorial}
        samples, traces = [], []
        for label, module in (("baseline", old), ("candidate", tables)):
            sampler = fresh(module, fixture)
            normalizer = sampler.normalizer()
            if label == "candidate":
                assert sampler._choices == {}
            rng = Trace()
            samples.append([sampler.sample(rng) for _ in range(200)])
            traces.append(rng.trace)
            entry[label] = {"normalizer": str(normalizer), "dp_stats": sampler.stats,
                            "sample_sequence_sha256": digest(samples[-1]), "rng_trace_sha256": digest(traces[-1])}
            phases = {key: [] for key in ("normalizer_dp", "first_draw_after_dp", "cold_first_draw")}
            for _ in range(REPETITIONS):
                sampler = fresh(module, fixture)
                phases["normalizer_dp"].append(elapsed(sampler.normalizer))
                rng = random.Random(SEED)
                phases["first_draw_after_dp"].append(elapsed(lambda: sampler.sample(rng)))
                rng = random.Random(SEED)
                phases["cold_first_draw"].append(elapsed(lambda: fresh(module, fixture).sample(rng)))
            entry[label].update({key: summarize(spans) for key, spans in phases.items()})
        assert samples[0] == samples[1] and traces[0] == traces[1]
        assert entry["baseline"]["normalizer"] == entry["candidate"]["normalizer"]
        assert entry["baseline"]["dp_stats"] == entry["candidate"]["dp_stats"]
        entry["exact_200_samples_and_rng_stop_value_pairs_match"] = True
        entry["rng_calls_in_200_samples"] = len(traces[0])
        preparation = []
        for _ in range(REPETITIONS):
            prepared = fresh(tables, fixture)
            prepared.normalizer()
            preparation.append(elapsed(lambda: prepare_all(prepared)))
        unprepared = fresh(tables, fixture)
        unprepared.normalizer()
        cache_memory = allocations(lambda: prepare_all(unprepared))
        plans = prepared._choices
        entry["candidate_complete_cache"] = {
            "preparation": summarize(preparation), "plans": len(plans),
            "cumulative_integers": sum(map(len, plans.values())),
            "integer_bits": sum(x.bit_length() for plan in plans.values() for x in plan),
            "dictionary_and_plan_tuple_shallow_bytes": sys.getsizeof(plans) + sum(sys.getsizeof(plan) for plan in plans.values()),
            "unique_cumulative_integer_object_bytes": sum(sys.getsizeof(x) for x in {id(x): x for plan in plans.values() for x in plan}.values()),
            "incremental_allocations_after_completed_dp": cache_memory,
        }
        warmed_old = fresh(old, fixture)
        warmed_old.normalizer()
        for label, sampler in (("baseline", warmed_old), ("candidate", prepared)):
            entry[label]["warm_2000_draws"] = measure(lambda: draw_batch(sampler))
        result.append(entry)
    return result


def graph_kernel(module, size):
    matrix = tuple(tuple(Fraction(int(j == (i + 1) % size)) for j in range(size)) for i in range(size))
    return module.ExactKernel(tuple(((i,),) for i in range(size)), matrix, (Fraction(1, size),) * size)


def scc_benchmarks(old, oracle):
    for bits in range(512):
        matrix = tuple(tuple(Fraction((bits >> (3 * i + j)) & 1) for j in range(3)) for i in range(3))
        states = tuple(((i,),) for i in range(3))
        expected = oracle(matrix)
        for module in (old, kernels):
            assert module.ExactKernel(states, matrix, (0, 0, 1)).communicating_classes() == expected
    result = []
    for size in (64, 128, 256):
        entry = {"fixture": "directed_cycle_dense_fraction_matrix", "states": size, "exact_classes_match": True}
        for label, module in (("baseline", old), ("candidate", kernels)):
            kernel = graph_kernel(module, size)
            assert kernel.communicating_classes() == (tuple(range(size)),)
            entry[label] = {
                "input_setup_excluded": measure(kernel.communicating_classes),
                "input_setup_included": measure(lambda: graph_kernel(module, size).communicating_classes()),
                "allocations_input_setup_excluded": allocations(kernel.communicating_classes),
            }
        result.append(entry)
    return {"all_512_three_vertex_digraphs_match_independent_oracle": True, "fixtures": result}


def heat_fixture(module, table_module, name):
    if name in ("uniform_2x2_30", "uniform_2x2_120", "weighted_2x2_30", "empty_catalog"):
        margin = 120 if name.endswith("120") else 30
        problem = table_module.TableProblem([margin] * 2, [margin] * 2)
        weights = (table_module.ProductWeights([[Fraction(2, 3), 1], [1, Fraction(3, 2)]], True)
                   if name.startswith("weighted") else None)
    elif name == "weighted_capped_overlapping":
        problem = table_module.TableProblem([6, 6], [4] * 3, [[4, 3, 4], [4, 4, 4]], [[0, 0, 1], [0, 0, 0]])
        weights = table_module.ProductWeights([[0, Fraction(2, 3), 3], [2, 1, 5]], True)
    elif name == "structural_zero_six_cycle":
        problem = table_module.TableProblem([1] * 3, [1] * 3, structural_zeros=[(0, 2), (1, 0), (2, 1)])
        weights = table_module.ProductWeights([[1, 2, 1], [1, 3, 4], [5, 1, 2]], True)
    elif name == "singleton_line":
        problem = table_module.TableProblem([1, 1], [1, 1], lower_bounds=[[1, 0], [0, 1]])
        weights = None
    else:
        raise ValueError(name)
    states = tuple(table_module.ExactTableSampler(problem).tables())
    cycles = () if name == "empty_catalog" else module.simple_cycles(problem)
    choices = tuple(Fraction(i + 1, len(cycles) * (len(cycles) + 1) // 2) for i in range(len(cycles)))
    return problem, states, cycles, {"weights": weights, "cycle_probabilities": choices, "hold_probability": Fraction(1, 7)}


def build(module, inputs):
    problem, states, cycles, options = inputs
    return module.heat_bath_kernel(problem, states, cycles, **options)


def heat_benchmarks(old, old_tables, oracle):
    result = []
    names = ("uniform_2x2_30", "uniform_2x2_120", "weighted_2x2_30", "weighted_capped_overlapping",
             "structural_zero_six_cycle", "empty_catalog", "singleton_line")
    for name in names:
        entry, outputs = {"fixture": name}, []
        for label, module, table_module in (("baseline", old, old_tables), ("candidate", kernels, tables)):
            inputs = heat_fixture(module, table_module, name)
            output = build(module, inputs)
            outputs.append((output.states, output.matrix, output.stationary))
            entry.update({"states": len(output.states), "cycles": len(inputs[2])})
            entry[label] = {
                "input_setup_excluded": measure(lambda: build(module, inputs)),
                "input_setup_included": measure(lambda: build(module, heat_fixture(module, table_module, name))),
                "allocations_input_setup_excluded": allocations(lambda: build(module, inputs)),
            }
            counts = {"shift_calls": 0, "line_interval_calls": 0}
            def counted(key, function):
                def call(*args):
                    counts[key] += 1
                    return function(*args)
                return call
            with patch.object(module, "_shift", counted("shift_calls", module._shift)), \
                    patch.object(module, "line_interval", counted("line_interval_calls", module.line_interval)):
                build(module, inputs)
            entry[label]["operation_counts"] = counts
        problem, states, cycles, options = inputs
        matrix, stationary = oracle(states, cycles, options["weights"], options["cycle_probabilities"], options["hold_probability"])
        assert outputs[0] == outputs[1] == (states, matrix, stationary)
        entry["exact_states_matrix_stationary_match_baseline_and_independent_oracle"] = True
        result.append(entry)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / ".local/reports/implementation-benchmarks.json")
    args = parser.parse_args()
    baseline, baseline_hashes = load_baseline()
    spec = importlib.util.spec_from_file_location("_kernel_benchmark_oracles", ROOT / "tests/test_kernels.py")
    oracles = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracles)
    paths = ("src/contingency115/tables.py", "src/contingency115/kernels.py",
             "tests/test_kernels.py", "experiments/implementation_benchmarks.py")
    result = {
        "schema_version": 1, "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "baseline_commit": BASELINE, "baseline_source_sha256": baseline_hashes,
        "candidate_and_reproduction_sha256": {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in paths},
        "environment": {"python_version": platform.python_version(), "os": platform.system(),
                        "os_release": platform.release(), "architecture": platform.machine()},
        "repetitions": REPETITIONS, "seed": SEED, "warmed_draws_per_repetition": DRAWS,
        "boundaries": {
            "baseline": "Both baseline tables and kernels loaded from pinned Git sources under an isolated in-memory package; candidate modules are current checkout sources.",
            "weighted": "DP excludes sampler/problem/weights construction and feasibility. First after DP excludes completed DP and RNG creation, includes lazy visited-plan preparation. Cold first draw includes construction, feasibility, DP and visited plans, excludes RNG creation. Warm 2000 draws include RNG creation but exclude DP/all-plan preparation. Complete cache preparation excludes completed DP and is benchmark-only eager work.",
            "scc": "Excluded input setup uses preconstructed states and dense matrix; included constructs them. Adjacency construction is always timed. There is no persistent prepared/warm SCC cache.",
            "heat": "Excluded input setup uses preconstructed problem/weights/fiber/catalog; included constructs them. Both include validation, complete-fiber DP count, masses, dense matrix and exact stochasticity/balance assertions. Cycle-line reuse occurs within one construction; repeated calls do not retain it.",
            "memory": "Separate single tracemalloc runs, never during timing: Python allocations only, excludes prebuilt inputs and native/RSS allocations, returned output retained. Weighted cache allocations start after completed DP and an empty cache. Shallow dictionary/tuple sizes exclude existing DP state keys; unique integer object sizes include shared/interned integers and are object footprint, not incremental allocations. Integer-bit payload is separately reported.",
            "oracle": "Only Boolean closure and independent pairwise-line/rational-weight oracle functions from tests/test_kernels.py are reused; no test suite runs. Trace/sample SHA256 covers compact JSON of integer arrays, with equality also checked directly.",
            "limitations": "Three bounded repetitions with uncontrolled machine load, including noise-scale first-draw/no-reuse cases. Fixture-specific reference-implementation results; dense storage and rational bit costs remain. No formal sampler runtime, mixing, accuracy, release-wide or human-review claim.",
        },
        "weighted_draw_cache": weighted_benchmarks(baseline["tables"]),
        "communicating_classes": scc_benchmarks(baseline["kernels"], oracles.reachability_classes),
        "heat_bath_lines": heat_benchmarks(baseline["kernels"], baseline["tables"], oracles.direct_heat_bath),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print("Exact comparisons passed; results written to the requested output.")


if __name__ == "__main__":
    main()
