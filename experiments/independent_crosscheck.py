"""Independent finite oracles for the reference samplers, kernels and optimizer.

Run from the repository root:
    PYTHONPATH=src python3 experiments/independent_crosscheck.py

The seed and case schedule are fixed. This is a bounded research audit, not a
benchmark, distribution-frequency test, universal proof, or substitute for
the unit tests. Only the standard library and this repository are required.
"""

from __future__ import annotations

import argparse
from dataclasses import replace
from fractions import Fraction
import hashlib
from itertools import combinations, permutations, product
import json
from math import factorial
from pathlib import Path
import random

from contingency115.kernels import heat_bath_kernel, simple_cycles
from contingency115.optimize import (
    InfeasibleFlowError,
    linear_bounds,
    verify_infeasibility,
    verify_optimality,
)
from contingency115.tables import (
    ExactTableSampler,
    ExactWeightedTableSampler,
    InfeasibleTableError,
    ProductWeights,
    TableProblem,
)


SEED = 11520261008
REPRODUCTION_COMMAND = "PYTHONPATH=src python3 experiments/independent_crosscheck.py"
ROOT = Path(__file__).resolve().parents[1]


def brute_tables(problem):
    """Enumerate cells directly; use neither DP branches nor table validation."""
    m, n = problem.shape
    result = []
    ranges = (range(problem.lower_bounds[i][j], problem.upper_bounds[i][j] + 1)
              for i in range(m) for j in range(n))
    for flat in product(*ranges):
        table = tuple(tuple(flat[i * n:(i + 1) * n]) for i in range(m))
        rows = tuple(map(sum, table))
        columns = tuple(sum(table[i][j] for i in range(m)) for j in range(n))
        if rows == problem.row_sums and columns == problem.column_sums:
            result.append(table)
    return result


def cycle_oracle(problem):
    """Enumerate row/column permutations, independently of catalog graph DFS."""
    m, n = problem.shape
    found = set()
    for length in range(2, min(m, n) + 1):
        for row_set in combinations(range(m), length):
            for tail in permutations(row_set[1:]):
                rows = (row_set[0],) + tail
                for columns in permutations(range(n), length):
                    signs = [[0] * n for _ in range(m)]
                    for index, column in enumerate(columns):
                        signs[rows[index]][column] = 1
                        signs[rows[(index + 1) % length]][column] = -1
                    if any(signs[i][j] and not problem.upper_bounds[i][j]
                           for i in range(m) for j in range(n)):
                        continue
                    orientation = next(value for row in signs for value in row if value)
                    found.add(tuple(tuple(orientation * value for value in row) for row in signs))
    return found


def independent_weight(table, activities, factorial_weight):
    """Compute the intended law without calling ProductWeights weight methods."""
    weight = Fraction(1)
    for i, row in enumerate(table):
        for j, value in enumerate(row):
            weight *= activities[i][j] ** value
            if factorial_weight:
                weight /= factorial(value)
    return weight


def run_crosscheck():
    rng = random.Random(SEED)
    counts = {
        "random_constraint_cases": 0,
        "empty_fibers": 0,
        "verified_infeasibility_cuts": 0,
        "verified_optimal_endpoints": 0,
        "altered_bound_certificates_rejected": 0,
        "exact_weighted_kernels": 0,
        "zero_mass_targets": 0,
        "exhaustive_3x3_support_catalogs": 0,
        "complete_4x4_cycles": 0,
    }
    for iteration in range(160):
        m, n = (2, 3) if iteration < 100 else (3, 3)
        lower = tuple(tuple(rng.randrange(2) if iteration % 3 == 0 else 0
                            for _ in range(n)) for _ in range(m))
        upper = tuple(tuple(lower[i][j] + rng.randrange(2 if m == 3 else 3)
                            for j in range(n)) for i in range(m))
        witness = tuple(tuple(rng.randrange(lower[i][j], upper[i][j] + 1)
                              for j in range(n)) for i in range(m))
        rows = list(map(sum, witness))
        columns = [sum(witness[i][j] for i in range(m)) for j in range(n)]
        if iteration % 4 == 0:
            first, second = rng.sample(range(n), 2)
            if columns[first]:
                columns[first] -= 1
                columns[second] += 1
        problem = TableProblem(rows, columns, upper, lower)
        fiber = brute_tables(problem)
        sampler = ExactTableSampler(problem)
        assert sampler.count() == len(fiber)
        assert list(sampler.tables()) == fiber
        costs = tuple(tuple(Fraction(rng.randrange(-7, 8), rng.randrange(1, 5))
                            for _ in range(n)) for _ in range(m))
        try:
            bounds = linear_bounds(problem, costs)
        except InfeasibleTableError as error:
            assert not fiber
            if isinstance(error, InfeasibleFlowError):
                assert verify_infeasibility(problem, error.certificate)
                counts["verified_infeasibility_cuts"] += 1
            counts["empty_fibers"] += 1
        else:
            assert fiber
            values = [sum(costs[i][j] * table[i][j] for i in range(m) for j in range(n))
                      for table in fiber]
            assert bounds.minimum.value == min(values)
            assert bounds.maximum.value == max(values)
            for endpoint in (bounds.minimum, bounds.maximum):
                assert verify_optimality(problem, costs, endpoint.table, endpoint.certificate)
                corrupted = replace(endpoint.certificate, bound=endpoint.value + 1)
                assert not verify_optimality(problem, costs, endpoint.table, corrupted)
                counts["verified_optimal_endpoints"] += 1
                counts["altered_bound_certificates_rejected"] += 1
            activities = tuple(tuple(Fraction(rng.randrange(4), rng.randrange(1, 4))
                                     for _ in range(n)) for _ in range(m))
            factorial_weight = bool(iteration % 2)
            weights = ProductWeights(activities, factorial_weight=factorial_weight)
            weighted = ExactWeightedTableSampler(problem, weights)
            masses = [independent_weight(table, activities, factorial_weight) for table in fiber]
            assert weighted.normalizer() == sum(masses)
            if sum(masses) and len(fiber) <= 30:
                catalog = simple_cycles(problem)
                assert {cycle.signs for cycle in catalog} == cycle_oracle(problem)
                kernel = heat_bath_kernel(problem, fiber, catalog, weights=weights)
                positive = {i for i, probability in enumerate(kernel.stationary) if probability}
                # Null states may have separate SCCs; connectivity is a claim
                # about the positive-support fiber, not these null states.
                classes = [set(component) & positive for component in kernel.communicating_classes()
                           if set(component) & positive]
                assert len(classes) == 1
                for i, table in enumerate(fiber):
                    assert kernel.stationary[i] == masses[i] / sum(masses)
                    assert weighted.probability(table) == masses[i] / sum(masses)
                counts["exact_weighted_kernels"] += 1
            elif not sum(masses):
                counts["zero_mass_targets"] += 1
        counts["random_constraint_cases"] += 1

    for bits in product((0, 1), repeat=9):
        upper = tuple(tuple(bits[3 * i + j] for j in range(3)) for i in range(3))
        problem = TableProblem([3] * 3, [3] * 3, upper)
        assert {cycle.signs for cycle in simple_cycles(problem)} == cycle_oracle(problem)
        counts["exhaustive_3x3_support_catalogs"] += 1
    problem = TableProblem([4] * 4, [4] * 4)
    catalog = simple_cycles(problem)
    assert len(catalog) == 204
    assert {cycle.signs for cycle in catalog} == cycle_oracle(problem)
    counts["complete_4x4_cycles"] = len(catalog)
    source_paths = ["src/contingency115/tables.py", "src/contingency115/kernels.py",
                    "src/contingency115/optimize.py", "experiments/independent_crosscheck.py"]
    return {
        "status": "passed",
        "seed": SEED,
        "reproduction_command": REPRODUCTION_COMMAND,
        "counts": counts,
        "arithmetic": "Python integers and Fraction; no frequency tests or numerical eigensolvers",
        "scope": "Finite independent enumeration and permutation oracles; not a universal proof",
        "source_sha256": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
                          for path in source_paths},
    }


def main():
    if not __debug__:
        raise RuntimeError("This audit uses assertions; run Python without -O")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "reports/independent-crosscheck.json")
    args = parser.parse_args()
    result = run_crosscheck()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "counts": result["counts"]}, indent=2))


if __name__ == "__main__":
    main()
