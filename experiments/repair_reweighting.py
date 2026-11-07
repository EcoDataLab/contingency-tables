"""Exact finite checks for repair-based output from the all-small chain.

Scaled repair rejection retains the original chain. Inverse-fiber MH is a
separate alternative. Neither changes the compiled sampler. Exhaustive matrix
construction is a diagnostic, not a scalable sampler implementation.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
import hashlib
from itertools import product
import json
from pathlib import Path

from contingency115.ideal_chain import build_rescaled_ideal_chain
from contingency115.tables import TableProblem

ROOT = Path(__file__).resolve().parents[1]


def repair(state, columns):
    result = list(state.row_view)
    if not state.balanced:
        s, t = state.defect_labels()
        result[t] -= 1
        result[(t // columns) * columns + s % columns] += 1
    return tuple(result)


def compositions(total, length):
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, length - 1):
                yield (first,) + rest


def independent_states(rows, columns):
    """Enumerate row compositions and ordered defect labels, without DP."""
    m, n = len(rows), len(columns)
    found = set()
    for row_parts in product(*(tuple(compositions(r, n)) for r in rows)):
        x = tuple(v for row in row_parts for v in row)
        candidates = {x}
        for s in range(m * n):
            for t in range(m * n):
                if s != t and x[t]:
                    q = list(x)
                    q[s] += 1
                    q[t] -= 1
                    candidates.add(tuple(q))
        for q in candidates:
            if all(sum(q[i * n + j] for i in range(m)) == columns[j]
                   for j in range(n)):
                found.add((x, q))
    return found


def reweighted(chain):
    """Return repairs, fiber sizes, normalized weights and an exact MH matrix."""
    m, n = chain.problem.shape
    if not m or not n or any(v <= 0 or v >= chain.U for v in
                            chain.problem.row_sums + chain.problem.column_sums):
        raise ValueError("requires nonempty positive margins strictly below U")
    if not chain.all_small or any(w != 1 for w in chain.completion_counts):
        raise ValueError("requires the ordinary unit-weight all-small chain")
    repaired = tuple(repair(state, n) for state in chain.states)
    loads = tuple(1 + (m * n - 1) * sum(v > 0 for v in table)
                  for table in repaired)
    count = len(set(repaired))
    stationary = tuple(F(1, count * load) for load in loads)
    matrix = []
    for i, row in enumerate(chain.matrix):
        new = [F(0) if i == j else value * min(F(1), F(loads[i], loads[j]))
               for j, value in enumerate(row)]
        new[i] = 1 - sum(new)
        matrix.append(tuple(new))
    return repaired, loads, stationary, tuple(matrix)


def verify(chain, repaired, loads, stationary, matrix):
    """Exact probability, repair-law and pointwise gap-comparison checks."""
    size, count = len(chain.states), len(set(repaired))
    assert len(loads) == len(stationary) == len(matrix) == size
    observed = Counter(repaired)
    assert all(observed[a] == ell for a, ell in zip(repaired, loads))
    assert sum(stationary) == 1 and all(w > 0 for w in stationary)
    output = defaultdict(F)
    lower = F(size, count * max(loads))
    upper = F(size, count * min(loads))
    for i, row in enumerate(matrix):
        assert len(row) == size and sum(row) == 1
        assert min(row) >= 0 and row[i] >= F(1, 2)
        assert lower * chain.stationary[i] <= stationary[i] <= upper * chain.stationary[i]
        output[repaired[i]] += stationary[i]
        for j, value in enumerate(row):
            assert stationary[i] * value == stationary[j] * matrix[j][i]
            if i != j:
                assert (value > 0) == (chain.matrix[i][j] > 0)
                assert stationary[i] * value >= lower * chain.stationary[i] * chain.matrix[i][j]
    assert set(output.values()) == {F(1, count)}
    return lower, upper


def numerical_gaps(chain, stationary, matrix):
    """Optional floating eigenvalues; remove beta before diagonalization."""
    import numpy as np

    def gap(weights, transition):
        # Similarity of I-P to a symmetric matrix avoids subtracting a tiny
        # spectral gap from one after computing the eigenvalues.
        w = np.sqrt(np.array([float(v) for v in weights]))
        laplacian = np.array([[float(((i == j) - v) / chain.beta)
                              for j, v in enumerate(row)]
                             for i, row in enumerate(transition)])
        symmetric = w[:, None] * laplacian / w[None, :]
        return float(np.linalg.eigvalsh(symmetric)[1]) if len(w) > 1 else None

    return {"evidence": "floating-point diagnostic, not an exact spectral certificate",
            "old_gap_divided_by_beta": gap(chain.stationary, chain.matrix),
            "new_gap_divided_by_beta": gap(stationary, matrix)}


def case(rows, columns, *, spectral=False):
    chain = build_rescaled_ideal_chain(TableProblem(rows, columns),
                                      U=max(rows + columns) + 1, L=1)
    repaired, loads, stationary, matrix = reweighted(chain)
    lower, upper = verify(chain, repaired, loads, stationary, matrix)
    assert {(s.row_view, s.column_view) for s in chain.states} == independent_states(rows, columns)
    m, n = len(rows), len(columns)
    p, total, count = m * n, sum(rows), len(set(repaired))
    # Independently reconstruct each fiber from its base table and all labels.
    expected = {}
    for table in set(repaired):
        expected[(table, table)] = table
        for s in range(p):
            for t in range(p):
                v = (t // n) * n + s % n
                if s != t and table[v]:
                    x, q = list(table), list(table)
                    x[t] += 1
                    x[v] -= 1
                    q[s] += 1
                    q[v] -= 1
                    key = tuple(x), tuple(q)
                    assert key not in expected
                    expected[key] = table
    assert expected == {(s.row_view, s.column_view): a for s, a in zip(chain.states, repaired)}
    rho = F(max(loads), min(loads))
    support_bound = F(1 + (p - 1) * min(p, total), 1 + (p - 1) * max(m, n))
    assert rho <= support_bound <= min(m, n)
    # Negative control: accept a repaired original-stationary draw with 1/ell.
    corrected = defaultdict(F)
    for i, table in enumerate(repaired):
        corrected[table] += chain.stationary[i] / loads[i]
    old_success = F(count, len(chain.states))
    assert set(corrected.values()) == {F(1, len(chain.states))}
    assert sum(corrected.values()) == old_success
    # The useful correction is c/ell, not 1/ell. A computable lower bound c
    # on every fiber increases success without changing the original chain.
    c = 1 + (p - 1) * max(m, n)
    scaled = {a: c * mass for a, mass in corrected.items()}
    scaled_success = sum(scaled.values())
    assert all(F(c, ell) <= 1 for ell in loads)
    assert set(scaled.values()) == {F(c, len(chain.states))}
    assert scaled_success >= 1 / support_bound
    assert {mass / scaled_success for mass in scaled.values()} == {F(1, count)}
    result = {
        "rows": rows, "columns": columns, "cutoff": chain.U, "padding": chain.L,
        "parameter_regime": chain.parameter_regime,
        "tables": count, "physical_states": len(chain.states), "beta": chain.beta,
        "minimum_fiber": min(loads), "maximum_fiber": max(loads),
        "mh_gap_allowance_multiplier": rho, "dimension_only_multiplier_bound": min(m, n),
        "old_balanced_output_success": old_success, "mh_repaired_output_success": F(1),
        "old_law_naive_repair_is_uniform": len(set(loads)) == 1,
        "unscaled_repair_rejection_success": old_success,
        "scaled_repair_rejection": {
            "known_fiber_lower_bound": c,
            "stationary_success": scaled_success,
            "certified_inverse_success_allowance": support_bound,
            "stationary_success_gain_over_balanced_only": c,
            "optimal_success_if_minimum_fiber_known": min(loads) * old_success,
            "chain_and_gap_unchanged": True,
        },
        "measure_ratio_bounds": [lower, upper],
        "independent_state_and_inverse_fiber_match": True,
        "exact_balance_uniform_output_and_energy_comparison": True,
    }
    if m == n == 2 and len(set(rows + columns)) == 1:
        t = rows[0]
        assert all(abs(repaired[i][0] - repaired[j][0]) <= 1
                   for i, adjacent in enumerate(chain.neighbors) for j in adjacent)
        mean = sum(w * a[0] for w, a in zip(stationary, repaired))
        variance = sum(w * (a[0] - mean)**2 for w, a in zip(stationary, repaired))
        assert variance == F(t * (t + 2), 12)
        result["reversible_local_lazy_inverse_gap_lower_bound"] = 4 * variance
        result["repair_coordinate_edge_increment_at_most_one"] = True
    if spectral:
        result["numerical_spectrum"] = numerical_gaps(chain, stationary, matrix)
    return result


def jsonable(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {key: jsonable(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [jsonable(item) for item in value]
    return value


def report(*, spectral=False):
    fixtures = [((t, t), (t, t)) for t in range(1, 7)]
    fixtures += [((2, 2), (2, 1, 1)), ((3, 2), (2, 2, 1)),
                 ((1, 1, 1), (1, 1, 1)), ((1,), (1,)), ((2,), (1, 1))]
    sources = ["experiments/repair_reweighting.py", "src/contingency115/ideal_chain.py"]
    return jsonable({
        "evidence_class": "exact finite checks of a mathematical derivation; not Lean",
        "scope": "ordinary positive margins, every row and column below cutoff",
        "cases": [case(rows, columns, spectral=spectral) for rows, columns in fixtures],
        "limits": ["Changes the terminal output rule; not the existing compiled machine.",
                   "The optional MH alternative changes the chain and worsens its generic gap allowance by rho.",
                   "Scaled repair rejection matches that alternative's leading dimension allowance without changing the chain.",
                   "No complete runtime degree or practical superiority is established.",
                   "Enumeration is exponential; finite checks do not prove the general theorem."],
        "source_sha256": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sources},
    })


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--spectral", action="store_true", help="also compute NumPy eigenvalue diagnostics")
    args = parser.parse_args()
    rendered = json.dumps(report(spectral=args.spectral), indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    else:
        print(rendered, end="")
