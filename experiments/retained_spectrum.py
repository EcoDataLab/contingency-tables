"""Exact finite certificates for the retained-correction path inequality.

This checks abstract finite paths, not physical transport, a sampler's mixing,
or runtime. Every matrix operation uses Fraction; no eigenvalue fit, NumPy,
SciPy, or linear-programming dependency is used.
"""

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path


EPSILONS = (F(1, 3), F(1, 30), F(1, 300000))


@dataclass(frozen=True)
class Case:
    name: str
    family: str
    weights: tuple[int, ...]
    correction: tuple[F, ...]
    cap: int


def constant_cap_case(weights, cap, exterior=0):
    weights = tuple(weights)
    correction = [F(exterior)]
    correction.extend(F(cap * max(a, b)) for a, b in zip(weights, weights[1:]))
    correction.append(F(exterior))
    return weights, tuple(correction), cap


def fixed_cases():
    """150 fixed cases in eight families, including genuinely zero Xi edges."""
    cases = []

    def add(family, weights, correction, cap):
        name = f"{family}-{len(cases) + 1:03d}"
        cases.append(Case(name, family, tuple(weights), tuple(map(F, correction)), cap))

    for n in range(1, 9):
        for cap in (0, 1, 4):
            add("uniform", *constant_cap_case([1] * (n + 1), cap))
    for n in range(1, 9):
        for ratio in (2, 3):
            for reverse in (False, True):
                weights = [ratio ** i for i in range(n + 1)]
                if reverse:
                    weights.reverse()
                for cap in (0, 2):
                    family = "geometric_descending" if reverse else "geometric_ascending"
                    add(family, *constant_cap_case(weights, cap))
    for n in range(2, 9):
        for cap in (0, 1, 4):
            weights = [2 ** min(i, n - i) for i in range(n + 1)]
            add("geometric_tent", *constant_cap_case(weights, cap))
    for n in range(2, 9):
        for cap in (0, 1, 4):
            weights = [1 + min(i, n - i) for i in range(n + 1)]
            add("linear_tent", *constant_cap_case(weights, cap))
    for n in range(1, 9):
        # At N=1 both exterior terms enter the same edge. For larger N,
        # each exterior term makes its nearest edge's Xi exactly zero.
        exterior = 2 if n == 1 else 3
        add("zero_resistance_boundary", *constant_cap_case([1] * (n + 1), 1, exterior))
    for n in range(1, 9):
        add("nonzero_exterior", *constant_cap_case([1] * (n + 1), 2, 3))
    for weights in ((1, 2), (2, 1), (1, 2, 3), (3, 2, 1)):
        # K=0 and all interior c=0; a nonzero unbounded exterior c makes
        # the first Xi zero without relying on equal adjacent weights.
        a, b = weights[:2]
        correction = [F(a) + F(a * a, b)] + [F(0)] * len(weights)
        add("unequal_zero_resistance", weights, correction, 0)
    assert len(cases) == 150
    return cases


def retained_resistances(case):
    z, c, cap = case.weights, case.correction, case.cap
    n = len(z) - 1
    assert n >= 1 and len(c) == n + 2
    assert min(z) > 0 and min(c) >= 0 and cap >= 0
    mode = max(range(n + 1), key=lambda i: z[i])
    assert list(z[:mode + 1]) == sorted(z[:mode + 1])
    assert list(z[mode:]) == sorted(z[mode:], reverse=True)
    xis = []
    for ell in range(1, n + 1):
        a, b = z[ell - 1:ell + 1]
        assert c[ell] <= cap * max(a, b)
        xi = (F(1, a) + F(1, b) + 2 * c[ell] / (a * b)
              - c[ell - 1] / (a * a) - c[ell + 1] / (b * b))
        assert xi >= 0
        xis.append(xi)
    return tuple(xis), mode


def comparison_matrix(weights, xis, cap, epsilon):
    """C L - V, with unordered-edge energy and unnormalized variance.

    L is the path Laplacian with conductance 1/(Xi+epsilon).
    V=diag(z)-zz^T/Z is exactly the weighted centered-variance matrix.
    """
    n, total = len(xis), sum(weights)
    coefficient = F(n * (n + 1) + 2 * cap) + epsilon * n * total / 4
    matrix = [[F(a * b, total) - (a if i == j else 0)
               for j, b in enumerate(weights)] for i, a in enumerate(weights)]
    for ell, xi in enumerate(xis, start=1):
        conductance = coefficient / (xi + epsilon)
        matrix[ell - 1][ell - 1] += conductance
        matrix[ell][ell] += conductance
        matrix[ell - 1][ell] -= conductance
        matrix[ell][ell - 1] -= conductance
    assert all(matrix[i][j] == matrix[j][i]
               for i in range(n + 1) for j in range(n + 1))
    assert all(sum(row) == 0 for row in matrix)
    return matrix, coefficient


def exact_psd_rank(matrix):
    """Exact symmetric Schur complements; return None for a non-PSD matrix.

    A zero pivot of a PSD matrix must have zero remaining row. Positive
    pivots permit congruence reduction to the trailing Schur complement.
    Consequently these checks constitute an exact PSD certificate.
    """
    work = [list(map(F, row)) for row in matrix]
    size = len(work)
    assert all(len(row) == size for row in work)
    assert all(work[i][j] == work[j][i] for i in range(size) for j in range(size))
    rank = 0
    for i in range(size):
        pivot = work[i][i]
        if pivot < 0:
            return None
        if pivot == 0:
            if any(work[i][j] != 0 for j in range(i + 1, size)):
                return None
            continue
        rank += 1
        for j in range(i + 1, size):
            for k in range(j, size):
                work[j][k] -= work[i][j] * work[i][k] / pivot
                work[k][j] = work[j][k]
    return rank


def run():
    if not __debug__:
        raise RuntimeError("run without -O so the exact checks remain enabled")
    # These independent negative controls reject both negative pivots and
    # an indefinite zero-pivot matrix; the actual comparisons are PSD.
    negative_controls = (((-1,),), ((1, 2), (2, 1)), ((0, 1), (1, 0)))
    assert all(exact_psd_rank(matrix) is None for matrix in negative_controls)
    cases = fixed_cases()
    catalog, witnesses, canonical_inputs = [], [], []
    family_counts = Counter()
    orders = Counter()
    zero_cases = exterior_cases = zero_edges = certificates = 0
    witnessed = set()
    for case in cases:
        xis, mode = retained_resistances(case)
        n, total = len(xis), sum(case.weights)
        family_counts[case.family] += 1
        zeros = [ell for ell, xi in enumerate(xis, start=1) if xi == 0]
        zero_cases += bool(zeros)
        zero_edges += len(zeros)
        exterior_cases += bool(case.correction[0] or case.correction[-1])
        for a, b in zip(case.weights, case.weights[1:]):
            orders["increasing" if a < b else "decreasing" if a > b else "equal"] += 1
        bounds = []
        for epsilon in EPSILONS:
            matrix, coefficient = comparison_matrix(case.weights, xis, case.cap, epsilon)
            rank = exact_psd_rank(matrix)
            assert rank == n, case.name  # The constant vector is the sole zero direction.
            bounds.append({"epsilon": str(epsilon), "coefficient": str(coefficient),
                           "matrix_rank": rank, "matrix_nullity": 1, "psd": True})
            certificates += 1
        inputs = {"id": case.name, "family": case.family, "weights": list(case.weights),
                  "correction": list(map(str, case.correction)), "K": case.cap}
        canonical_inputs.append(inputs)
        catalog.append({"id": case.name, "family": case.family, "N": n, "K": case.cap,
                        "Z": total, "zero_Xi_edges": zeros,
                        "limiting_coefficient": n * (n + 1) + 2 * case.cap,
                        "regularized_certificates": len(bounds)})
        if case.family not in witnessed:
            witnessed.add(case.family)
            witnesses.append({**inputs, "mode": mode, "Xi": list(map(str, xis)),
                              "certificates": bounds})
    assert certificates == 450 and zero_cases > 0 and exterior_cases > 0
    assert orders["increasing"] > 0 and orders["decreasing"] > 0
    digest = hashlib.sha256(json.dumps(canonical_inputs, sort_keys=True,
                                      separators=(",", ":")).encode()).hexdigest()
    return {
        "checks": "passed",
        "scope": "exact abstract finite-path matrix certificates; no physical transport or sampler runtime claim",
        "method": "Fraction arithmetic and exact symmetric Schur-complement PSD checks",
        "normalization": {"variance": "sum_i z_i (h_i - sum_j z_j h_j/Z)^2",
                          "energy": "sum_l (h_(l-1)-h_l)^2/(Xi_l+epsilon), unordered edges once",
                          "comparison_matrix": "[N(N+1)+2K+epsilon*N*Z/4]*L - [diag(z)-zz^T/Z]",
                          "limiting_coefficient": "N(N+1)+2K"},
        "counts": {"cases": len(cases), "regularized_psd_certificates": certificates,
                   "validator_negative_controls": len(negative_controls),
                   "cases_with_zero_Xi": zero_cases, "zero_Xi_edges": zero_edges,
                   "cases_with_nonzero_exterior_c": exterior_cases,
                   "adjacent_mass_orders": dict(sorted(orders.items()))},
        "epsilons": list(map(str, EPSILONS)),
        "families": dict(sorted(family_counts.items())),
        "canonical_inputs_sha256": digest,
        "witnesses": witnesses,
        "case_catalog": catalog,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(".local/reports/retained-spectrum.json"))
    if not __debug__:
        parser.error("run without -O so the exact checks remain enabled")
    args = parser.parse_args()
    report = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"checks": report["checks"], "counts": report["counts"],
                      "output": str(args.output)}))
