#!/usr/bin/env python3
"""Independent finite checks for the #115 review; not a full sampler or Lean proof.

Run: python3 audit115.py --output audit115-results.json
Python 3.10+ and NumPy. All finite combinatorial checks use integers/Fraction;
only the explicitly labeled spectral diagnostics use floating point.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
import json
import math
from pathlib import Path
import platform
import sys
import time

import numpy as np


def ceil_log2(n: int) -> int:
    assert n > 0
    return (n - 1).bit_length()


def ceil_fraction(x: Fraction) -> int:
    return -(-x.numerator // x.denominator)


def log10_integer(x: int) -> float:
    # Keep printing independent of Python's decimal conversion length limit.
    bits = x.bit_length()
    shift = max(0, bits - 52)
    return math.log10(x >> shift) + shift * math.log10(2)


def schedule(d: int, b: int, k: int, localized: bool) -> dict:
    u = d ** 20
    a0 = 2 + 2 * d * (u + 1) ** 2
    tv = u * (u + 1) * a0 if localized else 4 * d * d * (u + 1) ** 6
    gap = 128 * d * d * ((1 + 2 * d * d) * tv + 2)
    trials = 2 * (1 + d * d) * (k + 2)
    walks = gap * (2 * d * b + ceil_log2(trials) + k + 2)
    precision = k + 2 + ceil_log2(trials * (walks + 1))
    # Check base-two upper bounds on each of the three published error terms.
    assert trials // (2 * (1 + d * d)) >= k + 2
    assert walks // gap >= 2 * d * b + ceil_log2(trials) + k + 2
    assert trials * (walks + 1) <= 2 ** (precision - k - 2)
    return {"gap_bound": gap, "trials": trials, "walks": walks,
            "precision": precision}


def budget_checks() -> dict:
    cases = 0
    for d in (14, 19, 22, 40, 100):
        for b in (d, 2 * d, 104, 512):
            if b < d:
                continue
            for k in (1, 8, 20, 100, 501 * d * b + 1):
                old = schedule(d, b, k, False)
                new = schedule(d, b, k, True)
                assert new["gap_bound"] < old["gap_bound"]
                # Exact-correction upper bounds expressed as exponents.
                D = 500 * d * b + 1
                precision = D + d * b
                assert precision - D >= d * b
                assert 500 * d * b - D == -1
                cases += 1
    d = 19  # r=c=(3,3): literal sampling-paper parameters.
    u, padding, total = d ** 20, d ** 12, 6
    c_allowance = total + d * padding + u + 2
    b = d + ceil_log2(c_allowance + 2)
    k = 20
    out = {"checked_parameter_cases": cases,
           "illustration": {"rows": [3, 3], "columns": [3, 3],
                            "d": d, "b": b, "k": k}}
    original = {"trials": d ** 4 * (k + 1),
                "walks": d ** 200 * (k + b) ** 2,
                "precision": d ** 4 * (k + b) ** 2}
    variants = {"published": original,
                "explicit_existing_bound": schedule(d, b, k, False),
                "candidate_localized_bound": schedule(d, b, k, True)}
    out["illustration"]["schedules"] = {
        name: {key: (str(value) if key in ("trials", "precision")
                     else {"log10": log10_integer(value), "bits": value.bit_length()})
               for key, value in vals.items()}
        for name, vals in variants.items()}
    oldD = d ** 6 * b * b
    newD = 500 * d * b + 1
    out["illustration"]["correction"] = {
        "published_D": oldD, "published_k": 2 * oldD,
        "proposed_D": newD, "proposed_k": newD + d * b,
        "accuracy_bits_ratio": (2 * oldD) / (newD + d * b)}
    # Dense schedule: KB=2*(10^5*d^2*K0)^2, K0=4*d^8.
    dense_cases = 0
    for d in (14, 19, 40):
        KB = 2 * (10 ** 5 * d ** 2 * (4 * d ** 8)) ** 2
        for h in (1, 20, 1000):
            JD = 64 * (h + 2)
            ell = h + 2 + ceil_log2(JD * (1 + d))
            H = KB * (4 * d ** 5 + ell)
            assert JD // 64 >= h + 2
            assert H // KB - 4 * d ** 5 >= ell
            assert JD * (1 + d) <= 2 ** (ell - h - 2)
            dense_cases += 1
    out["checked_dense_cases"] = dense_cases
    return out


def path_checks() -> dict:
    """Check the cut coefficients implying the candidate path inequality."""
    sequences = cuts = 0
    worst = Fraction(0)
    for length in range(2, 8):
        for z in product(range(1, 6), repeat=length):
            if any(z[j] ** 2 < z[j - 1] * z[j + 1]
                   for j in range(1, length - 1)):
                continue
            sequences += 1
            width = length - 1
            Z = sum(z)
            for j in range(length - 1):
                # Weighted telescoping/Cauchy coefficient on edge j,j+1.
                coeff = Fraction(sum(z[a] * z[b] * (b - a)
                                     for a in range(j + 1)
                                     for b in range(j + 1, length)), Z)
                bound = width * (width + 1) * min(z[j], z[j + 1])
                assert coeff <= bound
                worst = max(worst, coeff / bound)
                cuts += 1
    # A support gap invalidates the positive-interval/log-concavity assumption.
    z_gap = (1, 0, 1)
    assert z_gap[1] ** 2 < z_gap[0] * z_gap[2]
    return {"positive_integer_sequences": sequences, "cut_inequalities": cuts,
            "largest_ratio_coefficient_to_bound": str(worst),
            "support_gap_negative_control": "rejected"}


def integer_leaf_partition(widths: tuple[int, ...]) -> dict:
    """All box-valid clique edges, including states absent after a hard limit."""
    owners = {}
    displays = edges_seen = 0
    for special, capacity in enumerate(widths):
        ordinary = [j for j in range(len(widths)) if j != special]
        for ell in range(1, capacity + 1):
            for choices in product(*(range(widths[j] + 1) for j in ordinary)):
                chosen = dict(zip(ordinary, choices))
                D = []
                for j, cap in enumerate(widths):
                    if j == special:
                        D.extend((ell, cap + 1 - ell))
                    else:
                        D.extend((chosen[j], cap - chosen[j]))
                owner = (special, ell, tuple(chosen[j] for j in range(special)))
                vertices = []
                for coord in range(2 * special, 2 * len(widths)):
                    if D[coord] == 0:
                        continue
                    v = D.copy()
                    v[coord] -= 1
                    if all(0 <= v[t] <= widths[t // 2] for t in range(len(v))):
                        vertices.append(tuple(v))
                displays += 1
                for x, y in combinations(vertices, 2):
                    assert tuple(map(max, zip(x, y))) == tuple(D)
                    edge = tuple(sorted((x, y)))
                    if edge in owners:
                        assert owners[edge] == owner
                        # A recovered complete display also means the same leaf.
                        raise AssertionError("An edge was emitted by two displays")
                    owners[edge] = owner
                    edges_seen += 1
    return {"widths": list(widths), "displays": displays,
            "unique_edges": edges_seen, "cross_owner_collisions": 0}


def binary_leaf_partition(pairs: int, adaptive: bool) -> dict:
    owners = {}
    nodes = 0
    def visit(fixed: dict[int, int]):
        nonlocal nodes
        if len(fixed) == pairs:
            return
        remaining = [j for j in range(pairs) if j not in fixed]
        special = (remaining[sum(fixed.values()) % len(remaining)]
                   if adaptive else remaining[0])
        ordinary = [j for j in remaining if j != special]
        owner = (tuple(sorted(fixed.items())), special)
        nodes += 1
        for choices in product((0, 1), repeat=len(ordinary)):
            D = {2 * j + value for j, value in fixed.items()}
            D.update(2 * j + value for j, value in zip(ordinary, choices))
            D.update((2 * special, 2 * special + 1))
            removable = [a for a in D if a // 2 not in fixed]
            vertices = [tuple(sorted(D - {a})) for a in removable]
            for x, y in combinations(vertices, 2):
                assert set(x) | set(y) == D
                edge = tuple(sorted((x, y)))
                assert edge not in owners, (owner, owners.get(edge))
                owners[edge] = owner
        for choice in (0, 1):
            visit(fixed | {special: choice})
    visit({})
    return {"pairs": pairs, "adaptive": adaptive,
            "contexts": nodes, "unique_edges": len(owners), "collisions": 0}


def compositions(total: int, length: int):
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, length - 1):
            yield (first,) + rest


def small_states(rows: tuple[int, ...], cols: tuple[int, ...], cap: int):
    """Literal all-small feasible profiles, represented as (x,q), q=U-y."""
    m, n = len(rows), len(cols)
    states = set()
    for row_entries in product(*(list(compositions(r, n)) for r in rows)):
        x = tuple(a for row in row_entries for a in row)
        if max(x, default=0) > cap:
            continue
        if all(sum(x[i * n + j] for i in range(m)) == cols[j] for j in range(n)):
            states.add((x, x))
        for positive in range(m * n):
            for negative in range(m * n):
                if positive == negative:
                    continue
                q = list(x)
                q[positive] -= 1
                q[negative] += 1
                if any(a < 0 or a > cap for a in q):
                    continue
                if all(sum(q[i * n + j] for i in range(m)) == cols[j]
                       for j in range(n)):
                    states.add((x, tuple(q)))
    return sorted(states)


def graph_and_heatbath(rows, cols):
    m, n = len(rows), len(cols)
    s = m * n
    cap = max(max(rows), max(cols)) + 1
    states = small_states(rows, cols, cap)
    lookup = {state: j for j, state in enumerate(states)}
    views = [x + tuple(cap - a for a in q) for x, q in states]
    view_lookup = {view: j for j, view in enumerate(views)}
    adjacency = np.zeros((len(states), len(states)), dtype=np.int8)
    for idx, view in enumerate(views):
        for donor in range(2 * s):
            if view[donor] == 0:
                continue
            for receiver in range(2 * s):
                if donor == receiver or view[receiver] == cap:
                    continue
                changed = list(view)
                changed[donor] -= 1
                changed[receiver] += 1
                if tuple(changed) in view_lookup:
                    j = view_lookup[tuple(changed)]
                    adjacency[idx, j] = adjacency[j, idx] = 1
        x, q = states[idx]
        if x != q:
            positive = next(t for t in range(s) if x[t] - q[t] == 1)
            negative = next(t for t in range(s) if x[t] - q[t] == -1)
            receiver = (positive // n) * n + negative % n
            repaired = list(x)
            repaired[positive] -= 1
            repaired[receiver] += 1
            repaired = tuple(repaired)
            j = lookup[(repaired, repaired)]
            adjacency[idx, j] = adjacency[j, idx] = 1
    degree = adjacency.sum(axis=1)
    proposal = Fraction(1, 2 ** ceil_log2(2 * int(degree.max())))
    P = adjacency.astype(float) * float(proposal)
    P[np.diag_indices(len(states))] = 1 - degree * float(proposal)
    cycles = []
    for i, k in combinations(range(m), 2):
        for j, l in combinations(range(n), 2):
            signs = [0] * s
            for cell, sign in ((i * n + j, 1), (k * n + l, 1),
                               (i * n + l, -1), (k * n + j, -1)):
                signs[cell] = sign
            cycles.append(signs)
    H = np.zeros_like(P)
    exact_rows = []
    for idx, (x, q) in enumerate(states):
        exact_row = {}
        for signs in cycles:
            lower, upper = -cap, cap
            for t, sign in enumerate(signs):
                if sign == 1:
                    lower = max(lower, -x[t], -q[t])
                    upper = min(upper, cap - x[t], cap - q[t])
                elif sign == -1:
                    lower = max(lower, x[t] - cap, q[t] - cap)
                    upper = min(upper, x[t], q[t])
            assert lower <= 0 <= upper
            probability = Fraction(1, len(cycles) * (upper - lower + 1))
            for shift in range(lower, upper + 1):
                xx = tuple(a + shift * signs[t] for t, a in enumerate(x))
                qq = tuple(a + shift * signs[t] for t, a in enumerate(q))
                j = lookup[(xx, qq)]
                assert tuple(a - b for a, b in zip(xx, qq)) == tuple(a - b for a, b in zip(x, q))
                exact_row[j] = exact_row.get(j, Fraction(0)) + probability
        assert sum(exact_row.values(), Fraction(0)) == 1
        exact_rows.append(exact_row)
        for j, probability in exact_row.items():
            H[idx, j] = float(probability)
    for i, row in enumerate(exact_rows):
        for j, probability in row.items():
            assert probability == exact_rows[j].get(i, Fraction(0))
    lazy_H = (np.eye(len(states)) + H) / 2
    mixed = (P + lazy_H) / 2
    T = [i for i, (x, q) in enumerate(states) if x == q]
    D = [i for i, (x, q) in enumerate(states) if x != q]
    def diagnostics(K):
        assert np.max(np.abs(K - K.T)) < 1e-12
        assert np.max(np.abs(K.sum(axis=1) - 1)) < 1e-12
        assert np.min(np.diag(K)) >= 0.5 - 1e-12
        eig = np.linalg.eigvalsh(K)
        assert eig[0] >= -1e-12
        gap = float(1 - eig[-2])
        trace = K[np.ix_(T, T)].copy()
        if D:
            trace += K[np.ix_(T, D)] @ np.linalg.solve(
                np.eye(len(D)) - K[np.ix_(D, D)], K[np.ix_(D, T)])
        trace_gap = float(1 - np.linalg.eigvalsh(trace)[-2])
        assert np.max(np.abs(trace.sum(axis=1) - 1)) < 1e-10
        return {"gap": gap, "transversal_trace_gap": trace_gap}
    baseline, candidate = diagnostics(P), diagnostics(mixed)
    assert candidate["gap"] >= baseline["gap"] / 2 - 1e-12
    return {"rows": rows, "columns": cols, "surrogate_uniform_cap": cap,
            "states": len(states), "tables": len(T), "edges": int(degree.sum()) // 2,
            "base_edge_probability": str(proposal),
            "baseline": baseline, "half_heatbath_mixture": candidate,
            "gap_ratio": candidate["gap"] / baseline["gap"],
            "trace_gap_ratio": candidate["transversal_trace_gap"] / baseline["transversal_trace_gap"],
            "exact_heatbath_detailed_balance": True}


def distribution_check() -> dict:
    # This example distinguishes table-uniform from a labeled-person model.
    # Each row contains two people; columns have totals (2,2).
    tables = [((a, 2 - a), (2 - a, a)) for a in range(3)]
    labeled = [Fraction(1, math.prod(math.factorial(x) for row in table for x in row))
               for table in tables]
    Z = sum(labeled, Fraction(0))
    assert [weight / Z for weight in labeled] == [Fraction(1, 6), Fraction(2, 3), Fraction(1, 6)]
    # Row/column-factor weights multiply every table by the same constant.
    alpha, beta = (2, 3), (5, 7)
    gauge = [math.prod((alpha[i] * beta[j]) ** table[i][j]
                       for i in range(2) for j in range(2)) for table in tables]
    assert len(set(gauge)) == 1
    # A non-log-concave unary multiplier breaks the child signature already
    # on the 2x2 example: the three child masses become (1,1,4).
    distorted = (1, 1, 4)
    assert distorted[1] ** 2 < distorted[0] * distorted[2]
    return {"tables": tables, "uniform_probabilities": ["1/3"] * 3,
            "conditional_labeled_probabilities": [str(w / Z) for w in labeled],
            "row_column_gauge_constant": gauge[0],
            "non_log_concave_multiplier_negative_control": list(distorted)}


def counting_inner_checks() -> dict:
    cases = 0
    # Use Fractions to check choices and the base-two Hoeffding upper bound.
    for H in (1, 10, 10000):
        for xi in (Fraction(1, 8), Fraction(1, 1000)):
            for theta in (Fraction(1, 8), Fraction(1, 1000000)):
                sigma = xi / (50 * (H + 1))
                M = ceil_fraction(8 * (H + 1) / theta)
                L = ceil_log2(M)
                N = ceil_fraction(1024 * L / sigma ** 2)
                # Each worst-range observable: relative tail <= 2 exp(-2N*sigma^2/961).
                # ln(2)<=1 allows the following dyadic upper bound, then union.
                exponent = 2 * N * sigma ** 2 / 961
                assert exponent >= L
                assert 2 * (H + 1) <= theta * (2 ** L) / 4
                Q = 3 * (H + 1) * N  # illustrative d=2: d+1=3
                ell = ceil_log2(ceil_fraction(8 * Q / theta))
                assert Q <= theta * (2 ** ell) / 8
                cases += 1
    return {"checked_cases": cases,
            "sample_formula": "ceil(1024*sigma^(-2)*ceil_log2(ceil(8*(H+1)/theta)))",
            "walk_formula": "ceil(K_bin*(H+d*B+ceil_log2(ceil(8*Q_in/theta))))"}


def weighted_local_transport(rows, cols, cap=2, padding=2) -> dict:
    """Exhaust actual 2x2 dense completions, then test every local mean contrast.

    Thresholds/padding are small surrogate values; this isolates proof lemmas,
    without pretending to execute the enormous published parameter schedule.
    """
    m, n = len(rows), len(cols)
    I = [i for i, r in enumerate(rows) if r >= cap]
    J = [j for j, c in enumerate(cols) if c >= cap]
    assert len(I) == len(J) == 2
    cells = [(i, j) for i in range(m) for j in range(n) if i not in I or j not in J]
    s = len(cells)
    weighted = {}
    for x in product(range(cap + 1), repeat=s):
        R = [rows[i] - sum(x[t] for t, (a, _) in enumerate(cells) if a == i)
             for i in range(m)]
        if any(r < 0 or (i not in I and r != 0) for i, r in enumerate(R)):
            continue
        q_candidates = [x]
        for positive, negative in product(range(s), repeat=2):
            if positive == negative:
                continue
            q = list(x)
            q[positive] -= 1
            q[negative] += 1
            if all(0 <= a <= cap for a in q):
                q_candidates.append(tuple(q))
        for q in q_candidates:
            C = [cols[j] - sum(q[t] for t, (_, b) in enumerate(cells) if b == j)
                 for j in range(n)]
            if any(c < 0 or (j not in J and c != 0) for j, c in enumerate(C)):
                continue
            rr = [R[i] + len(J) * padding for i in I]
            cc = [C[j] + len(I) * padding for j in J]
            if sum(rr) != sum(cc):
                continue
            lower, upper = max(0, rr[0] - cc[1]), min(rr[0], cc[0])
            weight = max(0, upper - lower + 1)
            if weight:
                weighted[(x, q)] = weight
    states = sorted(weighted)
    lookup = {state: i for i, state in enumerate(states)}
    weights = np.array([weighted[state] for state in states], dtype=float)
    local_laplacians = {}
    unit_edges = 0
    adjusted_edges = 0
    max_adjustment = max_adjustment_support = 0
    def check_adjustment(state, target):
        nonlocal adjusted_edges, max_adjustment, max_adjustment_support
        x, q = state
        xx, qq = target
        dr = [-sum(xx[t] - x[t] for t, (a, _) in enumerate(cells) if a == i) for i in I]
        dc = [-sum(qq[t] - q[t] for t, (_, b) in enumerate(cells) if b == j) for j in J]
        assert sum(dr) == sum(dc)
        matrix = [[0] * len(J) for _ in I]
        for i in range(1, len(I)):
            matrix[i][0] = dr[i]
        for j in range(1, len(J)):
            matrix[0][j] = dc[j]
        matrix[0][0] = dr[0] - sum(dc[1:])
        values = [a for row in matrix for a in row]
        assert max(map(abs, values)) <= 1
        assert sum(a != 0 for a in values) <= 3
        adjusted_edges += 1
        max_adjustment = max(max_adjustment, max(map(abs, values)))
        max_adjustment_support = max(max_adjustment_support, sum(a != 0 for a in values))
    for i, (x, q) in enumerate(states):
        if x != q:
            positive = next(t for t in range(s) if x[t] - q[t] == 1)
            negative = next(t for t in range(s) if x[t] - q[t] == -1)
            receiver = (cells[positive][0], cells[negative][1])
            repaired = list(x)
            repaired[positive] -= 1
            if receiver in cells:
                repaired[cells.index(receiver)] += 1
            repaired = tuple(repaired)
            assert (repaired, repaired) in weighted
            assert weighted[(repaired, repaired)] >= weighted[(x, q)]
            check_adjustment((x, q), (repaired, repaired))
        v = tuple(a for pair in zip(x, (cap - a for a in q)) for a in pair)
        for j in range(i + 1, len(states)):
            xx, qq = states[j]
            w = tuple(a for pair in zip(xx, (cap - a for a in qq)) for a in pair)
            if sum(abs(a - b) for a, b in zip(v, w)) != 2:
                continue
            unit_edges += 1
            check_adjustment((x, q), (xx, qq))
            D = tuple(max(a, b) for a, b in zip(v, w))
            occupancies = [D[2 * t] + D[2 * t + 1] for t in range(s)]
            special = [t for t, a in enumerate(occupancies) if a == cap + 1]
            if len(special) != 1 or any(a != cap for t, a in enumerate(occupancies)
                                       if t != special[0]):
                continue
            t = special[0]
            owner = (t, D[2 * t], tuple(D[2 * u] for u in range(t)))
            L = local_laplacians.setdefault(owner, np.zeros((len(states), len(states))))
            conductance = min(weights[i], weights[j])
            L[i, i] += conductance
            L[j, j] += conductance
            L[i, j] -= conductance
            L[j, i] -= conductance
    tested = 0
    worst = 0.0
    d = 10 + (m + 1) * (n + 1)
    A0 = 2 + 2 * d * (cap + 1) ** 2
    for t in range(s):
        prefixes = {x[:t] for x, q in states if x == q}
        for prefix in prefixes:
            children = [[i for i, (x, q) in enumerate(states)
                         if x == q and x[:t] == prefix and x[t] == a]
                        for a in range(cap + 1)]
            masses = [int(sum(weights[i] for i in child)) for child in children]
            positive = [a for a, z in enumerate(masses) if z > 0]
            assert positive == list(range(min(positive), max(positive) + 1))
            assert all(masses[a] ** 2 >= masses[a - 1] * masses[a + 1]
                       for a in range(1, cap))
            for ell in range(1, cap + 1):
                zm, zp = masses[ell - 1], masses[ell]
                if not zm or not zp:
                    continue
                a = np.zeros(len(states))
                a[children[ell - 1]] = weights[children[ell - 1]] / zm
                a[children[ell]] = -weights[children[ell]] / zp
                L = local_laplacians[(t, ell, prefix)]
                eigenvalues, vectors = np.linalg.eigh(L)
                positive_eigen = eigenvalues > 1e-10
                projection = vectors[:, positive_eigen].T @ a
                assert np.linalg.norm(a - vectors[:, positive_eigen] @ projection) < 1e-9
                ratio = min(zm, zp) * float(np.sum(projection ** 2 / eigenvalues[positive_eigen]))
                assert ratio <= A0 + 1e-8
                worst = max(worst, ratio)
                tested += 1
    return {"rows": rows, "columns": cols, "surrogate_cap": cap, "padding": padding,
            "small_cells": cells, "states": len(states), "unit_edges": unit_edges,
            "completion_weight_range": [int(min(weights)), int(max(weights))],
            "tested_positive_adjacent_contrasts": tested,
            "largest_min_mass_times_effective_resistance": worst,
            "candidate_A0": A0,
            "checked_completion_adjustments": adjusted_edges,
            "largest_adjustment_entry": max_adjustment,
            "largest_adjustment_support": max_adjustment_support,
            "arithmetic": "integer enumeration, float64 eigenanalysis for contrasts"}


def reduced_scales_checks() -> dict:
    cases = []
    for d in (14, 19, 22, 40, 100):
        B, A, L = 16 * d ** 3, 16 * d ** 2, 64 * d ** 3
        U = 8 * L * d ** 4
        assert L >= 2 * B and L >= 4 * d
        assert B >= 8 * d ** 3
        assert A * d <= B
        assert Fraction(2 * d * d, A) + Fraction(2 * d ** 3, B) <= Fraction(1, 4)
        assert Fraction(12 * d ** 3, L) < Fraction(1, 2)
        assert Fraction(4 * L * d ** 4, U) <= Fraction(1, 2)
        K0 = 4 * B
        KB = 2 * (10 ** 5 * d * d * K0) ** 2
        a0 = 2 + 2 * d * (U + 1) ** 2
        K = 128 * d * d * ((1 + 2 * d * d) * U * (U + 1) * a0 + 2)
        cases.append({"d": d, "B": B, "A": A, "L": L, "U": U,
                      "dense_KB_log10": log10_integer(KB),
                      "localized_small_K_log10": log10_integer(K)})
    # Generic residual-mixture identity with deliberately biased dyadic laws.
    residual_cases = 0
    for M in range(1, 13):
        bound_exponent = ceil_log2(M)
        D = 4 + bound_exponent
        k = D + bound_exponent
        R = k + bound_exponent
        numerators = [2 ** R // M] * M
        numerators[-1] += 2 ** R - sum(numerators)
        p = [Fraction(a, 2 ** R) for a in numerators]
        tv = sum(abs(a - Fraction(1, M)) for a in p) / 2
        assert tv <= Fraction(1, 2 ** k)
        residual = [2 ** (R + D) - M * (2 ** D - 1) * a for a in numerators]
        assert min(residual) >= 0 and sum(residual) == M * 2 ** R
        delta = Fraction(1, 2 ** D)
        assert all((1 - delta) * p[i] + delta * Fraction(residual[i], M * 2 ** R)
                   == Fraction(1, M) for i in range(M))
        residual_cases += 1
    return {"sufficient_inequality_cases": cases,
            "exact_residual_mixture_cases": residual_cases,
            "status": "candidate joint parameter reanalysis; not a Lean build"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("audit115-results.json"))
    args = parser.parse_args()
    start = time.perf_counter()
    out = {"reviewed_commit": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
           "environment": {"python": platform.python_version(), "numpy": np.__version__},
           "scope": "Independent finite checks; no full sampler, full FPRAS, or Lean build"}
    out["error_budgets"] = budget_checks()
    out["log_concave_path"] = path_checks()
    out["integer_leaf_partitions"] = [integer_leaf_partition(widths) for widths in
                                       ((2,), (2, 2), (2, 2, 2), (3, 3, 3), (2, 2, 2, 2), (2, 3, 2))]
    out["binary_leaf_partitions"] = [binary_leaf_partition(p, adaptive)
                                      for p in range(2, 7) for adaptive in (False, True)]
    out["spectral_diagnostics"] = [graph_and_heatbath(rows, cols) for rows, cols in
                                   (((2, 2), (2, 2)), ((3, 3), (3, 3)),
                                    ((4, 4), (4, 4)), ((3, 3), (2, 2, 2)),
                                    ((4, 3), (2, 3, 2)))]
    out["distribution_negative_controls"] = distribution_check()
    out["counting_inner_budgets"] = counting_inner_checks()
    out["weighted_local_transport"] = [weighted_local_transport(rows, cols) for rows, cols in
                                        (((2, 5), (2, 4, 1)), ((3, 3, 1), (3, 3, 1)),
                                         ((3, 4, 1), (2, 5, 1)))]
    out["reduced_scales"] = reduced_scales_checks()
    out["elapsed_seconds"] = time.perf_counter() - start
    args.output.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({"output": str(args.output),
                      "parameter_cases": out["error_budgets"]["checked_parameter_cases"],
                      "path_sequences": out["log_concave_path"]["positive_integer_sequences"],
                      "integer_leaf_edges": sum(x["unique_edges"] for x in out["integer_leaf_partitions"]),
                      "spectral_instances": len(out["spectral_diagnostics"]),
                      "elapsed_seconds": out["elapsed_seconds"]}, indent=2))


if __name__ == "__main__":
    main()
