"""Exact diagnostics for the transport localization argument.

These helpers check finite statements and evaluate conservative constants.
They are not a contingency-table sampler or a formal proof of the source
papers. See docs/transport-localization.md for assumptions and proofs.
"""

from __future__ import annotations

from fractions import Fraction
from math import isqrt
from typing import Callable, Iterable, Mapping, Sequence


def _masses(values: Sequence[int | Fraction]) -> tuple[Fraction, ...]:
    z = tuple(Fraction(value) for value in values)
    if not z or any(value < 0 for value in z) or not any(z):
        raise ValueError("Masses must be nonnegative, with positive total mass")
    return z


def interval_log_concave(values: Sequence[int | Fraction]) -> bool:
    """Require both log-concavity and interval support, including hard zeros."""
    z = _masses(values)
    support = [i for i, value in enumerate(z) if value]
    return (
        support == list(range(support[0], support[-1] + 1))
        and all(z[i] ** 2 >= z[i - 1] * z[i + 1] for i in range(1, len(z) - 1))
    )


def path_cut_coefficients(values: Sequence[int | Fraction]) -> tuple[Fraction, ...]:
    """Exact coefficients after unweighted telescoping and Cauchy--Schwarz.

    Coefficient j is sum_{a<=j<b} z[a] z[b] (b-a) / sum(z).
    No log-concavity hypothesis is needed to calculate these coefficients.
    """
    z = _masses(values)
    total = sum(z)
    left_mass = left_moment = Fraction(0)
    right_mass = total
    right_moment = sum((i * mass for i, mass in enumerate(z)), Fraction(0))
    cuts = []
    for j, mass in enumerate(z[:-1]):
        left_mass += mass
        left_moment += j * mass
        right_mass -= mass
        right_moment -= j * mass
        cuts.append((left_mass * right_moment - left_moment * right_mass) / total)
    return tuple(cuts)


def path_variance(values: Sequence[int | Fraction], h: Sequence[int | Fraction]) -> Fraction:
    """The unnormalized variance sum(z)*(E[h^2]-E[h]^2)."""
    z = _masses(values)
    if len(z) != len(h):
        raise ValueError("Mass and observable lengths differ")
    h = tuple(Fraction(value) for value in h)
    mean = sum((mass * value for mass, value in zip(z, h)), Fraction(0)) / sum(z)
    return sum((mass * (value - mean) ** 2 for mass, value in zip(z, h)), Fraction(0))


def path_uniform_bound(values: Sequence[int | Fraction]) -> int:
    """M(M+1)/2, using the diameter M of the positive support."""
    z = _masses(values)
    if not interval_log_concave(z):
        raise ValueError("An interval-supported log-concave sequence is required")
    support = [i for i, mass in enumerate(z) if mass]
    diameter = support[-1] - support[0]
    return diameter * (diameter + 1) // 2


def integer_leaf_edge_owner(
    x: Sequence[int], y: Sequence[int], widths: Sequence[int],
    order: Sequence[int] | None = None,
) -> tuple[int, int, tuple[tuple[int, int], ...]] | None:
    """Recover (special slot, adjacent level, prefix) or reject a non-leaf edge.

    Coordinates are interleaved as (x_0,y_0,x_1,y_1,...). An ownership
    certificate is combinatorial: it does not assert positive physical weight.
    """
    widths = tuple(widths)
    p = len(widths)
    order = tuple(range(p)) if order is None else tuple(order)
    if sorted(order) != list(range(p)) or any(width < 0 for width in widths):
        raise ValueError("Invalid widths or exposure order")
    x, y = tuple(x), tuple(y)
    if len(x) != 2 * p or len(y) != 2 * p:
        raise ValueError("Each slot needs two coordinates")
    if any(value < 0 or value > widths[k // 2] for v in (x, y) for k, value in enumerate(v)):
        return None
    differences = [k for k in range(2 * p) if x[k] != y[k]]
    if len(differences) != 2 or sorted(x[k] - y[k] for k in differences) != [-1, 1]:
        return None
    display = tuple(max(a, b) for a, b in zip(x, y))
    excess = [display[2 * j] + display[2 * j + 1] - widths[j] for j in range(p)]
    if excess.count(1) != 1 or any(value not in (0, 1) for value in excess):
        return None
    special = excess.index(1)
    index = order.index(special)
    prefix = order[:index]
    if any(k // 2 in prefix for k in differences):
        return None
    return special, display[2 * special], tuple((j, display[2 * j]) for j in prefix)


def binary_leaf_edge_owner(
    x: Iterable[int], y: Iterable[int], pairs: int,
    choose_pair: Callable[[Mapping[int, int]], int],
) -> tuple[tuple[tuple[int, int], ...], int] | None:
    """Recover a node in a deterministic adaptive binary exposure tree.

    Elements of pair j are 2*j and 2*j+1. The callback selects an unassigned
    pair from the fixed partial assignment; it must be deterministic.
    """
    if pairs < 1:
        raise ValueError("At least one pair is required")
    x, y = frozenset(x), frozenset(y)
    if len(x) != pairs or len(y) != pairs or len(x ^ y) != 2:
        return None
    display = x | y
    if any(element < 0 or element >= 2 * pairs for element in display):
        return None
    occupancy = [len(display & {2 * j, 2 * j + 1}) for j in range(pairs)]
    if occupancy.count(2) != 1 or any(value not in (1, 2) for value in occupancy):
        return None
    special = occupancy.index(2)
    fixed: dict[int, int] = {}
    while True:
        selected = choose_pair(dict(fixed))
        if selected in fixed or not 0 <= selected < pairs:
            raise ValueError("Exposure callback must select an unassigned pair")
        if selected == special:
            if any(element // 2 in fixed for element in x ^ y):
                return None
            return tuple(sorted(fixed.items())), special
        fixed[selected] = int(2 * selected + 1 in display)


def sampling_constants(d: int, width: int, small_slots: int | None = None) -> dict[str, int]:
    """Conservative integer constants, conditional on the source lemmas.

    For p=0 the state graph is a singleton and needs no gap estimate; this
    helper requires p>=1. The root-square maximum is exact for integer width.
    """
    p = d if small_slots is None else small_slots
    if d < 1 or width < 2 or not 1 <= p <= d:
        raise ValueError("Require d>=p>=1 and width>=2, as in the source transport")
    triangle = width * (width + 1) // 2
    quadratic = (width + 1) ** 2 // 4
    transversal = triangle * (2 + 2 * (p - 1) * quadratic)
    repair_multiplicity = p * (p - 1)
    a = (1 + repair_multiplicity) * transversal
    root = isqrt(a)
    root_ceiling = root + int(root * root < a)
    full = a + 2 * root_ceiling + 1
    return {
        "path_triangle": triangle,
        "root_quadratic_maximum": quadratic,
        "transversal": transversal,
        "repair_multiplicity": repair_multiplicity,
        "full_variance_integer_bound": full,
        "ideal_inverse_gap_integer_bound": 128 * d * d * full,
    }


def bounded_constants(pairs: int, q: int | Fraction) -> dict[str, Fraction]:
    """Localized bounded-paper constants for its controlled observables.

    This is not a full enlarged-chain spectral-gap bound. The trace bound
    applies to the transversal trace; the observable bound is restricted.
    """
    q = Fraction(q)
    p = pairs
    if p < 1 or q < 1:
        raise ValueError("Require p>=1 and q>=1")
    cp = 1 + 8 * (p - 1) * q ** 2
    cd = Fraction(0) if p == 1 else 8 + 32 * (p - 2) * q ** 3
    n = p * (p - 1)
    k_obs = 2 * p * p * ((1 + 24 * n) * cp + 8 * n * cd)
    return {
        "transversal": cp,
        "defect_mean": cd,
        "trace_inverse_gap": 2 * p * p * cp,
        "controlled_observable": k_obs,
    }
