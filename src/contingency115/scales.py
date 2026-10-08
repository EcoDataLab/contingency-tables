"""Exact arithmetic for the conditional scale audit of OpenAI result #115.

These helpers certify arithmetic and finite combinatorial examples. They do
not implement the published sampler or certify its complete Lean program.
See ``docs/scale-audit.md`` for the proofs and their remaining dependencies.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb
from typing import Sequence


@dataclass(frozen=True)
class SamplingScales:
    """The penalty, bin, padding, and small-margin threshold parameters."""

    d: int
    A: int
    B: int
    L: int
    U: int

    def __post_init__(self) -> None:
        if any(type(v) is not int or v <= 0 for v in
               (self.d, self.A, self.B, self.L, self.U)):
            raise ValueError("dimension and scales must be positive integers")


def proposed_scales(d: int) -> SamplingScales:
    """Return the manuscript-level d^25 candidate, for integer d >= 14.

    The threshold uses the all-switchings small-entry lemma, and the d^25
    conclusion additionally requires the localized transport inequality.
    """
    if type(d) is not int or d < 14:
        raise ValueError("the source dimension allowance must be an integer >= 14")
    return SamplingScales(d, 16 * d**2, 16 * d**3, 32 * d**3, 128 * d**5)


def sharper_scales(d: int) -> SamplingScales:
    """Use U=64d^5 with the marked cell's own padding in the margin bound.

    Apply the switching lemma at a=U+L, t=L. The resulting denominator
    is U+1, and this constructor must not be tested against the older
    U-L+1 sufficient condition.
    """
    base = proposed_scales(d)
    return SamplingScales(d, base.A, base.B, base.L, 64 * d**5)


def shape_aware_scales(rows: int, columns: int) -> SamplingScales:
    """An explicit threshold using full dimensions and the linear tail bound.

    This uses mn as an upper bound on large-cell count, so there is no
    circular dependence on the large rectangle selected by U. Singleton
    dimensions have e=0 and use U=2L; their actual sampling problem is
    deterministic. Empty dimensions bypass the sampler and are not inputs.
    """
    if any(type(v) is not int or v < 1 for v in (rows, columns)):
        raise ValueError("shape-aware scales require positive integer dimensions")
    d = 10 + (rows + 1) * (columns + 1)
    base = proposed_scales(d)
    e = (rows - 1) * (columns - 1)
    threshold = max(2 * base.L, 2 * base.L * rows * columns * e - base.L - e)
    return SamplingScales(d, base.A, base.B, base.L, threshold)


def small_entry_bound(rows: int, columns: int, minimum_margin: int,
                      threshold: int) -> Fraction:
    """Unclipped all-switchings bound for a marked cell of an unrestricted fiber.

    Both incident margins must be at least ``minimum_margin``. For
    1 <= threshold <= minimum_margin, the event is X[i,j] < threshold.
    Singleton-dimensional fibers have bound zero. Cell caps and structural
    zeros are not supported by this lemma.
    """
    if any(type(v) is not int for v in (rows, columns, minimum_margin, threshold)):
        raise ValueError("all arguments must be integers")
    if rows < 1 or columns < 1 or not 1 <= threshold <= minimum_margin:
        raise ValueError("require positive dimensions and 1 <= threshold <= margin")
    return Fraction(threshold * (rows - 1) * (columns - 1),
                    minimum_margin - threshold + 1)


def small_entry_bound_refined(rows: int, columns: int, minimum_margin: int,
                              threshold: int) -> Fraction:
    """Sharper all-switchings bound using the target-dependent incoming count.

    A target with marked value y has at most e*min(t,y) incoming labels,
    where e=(rows-1)*(columns-1). This adds e to the denominator. The
    simpler ``small_entry_bound`` remains useful for transparent scales.
    """
    small_entry_bound(rows, columns, minimum_margin, threshold)
    e = (rows - 1) * (columns - 1)
    return Fraction(threshold * e, minimum_margin - threshold + 1 + e)


def small_entry_tail_product_bound(rows: int, columns: int, minimum_margin: int,
                                    threshold: int) -> Fraction:
    """Upper bound 1-product((a-k)/(a+e-k), k=0..t-1) for P(Xij<t).

    Conditioning on Xij>=k and subtracting k in that cell gives another
    unrestricted uniform fiber; apply the refined zero-entry bound there.
    Same domain and model restrictions as ``small_entry_bound``.
    """
    small_entry_bound(rows, columns, minimum_margin, threshold)
    e = (rows - 1) * (columns - 1)
    survival = Fraction(1)
    for k in range(threshold):
        survival *= Fraction(minimum_margin - k, minimum_margin + e - k)
    return 1 - survival


def small_entry_bound_linear(rows: int, columns: int, minimum_margin: int,
                              threshold: int) -> Fraction:
    """The simplified, unclipped tail bound t*e/(a+e).

    This follows from the conditional-shift survival product. It is exact
    for every threshold in equal-margin 2x2 tables. When e=0 the event is
    empty; both this expression and the product bound give zero.
    """
    small_entry_bound(rows, columns, minimum_margin, threshold)
    e = (rows - 1) * (columns - 1)
    return Fraction(threshold * e, minimum_margin + e)


def small_entry_mean_lower_bound(rows: int, columns: int,
                                 minimum_margin: int) -> Fraction:
    """E[Xij] >= a/(e+1), by summing the conditional-shift survival bound."""
    if any(type(v) is not int for v in (rows, columns, minimum_margin)):
        raise ValueError("all arguments must be integers")
    if rows < 1 or columns < 1 or minimum_margin < 0:
        raise ValueError("require positive dimensions and nonnegative margin")
    return Fraction(minimum_margin, (rows - 1) * (columns - 1) + 1)


def switching_outdegree(table: Sequence[Sequence[int]], row: int, column: int) -> int:
    """Count all donor-pair/positive-amount switches increasing a marked cell."""
    if not table or not table[0] or any(len(r) != len(table[0]) for r in table):
        raise ValueError("table must be a nonempty rectangle")
    if any(type(x) is not int or x < 0 for r in table for x in r):
        raise ValueError("entries must be nonnegative integers")
    if not 0 <= row < len(table) or not 0 <= column < len(table[0]):
        raise ValueError("marked cell is outside the table")
    return sum(min(table[row][j], table[i][column])
               for i in range(len(table)) if i != row
               for j in range(len(table[0])) if j != column)


def reference_adjustment(row_changes: Sequence[int], column_changes: Sequence[int],
                         reference_row: int = 0, reference_column: int = 0
                         ) -> tuple[tuple[int, ...], ...]:
    """Return the source's reference-row/reference-column completion adjustment.

    Compatible arbitrary changes are accepted; the norm/support claims apply
    only to the edge families proved in the audit, not to all inputs here.
    Empty blocks require every residual change to be zero.
    """
    r, c = tuple(row_changes), tuple(column_changes)
    if any(type(x) is not int for x in r + c) or sum(r) != sum(c):
        raise ValueError("integer row and column changes must have equal totals")
    if not r or not c:
        if any(r + c):
            raise ValueError("empty blocks cannot have nonzero residual changes")
        return tuple(() for _ in r)
    if not 0 <= reference_row < len(r) or not 0 <= reference_column < len(c):
        raise ValueError("reference cell is outside the block")
    answer = [[0] * len(c) for _ in r]
    for i in range(len(r)):
        if i != reference_row:
            answer[i][reference_column] = r[i]
    for j in range(len(c)):
        if j != reference_column:
            answer[reference_row][j] = c[j]
    answer[reference_row][reference_column] = (
        r[reference_row] - sum(c[j] for j in range(len(c)) if j != reference_column)
    )
    return tuple(map(tuple, answer))


def scale_residuals(s: SamplingScales) -> dict[str, int]:
    """Cross-multiplied sufficient inequalities; nonnegative means satisfied.

    This is a list of analytic scale obligations, not a certificate that the
    entire reparameterized sampler has been implemented or formally checked.
    """
    d, A, B, L, U = s.d, s.A, s.B, s.L, s.U
    return {
        "positive_integer_widths": L - 2 * B,
        "half_inner_volume": B - 8 * d**3,
        "within_bin_comparison": B - A * d,
        "layer_sum_normalizer": A * B - 8 * d**2 * B - 8 * d**3 * A,
        "directional_half_acceptance_new_switching": L - 4 * d,
        "half_unpadding_success_new_switching": U - L + 1 - 2 * L * d**2,
        "unpadding_threshold_at_most_half_margin": U - 2 * L,
        # These two are optional cross-checks using the old small-entry lemma.
        "old_small_entry_lemma_domain": L - 4 * d,
        "directional_half_acceptance_old_switching": L - 16 * d**3,
    }


def scale_probability_bounds(s: SamplingScales) -> dict[str, Fraction]:
    """Unclipped rational bounds entering the analytic argument."""
    if s.U < s.L:
        raise ValueError("the unpadding bound requires U >= L")
    return {
        "inner_volume_loss": Fraction(4 * s.d**3, s.B),
        "log_density_change_per_bin": Fraction(s.A * s.d, s.B),
        "layer_exponent_sum": Fraction(2 * s.d**2, s.A) + Fraction(2 * s.d**3, s.B),
        "directional_completion_rejection": Fraction(2 * s.d, s.L),
        "best_edge_orientation_rejection": Fraction(s.d, s.L),
        "unpadding_bad_fraction": Fraction(s.L * s.d**2, s.U - s.L + 1),
    }


def padded_margin_scale_residuals(s: SamplingScales) -> dict[str, int]:
    """The enlarged-margin sufficient conditions, with denominator U+1."""
    result = scale_residuals(s)
    del result["half_unpadding_success_new_switching"]
    result["half_unpadding_success_enlarged_margins"] = s.U + 1 - 2 * s.L * s.d**2
    return result


def padded_margin_scale_probability_bounds(s: SamplingScales) -> dict[str, Fraction]:
    """Use actual enlarged margin >=U+L at every padded marked cell."""
    result = scale_probability_bounds(s)
    result["unpadding_bad_fraction"] = Fraction(s.L * s.d**2, s.U + 1)
    return result


def shape_aware_scale_probability_bounds(rows: int, columns: int) -> dict[str, Fraction]:
    """Bounds for shape_aware_scales using the stronger linear tail lemma."""
    s = shape_aware_scales(rows, columns)
    result = padded_margin_scale_probability_bounds(s)
    e = (rows - 1) * (columns - 1)
    result["unpadding_bad_fraction"] = Fraction(rows * columns * s.L * e, s.U + s.L + e)
    return result


# Polynomials have integer coefficients in ascending powers of d. The tiny
# exact certificate format intentionally needs no symbolic algebra dependency.
Polynomial = tuple[int, ...]


def _add(a: Polynomial, b: Polynomial) -> Polynomial:
    return tuple((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b))))


def _scale(a: Polynomial, k: int) -> Polynomial:
    return tuple(k * x for x in a)


def _mul(a: Polynomial, b: Polynomial) -> Polynomial:
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return tuple(result)


def evaluate_polynomial(coefficients: Sequence[int], d: int) -> int:
    value = 0
    for coefficient in reversed(coefficients):
        value = value * d + coefficient
    return value


@dataclass(frozen=True)
class PolynomialCertificate:
    """If all shifted coefficients are >= 0, P(d) >= 0 for every d >= lower."""

    name: str
    lower: int
    coefficients: Polynomial
    shifted_coefficients: Polynomial

    def verify(self) -> bool:
        expected = tuple(sum(self.coefficients[j] * comb(j, k) * self.lower ** (j - k)
                             for j in range(k, len(self.coefficients)))
                         for k in range(len(self.coefficients)))
        return self.shifted_coefficients == expected and all(x >= 0 for x in expected)


def proposed_scale_certificates() -> tuple[PolynomialCertificate, ...]:
    """Exact finite certificates for all listed inequalities, for every d >= 14.

    Substitution d = 14+x expands each residual as a polynomial whose integer
    coefficients are nonnegative. This certifies a universal arithmetic
    statement, rather than testing finitely many dimension values.
    """
    return _scale_certificates(128, False)


def sharper_scale_certificates() -> tuple[PolynomialCertificate, ...]:
    """Universal certificate for the U=64d^5 enlarged-margin construction."""
    return _scale_certificates(64, True)


def _scale_certificates(threshold_coefficient: int, enlarged_margin: bool
                         ) -> tuple[PolynomialCertificate, ...]:
    one, d, d2, d3 = (1,), (0, 1), (0, 0, 1), (0, 0, 0, 1)
    A, B, L = _scale(d2, 16), _scale(d3, 16), _scale(d3, 32)
    U = (0, 0, 0, 0, 0, threshold_coefficient)
    sub = lambda a, b: _add(a, _scale(b, -1))
    residuals = {
        "positive_integer_widths": sub(L, _scale(B, 2)),
        "half_inner_volume": sub(B, _scale(d3, 8)),
        "within_bin_comparison": sub(B, _mul(A, d)),
        "layer_sum_normalizer": sub(sub(_mul(A, B), _scale(_mul(d2, B), 8)),
                                      _scale(_mul(d3, A), 8)),
        "directional_half_acceptance_new_switching": sub(L, _scale(d, 4)),
        "half_unpadding_success_new_switching": sub(_add(sub(U, L), one),
                                                   _scale(_mul(L, d2), 2)),
        "unpadding_threshold_at_most_half_margin": sub(U, _scale(L, 2)),
        "old_small_entry_lemma_domain": sub(L, _scale(d, 4)),
        "directional_half_acceptance_old_switching": sub(L, _scale(d3, 16)),
    }
    if enlarged_margin:
        del residuals["half_unpadding_success_new_switching"]
        residuals["half_unpadding_success_enlarged_margins"] = sub(
            _add(U, one), _scale(_mul(L, d2), 2))
    result = []
    for name, coefficients in residuals.items():
        shifted = tuple(sum(coefficients[j] * comb(j, k) * 14 ** (j - k)
                            for j in range(k, len(coefficients)))
                        for k in range(len(coefficients)))
        result.append(PolynomialCertificate(name, 14, coefficients, shifted))
    return tuple(result)
