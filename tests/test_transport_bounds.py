"""Finite exact checks of the independently proved transport refinements."""

from fractions import Fraction
from itertools import combinations, product
import random
import unittest

from contingency115.transport_bounds import (
    binary_leaf_edge_owner,
    bounded_constants,
    integer_leaf_edge_owner,
    interval_log_concave,
    path_cut_coefficients,
    path_uniform_bound,
    path_variance,
    sampling_constants,
)


class PathBoundsTests(unittest.TestCase):
    def test_cut_bound_for_integer_log_concave_sequences(self):
        checked_sequences = checked_cuts = 0
        for length in range(2, 7):
            for z in product(range(1, 6), repeat=length):
                if not interval_log_concave(z):
                    continue
                checked_sequences += 1
                bound = path_uniform_bound(z)
                for j, coefficient in enumerate(path_cut_coefficients(z)):
                    direct = Fraction(sum(z[a] * z[b] * (b - a)
                                          for a in range(j + 1)
                                          for b in range(j + 1, length)), sum(z))
                    self.assertEqual(coefficient, direct)
                    self.assertLessEqual(coefficient, bound * min(z[j], z[j + 1]))
                    checked_cuts += 1
        self.assertGreater(checked_sequences, 500)
        self.assertGreater(checked_cuts, 2000)

    def test_rational_scales_and_hard_zero_endpoints(self):
        for z in ((0, 1, 2, 2, 1, 0), (0, 0, 3, 0), (2, 1), (1, 3, 9, 27)):
            for scale in (Fraction(1, 13), Fraction(17, 4), Fraction(1)):
                masses = tuple(scale * x for x in z)
                bound = path_uniform_bound(masses)
                for h in product((-2, 0, 3), repeat=len(z)):
                    energy = sum(min(masses[j], masses[j + 1]) * (h[j] - h[j + 1]) ** 2
                                 for j in range(len(z) - 1))
                    self.assertLessEqual(path_variance(masses, h), bound * energy)

    def test_support_and_log_concavity_negative_controls(self):
        self.assertFalse(interval_log_concave((1, 0, 1)))
        # Local inequalities alone miss a zero gap of length two.
        gap = (1, 0, 0, 1)
        self.assertTrue(all(gap[j] ** 2 >= gap[j - 1] * gap[j + 1] for j in (1, 2)))
        self.assertFalse(interval_log_concave(gap))
        self.assertFalse(interval_log_concave((1, 1, 4)))
        self.assertGreater(path_variance(gap, (0, 0, 1, 1)), 0)
        for z in (gap, (1, 1, 4)):
            with self.assertRaises(ValueError):
                path_uniform_bound(z)

    def test_quadratic_order_and_single_edge_sharpness(self):
        for width in range(1, 30):
            z = (1,) * (width + 1)
            ratio = path_variance(z, tuple(range(width + 1))) / width
            self.assertEqual(ratio, Fraction((width + 1) * (width + 2), 12))
        for r in (1, 7, 10**12):
            self.assertEqual(path_variance((1, r), (0, 1)), Fraction(r, r + 1))


class OwnershipTests(unittest.TestCase):
    def test_complete_integer_leaf_families(self):
        total_edges = 0
        for widths in ((1,), (2,), (2, 2), (3, 3, 3), (2, 2, 2, 2), (2, 3, 2)):
            p = len(widths)
            orders = {tuple(range(p)), tuple(reversed(range(p)))}
            for order in orders:
                seen = {}
                for depth, special in enumerate(order):
                    other = [j for j in range(p) if j != special]
                    for ell in range(1, widths[special] + 1):
                        for choices in product(*(range(widths[j] + 1) for j in other)):
                            chosen = dict(zip(other, choices))
                            display = []
                            for j, width in enumerate(widths):
                                display.extend((ell, width + 1 - ell) if j == special
                                               else (chosen[j], width - chosen[j]))
                            owner = special, ell, tuple((j, chosen[j]) for j in order[:depth])
                            vertices = []
                            for j in order[depth:]:
                                for coord in (2 * j, 2 * j + 1):
                                    if not display[coord]:
                                        continue
                                    v = list(display)
                                    v[coord] -= 1
                                    if all(value <= widths[k // 2] for k, value in enumerate(v)):
                                        vertices.append(tuple(v))
                            for x, y in combinations(vertices, 2):
                                edge = tuple(sorted((x, y)))
                                self.assertNotIn(edge, seen)
                                seen[edge] = owner
                                self.assertEqual(tuple(map(max, zip(x, y))), tuple(display))
                                self.assertEqual(integer_leaf_edge_owner(x, y, widths, order), owner)
                                self.assertEqual(integer_leaf_edge_owner(y, x, widths, order), owner)
                total_edges += len(seen)
        self.assertGreater(total_edges, 5000)

    def test_fixed_prefix_holes_are_rejected(self):
        # Full display has special slot 1, but one hole changes fixed slot 0.
        self.assertIsNone(integer_leaf_edge_owner((0, 1, 1, 1), (1, 1, 0, 1), (2, 1)))
        self.assertIsNone(integer_leaf_edge_owner((1, 1), (1, 1), (2,)))
        self.assertIsNone(integer_leaf_edge_owner((0, 0), (1, 1), (2,)))

    def test_adaptive_binary_tree_ownership(self):
        total_edges = 0
        for pairs in range(1, 7):
            for strategy in range(3):
                def choose(fixed):
                    remaining = [j for j in range(pairs) if j not in fixed]
                    if strategy == 0:
                        return remaining[0]
                    if strategy == 1:
                        return remaining[sum(fixed.values()) % len(remaining)]
                    return remaining[(sum((j + 1) * (value + 1) for j, value in fixed.items())
                                      + len(fixed) ** 2) % len(remaining)]

                seen = {}

                def visit(fixed):
                    if len(fixed) == pairs:
                        return
                    special = choose(fixed)
                    ordinary = [j for j in range(pairs) if j not in fixed and j != special]
                    owner = tuple(sorted(fixed.items())), special
                    for choices in product((0, 1), repeat=len(ordinary)):
                        display = {2 * j + value for j, value in fixed.items()}
                        display.update(2 * j + value for j, value in zip(ordinary, choices))
                        display.update((2 * special, 2 * special + 1))
                        removable = [element for element in display if element // 2 not in fixed]
                        vertices = [frozenset(display - {element}) for element in removable]
                        for x, y in combinations(vertices, 2):
                            edge = tuple(sorted((tuple(sorted(x)), tuple(sorted(y)))))
                            self.assertNotIn(edge, seen)
                            seen[edge] = owner
                            self.assertEqual(x | y, display)
                            self.assertEqual(binary_leaf_edge_owner(x, y, pairs, choose), owner)
                    for value in (0, 1):
                        visit(fixed | {special: value})

                visit({})
                total_edges += len(seen)
        self.assertGreater(total_edges, 7500)


class ComparisonTests(unittest.TestCase):
    def test_integer_root_quadratic_maximum(self):
        for width in range(1, 100):
            maximum = max(a * (width + 1 - a) for a in range(width + 2))
            self.assertEqual(maximum, (width + 1) ** 2 // 4)

    def test_centered_conditioning_is_sharp(self):
        for z in product(range(1, 5), repeat=4):
            for count in (1, 2, 3):
                rho = Fraction(sum(z[:count]), sum(z))
                h = (1,) * count + (0,) * (4 - count)
                variance = path_variance(z, h) / sum(z)
                self.assertEqual((1 - rho) ** 2, (1 - rho) * variance / rho)
                if rho >= Fraction(1, 4):
                    self.assertLessEqual((1 - rho) ** 2, 3 * variance)

    def test_repair_triangle_with_overlapping_edges(self):
        rng = random.Random(115)
        # Three transversals; two defects may repair to the first one. Their
        # edges need not be disjoint from edges counted by another estimate.
        repair = (0, 1, 2, 0, 0, 1)
        weights = (5, 3, 4, 2, 5, 1)
        multiplicity = 2
        for _ in range(300):
            h = tuple(rng.randrange(-20, 21) for _ in weights)
            transversal_variance = path_variance(weights[:3], h[:3])
            variance = path_variance(weights, h)
            repair_energy = sum(weights[i] * (h[i] - h[repair[i]]) ** 2 for i in range(3, 6))
            a = (1 + multiplicity) * transversal_variance
            remainder = variance - a - repair_energy
            # Exact squared comparison, with sign checked before squaring.
            if remainder > 0:
                self.assertLessEqual(remainder ** 2, 4 * a * repair_energy)

    def test_constants_improve_initial_and_source_bounds(self):
        for d in (14, 19, 40):
            for u in (2, 7, d**20):
                for p in (1, 2, d - 1):
                    improved = sampling_constants(d, u, p)
                    initial_ct = u * (u + 1) * (2 + 2 * d * (u + 1) ** 2)
                    initial_full = (1 + 2 * d * d) * initial_ct + 2
                    source_full = (1 + 2 * d * d) * 4 * d * d * (u + 1) ** 6 + 2
                    self.assertLess(improved["full_variance_integer_bound"], initial_full)
                    self.assertLess(initial_full, source_full)
                    a = (1 + p * (p - 1)) * improved["transversal"]
                    remainder = improved["full_variance_integer_bound"] - a - 1
                    self.assertGreaterEqual(remainder * remainder, 4 * a)
        for p in range(1, 10):
            for q in (1, 3, Fraction(7, 2), 100):
                values = bounded_constants(p, q)
                cp_old = p * (1 + 8 * p * q**2)
                cd_old = 8 + 32 * p * q**3
                self.assertLess(values["transversal"], cp_old)
                self.assertLess(values["controlled_observable"], 10 * p**4 * (9 * cp_old + 2 * cd_old))
                self.assertGreaterEqual(values["controlled_observable"], values["trace_inverse_gap"])


if __name__ == "__main__":
    unittest.main()
