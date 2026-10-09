from collections import Counter
from dataclasses import replace
from fractions import Fraction
from itertools import product
import unittest

from contingency115.ideal_chain import (IdealChainBudget, PhysicalState,
    build_ideal_chain, build_rescaled_ideal_chain)
from contingency115.kernels import ExactKernel
from contingency115.tables import (ComputationBudgetExceeded, ExactTableSampler,
                                   InfeasibleTableError, TableProblem)


class Choices:
    def __init__(self, *choices):
        self.choices = iter(choices)

    def randrange(self, stop):
        value = next(self.choices)
        assert 0 <= value < stop
        return value


def independently_all_small_states(k):
    # Enumerate the actual two views independently, without generating defects.
    views = tuple(product(range(k + 1), repeat=4))
    rows = [x for x in views if x[0] + x[1] == x[2] + x[3] == k]
    columns = [q for q in views if q[0] + q[2] == q[1] + q[3] == k]
    return {PhysicalState(x, q) for x in rows for q in columns
            if sorted(qi - xi for xi, qi in zip(x, q)) in
            ([0, 0, 0, 0], [-1, 0, 0, 1])}


class IdealChainTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.one = build_ideal_chain(TableProblem((1, 1), (1, 1)))
        cls.two = build_ideal_chain(TableProblem((2, 2), (2, 2)))
        U = 19**20
        cls.mixed = build_ideal_chain(TableProblem((U, 1), (U, 1)))
        cls.rescaled = build_rescaled_ideal_chain(TableProblem((4, 4, 1), (4, 4, 1)), U=4, L=1)

    def assert_invariants(self, chain):
        # ExactKernel's generic invariants do not rely on table identities.
        kernel = ExactKernel(chain.states, chain.matrix, chain.stationary)
        self.assertTrue(kernel.is_stochastic())
        self.assertTrue(kernel.satisfies_detailed_balance())
        self.assertEqual(len(kernel.communicating_classes()), 1)
        self.assertEqual(sum(chain.stationary), 1)
        for i, row in enumerate(chain.neighbors):
            self.assertEqual(len(row), len(set(row)))
            self.assertNotIn(i, row)
            self.assertLessEqual(len(row), 5 * chain.d**2 + 1)
            self.assertLessEqual(len(row) * chain.beta, Fraction(1, 2))
            for j in row:
                self.assertIn(i, chain.neighbors[j])
                self.assertEqual(chain.acceptance_counts[i][j], chain.acceptance_counts[j][i])
            self.assertEqual(sum(chain.stationary[j] * chain.matrix[j][i]
                                 for j in range(len(chain.states))), chain.stationary[i])

    def test_literal_parameters_state_set_and_empty_fibres(self):
        for k, chain, count, edges in ((1, self.one, 14, 28), (2, self.two, 27, 56)):
            self.assertEqual((chain.d, chain.U, chain.L, chain.beta),
                             (19, 19**20, 19**12, Fraction(1, 16384)))
            self.assertEqual(set(chain.states), independently_all_small_states(k))
            self.assertEqual(len(chain.states), count)
            self.assertEqual(sum(map(len, chain.neighbors)) // 2, edges)
            self.assertEqual(chain.completions, (((),),) * count)
            self.assertIsNone(chain.reference_cell)
            for i, state in enumerate(chain.states):
                self.assertEqual(chain.doubled_profile(i), state.row_view +
                                 tuple(chain.U - q for q in state.column_view))
            self.assert_invariants(chain)

    def test_independent_doubled_exchange_and_repair_edges(self):
        for chain in (self.one, self.two, self.mixed, self.rescaled):
            cells = chain.small_cells
            cell_index = {cell: k for k, cell in enumerate(cells)}
            repair_edges = set()
            for i, state in enumerate(chain.states):
                delta = [q - x for x, q in zip(state.row_view, state.column_view)]
                if any(delta):
                    s, t = delta.index(1), delta.index(-1)
                    repaired = list(state.row_view)
                    repaired[t] -= 1
                    cross = cells[t][0], cells[s][1]
                    if cross in cell_index:
                        repaired[cell_index[cross]] += 1
                    j = chain.states.index(PhysicalState(tuple(repaired), tuple(repaired)))
                    repair_edges.update(((i, j), (j, i)))
            for i in range(len(chain.states)):
                for j in range(len(chain.states)):
                    difference = [b - a for a, b in zip(chain.doubled_profile(i), chain.doubled_profile(j))]
                    exchange = sorted(difference) == [-1] + [0] * (len(difference) - 2) + [1]
                    self.assertEqual(j in chain.neighbors[i], exchange or (i, j) in repair_edges)

    def test_feasibility_equations_and_fibre_margins(self):
        for chain in (self.one, self.two, self.mixed, self.rescaled):
            for state, (rr, cc), fibre in zip(chain.states, chain.residual_margins, chain.completions):
                self.assertTrue(state.balanced or state.defect_labels() is not None)
                m, n = chain.problem.shape
                a, b = [0] * m, [0] * n
                for (i, j), x, q in zip(chain.small_cells, state.row_view, state.column_view):
                    self.assertTrue(0 <= x <= chain.U and 0 <= q <= chain.U)
                    a[i] += x
                    b[j] += q
                full_r = tuple(chain.problem.row_sums[i] - a[i] +
                               (len(chain.large_columns) * chain.L if i in chain.large_rows else 0)
                               for i in range(m))
                full_c = tuple(chain.problem.column_sums[j] - b[j] +
                               (len(chain.large_rows) * chain.L if j in chain.large_columns else 0)
                               for j in range(n))
                self.assertTrue(all(x <= r for x, r in zip(a, chain.problem.row_sums)))
                self.assertTrue(all(q <= c for q, c in zip(b, chain.problem.column_sums)))
                self.assertTrue(all(full_r[i] == 0 for i in range(m) if i not in chain.large_rows))
                self.assertTrue(all(full_c[j] == 0 for j in range(n) if j not in chain.large_columns))
                self.assertEqual(sum(full_r), sum(full_c))
                self.assertEqual(rr, tuple(full_r[i] for i in chain.large_rows))
                self.assertEqual(cc, tuple(full_c[j] for j in chain.large_columns))
                for completion in fibre:
                    if chain.all_small:
                        self.assertEqual(completion, ())
                    else:
                        self.assertEqual(tuple(map(sum, completion)), rr)
                        self.assertEqual(tuple(sum(row[j] for row in completion) for j in range(len(cc))), cc)
                        self.assertTrue(all(value <= chain.large_capacity for row in completion for value in row))

    def test_stationary_output_bijection_and_conditional_uniformity(self):
        for chain in (self.one, self.two, self.mixed, self.rescaled):
            if chain is self.mixed:
                U = chain.U
                tables = {((U - 1, 1), (1, 0)), ((U, 0), (0, 1))}
            else:
                tables = set(ExactTableSampler(chain.problem).tables())
            preimages = Counter()
            for i, fibre in enumerate(chain.completions):
                for rank in range(len(fibre)):
                    table = chain.output(i, Choices(rank))
                    if table is not None:
                        preimages[table] += 1
            self.assertEqual(set(preimages), tables)
            self.assertEqual(set(preimages.values()), {1})
            law, failure = chain.stationary_output_law()
            self.assertEqual(set(law), tables)
            self.assertEqual(sum(law.values()) + failure, 1)
            self.assertEqual(set(mass / (1 - failure) for mass in law.values()), {Fraction(1, len(tables))})
            self.assert_invariants(chain)
        self.assertEqual(self.one.stationary_output_law()[1], Fraction(6, 7))
        self.assertEqual(self.two.stationary_output_law()[1], Fraction(8, 9))

    def test_literal_mixed_large_crossing_and_unique_completions(self):
        chain = self.mixed
        self.assertEqual(chain.parameter_regime, "literal paper parameters")
        self.assertEqual(chain.reference_cell, (0, 0))
        self.assertEqual((len(chain.states), sum(map(len, chain.neighbors)) // 2), (9, 14))
        self.assertEqual(chain.completion_counts, (1,) * 9)
        self.assertTrue(any(state.defect_labels() is not None and
            (chain.small_cells[state.defect_labels()[1]][0],
             chain.small_cells[state.defect_labels()[0]][1]) == (0, 0)
             for state in chain.states))

    def test_nontrivial_completion_translation_is_source_star_not_metropolis(self):
        chain = self.rescaled
        self.assertIn("rescaled diagnostic", chain.parameter_regime)
        self.assertEqual(set(chain.completion_counts), {5, 6, 7})
        self.assertEqual((len(chain.states), sum(map(len, chain.neighbors)) // 2), (49, 150))
        rejecting_edges = 0
        metropolis_disagreements = 0
        for i, neighbors in enumerate(chain.neighbors):
            for j in neighbors:
                delta = chain.translation(i, j)
                rr, cc = chain.residual_margins[i]
                target_r, target_c = chain.residual_margins[j]
                self.assertEqual(tuple(map(sum, delta)), tuple(y - x for x, y in zip(rr, target_r)))
                self.assertEqual(tuple(sum(row[b] for row in delta) for b in range(len(cc))),
                                 tuple(y - x for x, y in zip(cc, target_c)))
                self.assertEqual(delta[1][1], 0)
                forward = set()
                for completion in chain.completions[i]:
                    translated = tuple(tuple(value + delta[a][b] for b, value in enumerate(row))
                                       for a, row in enumerate(completion))
                    if min(value for row in translated for value in row) >= 0:
                        forward.add(translated)
                backward = {completion for completion in chain.completions[j]
                            if chain.completion_passes(j, i, completion)}
                self.assertEqual(forward, backward)
                self.assertEqual(len(forward), chain.acceptance_counts[i][j])
                rejecting_edges += len(forward) < chain.completion_counts[i]
                metropolis_disagreements += (chain.matrix[i][j] != chain.beta *
                    min(1, Fraction(chain.completion_counts[j], chain.completion_counts[i])))
        self.assertEqual(rejecting_edges, 82)
        self.assertGreater(metropolis_disagreements, 0)

    def test_literal_rng_decision_tree_including_holds_and_rejections(self):
        for chain in (self.one, self.rescaled):
            for i, neighbors in enumerate(chain.neighbors):
                counts = Counter()
                for slot in range(len(neighbors)):
                    for rank in range(chain.completion_counts[i]):
                        counts[chain.step(i, Choices(slot, rank))] += 1
                # All unused dyadic slots are identical holds, no completion draw.
                hold_slots = chain.beta.denominator - len(neighbors)
                self.assertEqual(chain.step(i, Choices(len(neighbors))), i)
                counts[i] += hold_slots * chain.completion_counts[i]
                denominator = chain.beta.denominator * chain.completion_counts[i]
                self.assertEqual(tuple(Fraction(counts[j], denominator) for j in range(len(chain.states))), chain.matrix[i])

    def test_exact_censoring_and_physical_return_time(self):
        for chain, pi, times in ((self.one, Fraction(1, 7), (7, 7)),
                                 (self.two, Fraction(1, 9), (7, 13, 7))):
            result = chain.all_small_return_kernel()
            kernel = result.kernel
            self.assertEqual(result.stationary_success_probability, pi)
            self.assertEqual(result.expected_physical_steps_per_return, 1 / pi)
            self.assertEqual(result.per_start_expected_physical_steps, times)
            size = len(kernel.states)
            self.assertEqual(kernel.stationary, (Fraction(1, size),) * size)
            for i, row in enumerate(kernel.matrix):
                for j, value in enumerate(row):
                    self.assertEqual(value, Fraction(1, 7680) if abs(i-j) == 1 else
                                     1 - Fraction((i > 0) + (i < size-1), 7680) if i == j else 0)
            self.assertTrue(kernel.is_stochastic())
            self.assertTrue(kernel.satisfies_detailed_balance())
            self.assertIn("bypass", result.construction)
        with self.assertRaises(ValueError):
            self.mixed.all_small_return_kernel()

    def test_independent_first_hit_equations_on_embedded_jump_chain(self):
        # Solve the nonlazy graph Dirichlet problem, avoiding the implementation's
        # (I-P_BB) lazy-kernel system and its simultaneous probability/time RHS.
        chain = self.one
        a = [i for i, state in enumerate(chain.states) if state.balanced]
        b = [i for i, state in enumerate(chain.states) if not state.balanced]
        system = [[Fraction(len(chain.neighbors[i]) if i == j else
                            -int(j in chain.neighbors[i])) for j in b] +
                  [Fraction(a[1] in chain.neighbors[i])] for i in b]
        for column in range(len(b)):
            pivot = next(row for row in range(column, len(b)) if system[row][column])
            system[column], system[pivot] = system[pivot], system[column]
            for row in range(column + 1, len(b)):
                factor = system[row][column] / system[column][column]
                system[row] = [x - factor*y for x, y in zip(system[row], system[column])]
        h = {}
        for row in reversed(range(len(b))):
            h[b[row]] = (system[row][-1] - sum(system[row][j] * h[b[j]]
                         for j in range(row + 1, len(b)))) / system[row][row]
        h[a[0]], h[a[1]] = Fraction(0), Fraction(1)
        for i in b:
            self.assertEqual(h[i] * len(chain.neighbors[i]), sum(h[j] for j in chain.neighbors[i]))
        result = chain.all_small_return_kernel().kernel
        for index, i in enumerate(a):
            self.assertEqual(sum(chain.matrix[i][j] * h[j] for j in range(len(chain.states))), result.matrix[index][1])

    def test_budget_caps_fail_without_partial_results(self):
        small = self.one.problem
        for key in ("max_cells", "max_input_bits", "max_profile_candidates",
                    "max_physical_states", "max_transition_work", "max_rational_bits"):
            with self.subTest(key=key), self.assertRaises(ComputationBudgetExceeded):
                build_ideal_chain(small, budget=replace(IdealChainBudget(), **{key: 1}))
        with self.assertRaises(ComputationBudgetExceeded):
            build_ideal_chain(self.mixed.problem, budget=replace(IdealChainBudget(), max_completions=1))
        for key in ("max_dp_states", "max_dp_transitions"):
            with self.subTest(key=key), self.assertRaises(ComputationBudgetExceeded):
                build_rescaled_ideal_chain(self.rescaled.problem, U=4, L=1,
                    budget=replace(IdealChainBudget(), **{key: 1}))
        for key in ("max_solve_size", "max_solve_work", "max_rational_bits"):
            with self.subTest(key=key), self.assertRaises(ComputationBudgetExceeded):
                self.one.all_small_return_kernel(budget=replace(IdealChainBudget(), **{key: 1}))
        frozen = replace(self.one, matrix=tuple(tuple(Fraction(i == j) for j in range(14)) for i in range(14)))
        with self.assertRaises(ValueError):
            frozen.all_small_return_kernel()

    def test_literal_excursion_counts_holds_and_enforces_cap(self):
        chain = self.one
        start = next(i for i, state in enumerate(chain.states) if state.balanced)
        result = chain.physical_return(start, max_steps=1, rng=Choices(chain.beta.denominator - 1))
        self.assertEqual((result.state_index, result.physical_steps), (start, 1))
        self.assertEqual(chain.problem.validate_table(result.table), result.table)
        slot = next(k for k, i in enumerate(chain.neighbors[start]) if not chain.states[i].balanced)
        with self.assertRaises(ComputationBudgetExceeded):
            chain.physical_return(start, max_steps=2, rng=Choices(slot, 0, chain.beta.denominator - 1))
        with self.assertRaises(ValueError):
            chain.physical_return(next(i for i, state in enumerate(chain.states) if not state.balanced), max_steps=1)

    def test_rejects_changed_target_and_malformed_input(self):
        for problem in (TableProblem((2, 2), (2, 2), structural_zeros=((0, 0),)),
                        TableProblem((2, 2), (2, 2), upper_bounds=((1, 2), (2, 2))),
                        TableProblem((2, 2), (2, 2), lower_bounds=((1, 0), (0, 0)))):
            with self.assertRaises(ValueError):
                build_ideal_chain(problem)
        with self.assertRaises(TypeError):
            build_ideal_chain(self.one.problem, weights=((1, 1), (1, 1)))
        with self.assertRaises(InfeasibleTableError):
            build_ideal_chain(TableProblem((1, 1), (1, 2)))
        with self.assertRaises(ValueError):
            build_rescaled_ideal_chain(self.one.problem, U=1, L=1)
        with self.assertRaises(TypeError):
            IdealChainBudget(max_cells=True)

    def test_zero_margins_degenerate_rectangles_and_parameter_bits(self):
        for rows, columns in (((0,), (0,)), ((1,), (1,)),
                              ((0, 2), (1, 1)), ((1, 1), (0, 2)),
                              ((0, 0), (0, 0))):
            chain = build_ideal_chain(TableProblem(rows, columns))
            result = chain.all_small_return_kernel()
            self.assert_invariants(chain)
            self.assertTrue(result.kernel.is_stochastic())
            law, failure = chain.stationary_output_law()
            self.assertEqual(set(law), set(ExactTableSampler(chain.problem).tables()))
            self.assertEqual(sum(law.values()) + failure, 1)
        U = 14**20
        singleton = build_ideal_chain(TableProblem((U,), (U,)))
        self.assertFalse(singleton.all_small)
        self.assertEqual(singleton.stationary_output_law(), ({((U,),): Fraction(1)}, Fraction(0)))
        with self.assertRaises(ComputationBudgetExceeded):
            build_rescaled_ideal_chain(self.one.problem, U=2, L=1 << 4096)


if __name__ == "__main__":
    unittest.main()
