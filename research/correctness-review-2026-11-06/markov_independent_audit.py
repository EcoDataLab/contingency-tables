"""Small exact oracles derived from equations, without production enumerators.

These intentionally avoid IdealPhysicalChain as the oracle for the general
catalog and avoid the production table sampler as a completion/count oracle.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product
import unittest

from contingency115.chain_diagnostics import stationary_variance
from contingency115.general_defect_chain import CompletionOracleContract, GeneralDefectChain
from contingency115.general_defect_terminal import GeneralRepairTerminal
from contingency115.general_neighbors import BalancedNeighborCatalog
from contingency115.ideal_chain import PhysicalState, build_rescaled_ideal_chain
from contingency115.kernels import ExactKernel, four_cycles, simple_cycles, heat_bath_kernel
from contingency115.mixtures import check_psd, certify_gap_lower_bound, fixed_mixture
from contingency115.tables import TableProblem, ProductWeights


class UnusedOracle:
    contract = CompletionOracleContract(0, 0, 0)

    def draw(self, request, context):
        raise AssertionError("geometry/count checks must not call a completion oracle")


def integer_tables(rows, columns):
    """Brute-force first rows, checking columns; no table-library search code."""
    if not rows:
        if not any(columns):
            yield ()
        return
    for row in product(*(range(min(rows[0], c) + 1) for c in columns)):
        if sum(row) == rows[0]:
            for rest in integer_tables(rows[1:], tuple(c-x for c, x in zip(columns, row))):
                yield (row,) + rest


def physical_states(rows, columns, U):
    cells = tuple((i, j) for i, r in enumerate(rows) for j, c in enumerate(columns)
                  if r < U or c < U)
    found = set()
    for x in product(range(U + 1), repeat=len(cells)):
        used = tuple(sum(v for (i, _), v in zip(cells, x) if i == k) for k in range(len(rows)))
        if any(v > r or (r < U and v != r) for v, r in zip(used, rows)):
            continue
        candidates = [x]
        for s in range(len(cells)):
            for t in range(len(cells)):
                if s != t and x[s] < U and x[t]:
                    q = list(x)
                    q[s] += 1
                    q[t] -= 1
                    candidates.append(tuple(q))
        for q in candidates:
            used = tuple(sum(v for (_, j), v in zip(cells, q) if j == k)
                         for k in range(len(columns)))
            if any(v > c or (c < U and v != c) for v, c in zip(used, columns)):
                continue
            found.add(PhysicalState(x, q))
    return cells, found


def crossing_repair(cells, state):
    delta = [q-x for x, q in zip(state.row_view, state.column_view)]
    s, t = delta.index(1), delta.index(-1)
    crossing = cells[t][0], cells[s][1]
    values = list(state.row_view)
    values[t] -= 1
    if crossing in cells:
        values[cells.index(crossing)] += 1
    return PhysicalState(tuple(values), tuple(values)), crossing


def graph_neighbors(cells, states, source):
    # A doubled-coordinate unit exchange is exactly L1 distance two here:
    # every physical profile has the same doubled-coordinate total.
    result = {target for target in states if target != source and
              sum(abs(a-b) for a, b in zip(source.row_view + source.column_view,
                                         target.row_view + target.column_view)) == 2}
    if source.row_view != source.column_view:
        result.add(crossing_repair(cells, source)[0])
    else:
        result.update(target for target in states if target.row_view != target.column_view
                      and crossing_repair(cells, target)[0] == source)
    return result


class IndependentMarkovAuditTests(unittest.TestCase):
    def test_all_small_integer_rectangles_have_the_stated_graph(self):
        # Includes zero margins, empty families, one-side-small layouts and
        # defect entries exactly U; all are generated from the margin equations.
        for m, n, values in ((2, 2, range(5)), (2, 3, range(4))):
            for rows in product(values, repeat=m):
                for columns in product(values, repeat=n):
                    if sum(rows) != sum(columns):
                        continue
                    cells, states = physical_states(rows, columns, 2)
                    if len(cells) < 2:
                        continue
                    chain = GeneralDefectChain(TableProblem(rows, columns), U=2, L=7,
                                               oracle=UnusedOracle(), geometry_bits=0, star_trials=0)
                    for state in states:
                        expected = graph_neighbors(cells, states, state)
                        if state.row_view == state.column_view:
                            catalog = BalancedNeighborCatalog(rows, columns, state, U=2, L=7)
                            actual = [catalog.unrank(i) for i in range(catalog.degree)]
                            for i, target in enumerate(actual):
                                self.assertEqual(catalog.rank(target), i)
                        else:
                            actual = [chain.proposal(state, slot) for slot in range(chain.Q)]
                            actual = [target for target in actual if target is not None]
                        with self.subTest(rows=rows, columns=columns, state=state):
                            self.assertEqual(set(actual), expected)
                            self.assertEqual(len(actual), len(expected))

    def test_ideal_state_and_completion_enumeration_from_integer_equations(self):
        for rows in product(range(5), repeat=2):
            for columns in product(range(5), repeat=2):
                if sum(rows) != sum(columns):
                    continue
                _, expected = physical_states(rows, columns, 2)
                chain = build_rescaled_ideal_chain(TableProblem(rows, columns), U=2, L=1)
                self.assertEqual(set(chain.states), expected)
                cardinalities = []
                for (rr, cc), actual in zip(chain.residual_margins, chain.completions):
                    completion_set = set(integer_tables(rr, cc)) if rr and cc else {()}
                    self.assertEqual(set(actual), completion_set)
                    cardinalities.append(len(completion_set))
                self.assertEqual(chain.stationary, tuple(F(c, sum(cardinalities)) for c in cardinalities))
                self.assertTrue(all(min(row) >= 0 and sum(row) == 1 for row in chain.matrix))
                for i, pi in enumerate(chain.stationary):
                    for j, pj in enumerate(chain.stationary):
                        self.assertEqual(pi * chain.matrix[i][j], pj * chain.matrix[j][i])

    def test_weighted_physical_transition_and_rejection_law_from_translated_pairs(self):
        rows = columns = (2, 2, 1)
        U, L = 2, 7
        cells, states = physical_states(rows, columns, U)
        chain = build_rescaled_ideal_chain(TableProblem(rows, columns), U=U, L=L)
        self.assertEqual(set(chain.states), states)
        large_rows = tuple(i for i, r in enumerate(rows) if r >= U)
        large_columns = tuple(j for j, c in enumerate(columns) if c >= U)
        residuals, completions = {}, {}
        for state in states:
            rr = tuple(rows[i] - sum(v for (a, _), v in zip(cells, state.row_view) if a == i)
                       + len(large_columns)*L for i in large_rows)
            cc = tuple(columns[j] - sum(v for (_, b), v in zip(cells, state.column_view) if b == j)
                       + len(large_rows)*L for j in large_columns)
            residuals[state] = rr, cc
            completions[state] = set(integer_tables(rr, cc))
        d = 10 + (len(rows)+1)*(len(columns)+1)
        denominator = 1
        while denominator < 32*d*d:
            denominator *= 2
        beta = F(1, denominator)
        total = sum(map(len, completions.values()))
        self.assertEqual(chain.stationary, tuple(F(len(completions[state]), total) for state in chain.states))
        saw_rejection = False
        for i, state in enumerate(chain.states):
            expected = [F(0)] * len(chain.states)
            rr, cc = residuals[state]
            for target in graph_neighbors(cells, states, state):
                tr, tc = residuals[target]
                accepted = 0
                for completion in completions[state]:
                    # Preserve every off-star entry, fill the first column to
                    # the target row totals, then the first row to its columns.
                    shifted = [list(row) for row in completion]
                    for a in range(1, len(tr)):
                        shifted[a][0] = tr[a] - sum(shifted[a][1:])
                    for b in range(1, len(tc)):
                        shifted[0][b] = tc[b] - sum(shifted[a][b] for a in range(1, len(tr)))
                    shifted[0][0] = tr[0] - sum(shifted[0][1:])
                    accepted += tuple(map(tuple, shifted)) in completions[target]
                expected[chain.states.index(target)] = beta*F(accepted, len(completions[state]))
                saw_rejection |= accepted < len(completions[state])
            expected[i] = 1-sum(expected)
            self.assertEqual(chain.matrix[i], tuple(expected))
        self.assertTrue(saw_rejection)

    def test_joint_terminal_fiber_counts_from_actual_output_preimages(self):
        for rows, columns, U, L in [((2, 2, 1), (2, 2, 1), 2, 7),
                                     ((3, 3, 1), (3, 3, 1), 3, 7),
                                     ((2, 1, 1), (2, 1, 1), 2, 1),
                                     ((1, 1), (1, 1), 2, 1),
                                     ((2, 2), (3, 1), 3, 1)]:
            cells, states = physical_states(rows, columns, U)
            chain = GeneralDefectChain(TableProblem(rows, columns), U=U, L=L,
                                       oracle=UnusedOracle(), geometry_bits=0, star_trials=0)
            terminal = GeneralRepairTerminal(chain, acceptance_bits=0)
            large_rows = tuple(i for i, r in enumerate(rows) if r >= U)
            large_columns = tuple(j for j, c in enumerate(columns) if c >= U)
            counts, formula = Counter(), {}
            for state in states:
                if state.row_view == state.column_view:
                    continue
                rr = tuple(rows[i] - sum(v for (a, _), v in zip(cells, state.row_view) if a == i)
                           + len(large_columns)*L for i in large_rows)
                cc = tuple(columns[j] - sum(v for (_, b), v in zip(cells, state.column_view) if b == j)
                           + len(large_rows)*L for j in large_columns)
                repaired, crossing = crossing_repair(cells, state)
                completions = integer_tables(rr, cc) if large_rows and large_columns else [()]
                for completion in completions:
                    dense = [list(row) for row in completion]
                    if crossing not in cells:
                        dense[large_rows.index(crossing[0])][large_columns.index(crossing[1])] += 1
                    if any(v < L for row in dense for v in row):
                        continue
                    output = [[0]*len(columns) for _ in rows]
                    for (i, j), value in zip(cells, repaired.row_view):
                        output[i][j] = value
                    for a, i in enumerate(large_rows):
                        for b, j in enumerate(large_columns):
                            output[i][j] = dense[a][b] - L
                    table = tuple(map(tuple, output))
                    counts[table] += 1
                    ell = terminal._successful_joint_fiber(repaired)
                    if table in formula:
                        self.assertEqual(formula[table], ell)
                    formula[table] = ell
            self.assertEqual(set(counts), set(integer_tables(rows, columns)))
            self.assertEqual(counts, formula)
            # Uniform joint mass followed by c/ell acceptance has one and the
            # same unnormalized table mass, despite different preimage counts.
            self.assertEqual({F(count*terminal.fiber_lower_bound, formula[table])
                              for table, count in counts.items()}, {F(terminal.fiber_lower_bound)})

    def test_weighted_heat_bath_and_fixed_mixture_against_closed_form_laws(self):
        problem = TableProblem((2, 2), (2, 2))
        states = tuple(((k, 2-k), (2-k, k)) for k in range(3))
        # Activity products are 15**(2-k)*14**k. The Poisson divisor is
        # k!**2*(2-k)!**2, giving independently evaluated integer ratios.
        for factorial, expected in ((False, (F(225, 631), F(210, 631), F(196, 631))),
                                    (True, (F(225, 1261), F(840, 1261), F(196, 1261)))):
            weights = ProductWeights(((2, 3), (5, 7)), factorial_weight=factorial)
            bath = heat_bath_kernel(problem, states, four_cycles(problem),
                                    weights=weights, hold_probability=F(1, 3))
            self.assertEqual(bath.stationary, expected)
            self.assertEqual(bath.matrix, tuple(tuple(F(i == j, 3) + F(2, 3)*p
                                                      for j, p in enumerate(expected)) for i in range(3)))
            identity = heat_bath_kernel(problem, states, (), weights=weights)
            mixture = fixed_mixture((bath, identity), (F(2, 5), F(3, 5)))
            self.assertEqual(mixture.matrix, tuple(tuple(F(11, 15)*int(i == j) + F(4, 15)*p
                                                         for j, p in enumerate(expected)) for i in range(3)))
            self.assertTrue(certify_gap_lower_bound(mixture, F(4, 15)).certified)
            self.assertFalse(certify_gap_lower_bound(mixture, F(1, 3)).certified)
        null_weights = ProductWeights(((0, 1), (1, 1)))
        bath = heat_bath_kernel(problem, states, four_cycles(problem), weights=null_weights)
        self.assertEqual(bath.stationary, (1, 0, 0))
        self.assertEqual(bath.matrix, ((1, 0, 0),)*3)
        # Off-diagonal support on 3x3 is a single six-cycle. Truncating at four
        # must expose disconnected singleton classes instead of assuming mixing.
        problem = TableProblem((1, 1, 1), (1, 1, 1), structural_zeros=((0, 0), (1, 1), (2, 2)))
        states = (((0, 0, 1), (1, 0, 0), (0, 1, 0)),
                  ((0, 1, 0), (0, 0, 1), (1, 0, 0)))
        short = heat_bath_kernel(problem, states, simple_cycles(problem, max_length=4))
        full = heat_bath_kernel(problem, states, simple_cycles(problem, max_length=6))
        self.assertEqual(short.matrix, ((1, 0), (0, 1)))
        self.assertEqual(short.communicating_classes(), ((0,), (1,)))
        self.assertEqual(full.matrix, ((F(1, 2), F(1, 2)),)*2)

    def test_psd_against_every_three_by_three_principal_minor(self):
        for a, b, c, d, e, f in product(range(-2, 3), repeat=6):
            minors = (a, d, f, a*d-b*b, a*f-c*c, d*f-e*e,
                      a*d*f + 2*b*c*e - a*e*e - d*c*c - f*b*b)
            expected = all(value >= 0 for value in minors)
            self.assertEqual(check_psd(((a, b, c), (b, d, e), (c, e, f))).is_psd, expected)

    def test_gap_boundary_and_periodic_disconnected_stationary_variance(self):
        # The two-state nontrivial eigenvalue is 1-a-b, including negative
        # values. This is the algebraic gap, with no absolute-gap substitution.
        for a, b in product((F(1, 4), F(1, 2), F(1)), repeat=2):
            kernel = ExactKernel((((0,),), ((1,),)), ((1-a, a), (b, 1-b)),
                                 (b/(a+b), a/(a+b)))
            self.assertTrue(certify_gap_lower_bound(kernel, a+b).certified)
            if a+b < 2:
                self.assertFalse(certify_gap_lower_bound(kernel, (2+a+b)/2).certified)
        # Equal component means, but a periodic component contributes zero
        # asymptotic variance while the persistent component contributes 9/4.
        matrix = ((0, 1, 0, 0, 0), (1, 0, 0, 0, 0),
                  (0, 0, F(3, 4), F(1, 4), 0), (0, 0, F(1, 4), F(3, 4), 0),
                  (1, 0, 0, 0, 0))
        kernel = ExactKernel(tuple(((i,),) for i in range(5)), matrix,
                             (F(1, 8), F(1, 8), F(3, 8), F(3, 8), 0))
        result = stationary_variance(kernel, (0, 2, 0, 2, 1000))
        self.assertEqual(result.component_means, (1, 1))
        self.assertEqual(result.between_class_variance, 0)
        self.assertEqual(result.asymptotic_variance, F(9, 4))


if __name__ == '__main__':
    unittest.main()
