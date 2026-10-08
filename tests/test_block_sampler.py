from collections import Counter
from fractions import Fraction
from itertools import product
import random
import unittest
from unittest.mock import patch

from contingency115.block_sampler import BlockSamplerBudget, BlockTableSampler, BlockWeightedSampler, _edge_blocks
from contingency115.kernels import simple_cycles
from contingency115.tables import (ComputationBudgetExceeded, ExactTableSampler, ExactWeightedTableSampler,
                                   InfeasibleTableError, ProductWeights, TableProblem, ZeroMassError)


def star_blocks(count=2, fixed_chord=0):
    columns = 3 * count
    upper = [[2] * columns] + [[2 if j // 3 == i else 0 for j in range(columns)] for i in range(count)]
    lower = [[0] * columns for _ in range(count + 1)]
    rows, cols = [3 * count] + [3] * count, [2] * columns
    if fixed_chord:
        upper[1][3] = lower[1][3] = fixed_chord
        rows[1] += fixed_chord
        cols[3] += fixed_chord
    return TableProblem(rows, cols, upper, lower)


def cycle_union_oracle(problem):
    m, n = problem.shape
    active = [[int(problem.upper_bounds[i][j] > problem.lower_bounds[i][j]) for j in range(n)] for i in range(m)]
    edges = {(i, j) for i in range(m) for j in range(n) if active[i][j]}
    parent = {edge: edge for edge in edges}
    def find(edge):
        while parent[edge] != edge:
            edge = parent[edge]
        return edge
    for cycle in simple_cycles(TableProblem([n] * m, [m] * n, active)):
        cells = [(i, j) for i, row in enumerate(cycle.signs) for j, value in enumerate(row) if value]
        first = find(cells[0])
        for cell in cells[1:]:
            parent[find(cell)] = first
    groups = {}
    for edge in edges:
        groups.setdefault(find(edge), set()).add(edge)
    return {frozenset(group) for group in groups.values()}


class NoRandom:
    def randrange(self, stop):
        raise AssertionError("RNG must not be called")


class BlockSamplerTests(unittest.TestCase):
    def compare_dp(self, problem, weights=None):
        sampler = BlockTableSampler(problem)
        oracle = ExactTableSampler(problem)
        self.assertEqual(sampler.count(), oracle.count())
        tables = tuple(sampler.tables())
        self.assertEqual(set(tables), set(oracle.tables()))
        for rank, table in enumerate(tables):
            self.assertEqual(sampler.rank(table), rank)
            for block in sampler.blocks:
                block.problem.validate_table(block.project(table))
        if weights is not None:
            weighted = BlockWeightedSampler(problem, weights)
            reference = ExactWeightedTableSampler(problem, weights)
            self.assertEqual(weighted.normalizer(), reference.normalizer())
            if weighted.normalizer():
                for table in tables:
                    self.assertEqual(weighted.probability(table), reference.probability(table))
            else:
                error = ZeroMassError if sampler.count() else InfeasibleTableError
                with self.assertRaises(error):
                    weighted.sample(NoRandom())
        return sampler

    def test_all_three_by_three_blocks_against_cycle_union_oracle(self):
        for allowed in product((0, 1), repeat=9):
            upper = tuple(allowed[3 * i:3 * i + 3] for i in range(3))
            problem = TableProblem(tuple(map(sum, upper)), tuple(sum(row[j] for row in upper) for j in range(3)), upper)
            self.assertEqual({frozenset(block) for block in _edge_blocks(problem)}, cycle_union_oracle(problem))

    def test_all_binary_two_by_three_supports_and_attainable_margins(self):
        for allowed in product((0, 1), repeat=6):
            margins = set()
            for values in product(*(range(cap + 1) for cap in allowed)):
                margins.add(((sum(values[:3]), sum(values[3:])), tuple(values[j] + values[3 + j] for j in range(3))))
            for rows, columns in margins:
                self.compare_dp(TableProblem(rows, columns, (allowed[:3], allowed[3:])))

    def test_complex_blocks_share_articulation_and_fixed_chord(self):
        for fixed in (0, 1, 5):
            problem = star_blocks(fixed_chord=fixed)
            weights = ProductWeights([[Fraction(i + j + 1, 3) for j in range(6)] for i in range(3)], True)
            sampler = self.compare_dp(problem, weights)
            self.assertEqual(sampler.count(), 49)
            self.assertEqual([block.method for block in sampler.blocks], ["dp", "dp"])
            self.assertEqual(sampler.stats["dp_states"], 18)
            self.assertEqual(sampler.stats["dp_transitions"], 28)
            self.assertTrue(all(table[1][3] == fixed for table in sampler.tables()))
        self.compare_dp(star_blocks(fixed_chord=2).transpose())

    def test_bridge_between_components_and_cycle_dp_hybrid(self):
        # K2,3 and a rectangle share row zero; the last row is a bridge leaf.
        problem = TableProblem([5, 3, 2, 1], [3, 2, 2, 2, 2],
                               [[2] * 5, [2, 2, 2, 0, 0], [0, 0, 0, 2, 2], [1, 0, 0, 0, 0]])
        sampler = self.compare_dp(problem, ProductWeights([[1] * 5 for _ in range(4)], True))
        self.assertEqual(sampler.count(), 21)
        self.assertEqual({block.method for block in sampler.blocks}, {"cycle", "dp"})
        self.assertTrue(all(table[3][0] == 1 for table in sampler.tables()))

    def test_disconnected_empty_and_zero_fibers(self):
        problem = TableProblem([2, 2, 2, 2], [2, 2, 2, 2],
                               [[2, 2, 0, 0], [2, 2, 0, 0], [0, 0, 2, 2], [0, 0, 2, 2]])
        self.assertEqual(self.compare_dp(problem).count(), 9)
        for problem in (TableProblem([1], [0]), TableProblem([1], [1], structural_zeros=[(0, 0)])):
            sampler = self.compare_dp(problem, ProductWeights([[1]]))
            with self.assertRaises(InfeasibleTableError):
                sampler.sample(NoRandom())
        for problem in (TableProblem([0, 0], [0, 0, 0]), TableProblem([2, 3], [5])):
            sampler = self.compare_dp(problem)
            self.assertEqual(sampler.sample(NoRandom()), sampler.unrank(0))

    def test_seeded_bounded_product_laws_and_zero_activities(self):
        rng = random.Random(115_2026_10_10)
        for _ in range(80):
            upper = [[rng.randrange(3) for _ in range(4)] for _ in range(3)]
            lower = [[rng.randrange(cap + 1) for cap in row] for row in upper]
            witness = [[rng.randint(lower[i][j], upper[i][j]) for j in range(4)] for i in range(3)]
            problem = TableProblem(tuple(map(sum, witness)), tuple(sum(row[j] for row in witness) for j in range(4)), upper, lower)
            activities = [[Fraction(rng.randrange(4), rng.randrange(1, 4)) for _ in range(4)] for _ in range(3)]
            for factorial in (False, True):
                self.compare_dp(problem, ProductWeights(activities, factorial))

    def test_shared_and_per_block_dp_limits_are_distinct_and_sticky(self):
        problem = star_blocks()
        for options, expected_states, expected_transitions in (
            ({"max_dp_states_total": 17}, 17, None),
            ({"max_dp_states_per_block": 8}, 8, None),
            ({"max_dp_transitions_total": 27}, None, 27),
            ({"max_dp_transitions_per_block": 13}, None, 13),
        ):
            sampler = BlockTableSampler(problem, budget=BlockSamplerBudget(**options))
            with self.assertRaises(ComputationBudgetExceeded):
                sampler.sample(NoRandom())
            stats = sampler.stats
            self.assertTrue(stats["failed"])
            self.assertFalse(stats["complete"])
            if expected_states is not None:
                self.assertEqual(stats["dp_states"], expected_states)
            if expected_transitions is not None:
                self.assertEqual(stats["dp_transitions"], expected_transitions)
            with self.assertRaises(ComputationBudgetExceeded):
                sampler.count()
            self.assertEqual(stats, sampler.stats)
        success = BlockTableSampler(problem, budget=BlockSamplerBudget(max_dp_states_total=18, max_dp_transitions_total=28))
        self.assertEqual(success.count(), 49)

    def test_shared_cycle_preparation_limit_and_weight_preflight(self):
        problem = TableProblem([4, 2, 2], [2] * 4, [[2] * 4, [2, 2, 0, 0], [0, 0, 2, 2]])
        weights = ProductWeights([[1] * 4 for _ in range(3)], True)
        sampler = BlockWeightedSampler(problem, weights, budget=BlockSamplerBudget(max_cycle_line_states_total=5))
        with self.assertRaises(ComputationBudgetExceeded):
            sampler.sample(NoRandom())
        self.assertEqual(sampler.stats["cycle_line_states"], 3)
        self.assertEqual(sampler.stats["prepared_factors"], 1)
        with self.assertRaises(ComputationBudgetExceeded):
            sampler.normalizer()
        for options in ({"max_weight_cell_value": 1}, {"max_raw_cell_weight_bits": 1}):
            sampler = BlockWeightedSampler(problem, weights, budget=BlockSamplerBudget(**options))
            with patch.object(ProductWeights, "cell_weight", side_effect=AssertionError("preflight must precede powers/factorials")):
                with self.assertRaises(ComputationBudgetExceeded):
                    sampler.sample(NoRandom())

    def test_weighted_dp_failure_precedes_any_rng(self):
        problem = star_blocks()
        sampler = BlockWeightedSampler(problem, ProductWeights([[1] * 6 for _ in range(3)], True),
                                        budget=BlockSamplerBudget(max_dp_states_total=17))
        with self.assertRaises(ComputationBudgetExceeded):
            sampler.sample(NoRandom())
        self.assertEqual(sampler.stats["dp_states"], 17)
        self.assertFalse(sampler.stats["complete"])

    def test_exact_weighted_random_choice_tree(self):
        problem = star_blocks()
        sampler = BlockWeightedSampler(problem, ProductWeights([[1] * 6 for _ in range(3)], True))
        class NeedChoice(Exception):
            def __init__(self, stop):
                self.stop = stop
        class Tape:
            def __init__(self, prefix):
                self.prefix, self.index = prefix, 0
            def randrange(self, stop):
                if self.index == len(self.prefix):
                    raise NeedChoice(stop)
                value = self.prefix[self.index]
                self.index += 1
                return value
        probabilities = Counter()
        queue = [((), Fraction(1))]
        while queue:
            prefix, probability = queue.pop()
            try:
                table = sampler.sample(Tape(prefix))
            except NeedChoice as request:
                self.assertLessEqual(request.stop, 10)
                queue.extend((prefix + (choice,), probability / request.stop) for choice in range(request.stop))
            else:
                probabilities[table] += probability
        self.assertEqual(len(probabilities), 49)
        self.assertEqual(sum(probabilities.values()), 1)
        for table, probability in probabilities.items():
            self.assertEqual(probability, sampler.probability(table))

    def test_huge_cycle_width_and_many_small_complex_blocks(self):
        width = 2**200 + 17
        sampler = BlockTableSampler(TableProblem([width, width], [width, width]))
        self.assertEqual(sampler.count(), width + 1)
        self.assertEqual(sampler.stats["dp_states"], 0)
        for rank in (0, width // 2, width):
            self.assertEqual(sampler.rank(sampler.unrank(rank)), rank)
        many = BlockTableSampler(star_blocks(20))
        self.assertEqual(many.count(), 7**20)
        self.assertEqual(many.stats["dp_states"], 180)
        self.assertEqual(many.stats["dp_transitions"], 280)
        self.assertEqual(many.rank(many.unrank(many.count() - 1)), many.count() - 1)

    def test_correlated_uniform_marginals_do_not_satisfy_rng_contract(self):
        problem = star_blocks()
        sampler = BlockWeightedSampler(problem, ProductWeights([[1] * 6 for _ in range(3)], True))
        observed = Counter()
        class ReuseUniformRank:
            def __init__(self, value):
                self.value = value
                self.nontrivial_calls = 0
            def randrange(self, stop):
                if stop == 1:
                    return 0
                if stop != 10:
                    raise AssertionError(stop)
                self.nontrivial_calls += 1
                return self.value
        for value in range(10):
            rng = ReuseUniformRank(value)
            observed[sampler.sample(rng)] += 1
            self.assertEqual(rng.nontrivial_calls, 2)
        # Each nontrivial integer draw separately has a uniform marginal over
        # these ten equally weighted runs, but the two factor choices agree.
        self.assertEqual(len(observed), 7)
        self.assertEqual(BlockTableSampler(problem).count(), 49)
        self.assertTrue(any(Fraction(count, 10) != sampler.probability(table) for table, count in observed.items()))

    def test_zero_mass_and_bad_inputs(self):
        problem = star_blocks(fixed_chord=1)
        activities = [[1] * 6 for _ in range(3)]
        activities[1][3] = 0
        sampler = BlockWeightedSampler(problem, ProductWeights(activities, True))
        self.assertEqual(sampler.normalizer(), 0)
        with self.assertRaises(ZeroMassError):
            sampler.sample(NoRandom())
        self.assertEqual(sampler.stats["prepared_factors"], 0)
        with self.assertRaises(ComputationBudgetExceeded):
            BlockTableSampler(problem, budget=BlockSamplerBudget(max_cells=1))
        with self.assertRaises(TypeError):
            BlockSamplerBudget(max_dp_states_total=True)
        with self.assertRaises(ValueError):
            BlockSamplerBudget(max_dp_states_total=0)
        with self.assertRaises(TypeError):
            BlockTableSampler(problem, budget={})
        with self.assertRaises(ValueError):
            BlockWeightedSampler(problem, ProductWeights([[1]]))
        uniform = BlockTableSampler(problem)
        with self.assertRaises(IndexError):
            uniform.unrank(49)
        with self.assertRaises(TypeError):
            uniform.unrank(True)
        with self.assertRaises(ComputationBudgetExceeded):
            uniform.tables(max_tables=48)


if __name__ == "__main__":
    unittest.main()
