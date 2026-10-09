import importlib.util
from pathlib import Path
from fractions import Fraction
import random
import sys
import unittest

path = Path(__file__).resolve().parents[1] / "experiments/sampler_benchmarks.py"
spec = importlib.util.spec_from_file_location("sampler_benchmarks", path)
b = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = b
spec.loader.exec_module(b)


class Benchmarks(unittest.TestCase):
    def test_uniform_full_line(self):
        case = b.cases()[0]
        states = tuple(b.ExactTableSampler(case.problem).tables())
        catalog = b.four_cycles(case.problem)
        class Ranks:
            def __init__(self, rank): self.rank = rank
            def randrange(self, stop): return 0 if stop == 1 else self.rank
        for state in states:
            reached = [b.step(case, state, catalog, Ranks(rank), b.new_work()) for rank in range(3)]
            self.assertEqual(set(reached), set(states))

    def test_sparse_negative_control(self):
        case = next(c for c in b.cases() if c.name == "sparse_six_cycle")
        table = b.ExactTableSampler(case.problem).unrank(0)
        work = b.new_work()
        self.assertEqual(b.step(case, table, (), random.Random(1), work), table)
        self.assertEqual(work["empty_catalog_holds"], 1)
        self.assertEqual(len(b.simple_cycles(case.problem)), 1)

    def test_rational_choice(self):
        class Rank:
            def __init__(self, rank): self.rank = rank
            def randrange(self, stop):
                assert stop == 3
                return self.rank
        self.assertEqual([b.rational_choice([Fraction(1, 3), Fraction(2, 3)], Rank(i))
                          for i in range(3)], [0, 1, 1])

    def test_diagnostics(self):
        a, z = ((1, 0), (0, 1)), ((0, 1), (1, 0))
        result = b.diagnostics([a, z], {a: Fraction(1, 2), z: Fraction(1, 2)}, 2, True)
        self.assertEqual(result["empirical_total_variation"], "0")
        self.assertEqual(result["ess_per_sampling_second"], 1)
        self.assertIsNone(b.heuristic_ess([1] * 10))

    def test_bad_configuration(self):
        with self.assertRaises(ValueError): b.run(draws=0)

    def test_weighted_transition_matches_exact_kernel(self):
        from contingency115.kernels import heat_bath_kernel
        case = b.Case("weighted", "test", b.TableProblem([2, 2], [2, 2]),
                      b.ProductWeights([[2, 1], [1, 1]], factorial_weight=True))
        states = tuple(b.ExactTableSampler(case.problem).tables())
        catalog = b.four_cycles(case.problem)
        kernel = heat_bath_kernel(case.problem, states, catalog, weights=case.weights)
        masses = [case.weights.table_weight(t) for t in states]
        denominator = b.lcm(*(m.denominator for m in masses))
        total = sum(m.numerator * (denominator // m.denominator) for m in masses)
        class Rank:
            def __init__(self, rank): self.rank = rank
            def randrange(self, stop): return 0 if stop == 1 else self.rank
        for i, state in enumerate(states):
            counts = b.Counter(b.step(case, state, catalog, Rank(rank), b.new_work())
                               for rank in range(total))
            self.assertEqual(tuple(Fraction(counts[t], total) for t in states), kernel.matrix[i])

    def test_seed_repetitions_survive_singleton_support(self):
        case = b.Case("singleton", "test", b.TableProblem([0, 1], [0, 1]))
        result = b.run_case(case, draws=2, warmup=0, repetitions=3, seed=5)
        self.assertEqual(result["distinct_starts"], 1)
        for method in result["methods"]:
            self.assertEqual([run["seed"] for run in method["runs"]], [5, 6, 7])

    def test_reducibility_is_explicit(self):
        case = next(c for c in b.cases() if c.name == "sparse_six_cycle")
        result = b.run_case(case, draws=3, warmup=2, repetitions=1, seed=1)
        frozen = next(m for m in result["methods"] if m["method"] == "rectangles")
        diagnostic = frozen["exact_stationary_diagnostic"]
        self.assertEqual(diagnostic["status"], "infinite_between_classes")
        self.assertEqual(diagnostic["between_class_mean_variance"], "9")
        self.assertIsNone(diagnostic["asymptotic_variance"])
        self.assertTrue(all(run["ess"] is None for run in frozen["runs"]))

    def test_exact_diagnostic_cap_is_reported(self):
        case = next(c for c in b.cases() if c.name == "few_modes_6x3")
        states = tuple(b.ExactTableSampler(case.problem).tables())
        self.assertEqual(b.exact_diagnostic(case, states, "rectangles")["status"], "budget_exceeded")

    def test_bad_rng_rank_and_negative_mass(self):
        class Bad:
            def randrange(self, stop): return -1
        with self.assertRaises(ValueError): b.rational_choice([Fraction(1)], Bad())
        with self.assertRaises(ValueError): b.rational_choice([Fraction(-1), Fraction(2)], Bad())

    def test_fixed_selection_weights_match_exact_kernel(self):
        from contingency115.kernels import heat_bath_kernel
        case = b.Case("mixture", "test", b.TableProblem([1] * 3, [1] * 3))
        states = tuple(b.ExactTableSampler(case.problem).tables())
        cycles = b.four_cycles(case.problem)[:2]
        catalog = b.FixedCatalog(cycles, (Fraction(1, 3), Fraction(2, 3)), (1, 2), 3)
        expected = heat_bath_kernel(case.problem, states, cycles, cycle_probabilities=catalog.probabilities)
        class Ranks:
            def __init__(self, first, second): self.values = iter((first, second))
            def randrange(self, stop):
                rank = next(self.values)
                assert 0 <= rank < stop
                return rank
        for i, state in enumerate(states):
            observed = b.Counter()
            for cycle_rank in range(3):
                cycle = cycles[0 if cycle_rank == 0 else 1]
                lo, hi = b.line_interval(case.problem, state, cycle)
                for line_rank in range(hi - lo + 1):
                    reached = b.step(case, state, catalog, Ranks(cycle_rank, line_rank), b.new_work())
                    observed[reached] += Fraction(1, 3 * (hi - lo + 1))
            self.assertEqual(tuple(observed[t] for t in states), expected.matrix[i])

    def test_worker_panel_uses_its_own_inverse_factorial_law(self):
        case = next(c for c in b.cases() if c.name == "ordinary_worker_2x2_4")
        result = b.run_case(case, draws=4, warmup=0, repetitions=1, seed=3)
        self.assertEqual(result["target_law"], "ordinary_inverse_factorial_tables")
        self.assertEqual(result["exact_metric_mean"], "2")
        self.assertEqual(result["exact_metric_variance"], "4/3")
        self.assertIn("worker_urn_iid", [m["method"] for m in result["methods"]])
        self.assertNotIn("worker_urn_iid", [m["method"] for m in b.run_case(b.cases()[0], 1, 0, 1, 1)["methods"]])

    def test_literal_steps_and_direct_censored_draws_are_distinct(self):
        case = next(c for c in b.cases() if c.name == "ideal_1_2x2")
        result = b.run_case(case, draws=3, warmup=0, repetitions=1, seed=1)
        methods = {m["method"]: m for m in result["methods"]}
        physical, direct = methods["ideal_physical_return"], methods["ideal_direct_return"]
        self.assertEqual(physical["exact_stationary_diagnostic"]["variance_inflation_factor"], "7679")
        self.assertEqual(physical["exact_stationary_diagnostic"]["expected_physical_steps_per_return_at_stationarity"], "7")
        self.assertTrue(all(r["sampling_work"]["physical_steps"] >= 3 for r in physical["runs"]))
        self.assertTrue(all(r["sampling_work"]["physical_steps"] == 0 for r in direct["runs"]))
        adapter = b.prepare_method(case, "ideal_physical_return")
        class ZeroRank:
            def randrange(self, stop): return 0
        work = b.new_work()
        with self.assertRaises(b.ComputationBudgetExceeded):
            b.advance(case, "ideal_physical_return", direct["runs"][0]["start"], adapter, ZeroRank(), work, physical_remaining=1)
        self.assertEqual(work["physical_steps"], 1)
        self.assertEqual(work["failed_excursion_steps"], 1)
        self.assertEqual(work["physical_completed_returns"], 0)

    def test_preparation_exhaustion_preserves_failed_run_receipt(self):
        from unittest.mock import patch
        case = b.cases()[0]
        with patch.object(b, "prepare_method", side_effect=b.ComputationBudgetExceeded("bounded setup")):
            failed = b.timed_run(case, "exact_dp", None, 5, 0, 1, {})
        self.assertEqual(failed["status"], "budget_exceeded")
        self.assertEqual(failed["failed_phase"], "preparation")
        self.assertEqual(failed["requested_outputs"], 5)
        self.assertEqual(failed["completed_outputs"], 0)
        self.assertGreaterEqual(failed["preparation_seconds"], 0)
        self.assertNotIn("ess", failed)

    def test_tiny_end_to_end(self):
        result = b.run_case(b.cases()[0], draws=4, warmup=1, repetitions=2, seed=1)
        self.assertEqual(result["table_count"], 3)
        self.assertEqual(len(result["methods"]), 2)
        for method in result["methods"]:
            self.assertEqual(len(method["runs"]), 2 if method["method"] == "exact_dp" else 12)
            self.assertTrue(all(run["completed_outputs"] == 4 for run in method["runs"]))


if __name__ == "__main__": unittest.main()
