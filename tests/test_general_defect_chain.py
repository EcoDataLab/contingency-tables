"""Exact finite-word laws and bounded callback contracts for one trace step."""

from collections import Counter, defaultdict
from fractions import Fraction as F
import unittest

from contingency115.general_defect_chain import (CompletionOracleContract, CompletionRequest, GeneralDefectBudget,
                                                 GeneralDefectChain, defect_degree_bound)
from contingency115.general_neighbors import BalancedNeighborCatalog
from contingency115.ideal_chain import PhysicalState, build_rescaled_ideal_chain
from contingency115.kernels import ExactKernel
from contingency115.tables import ComputationBudgetExceeded, TableProblem


class Words:
    def __init__(self, *words):
        self.words, self.widths = iter(words), []

    def getrandbits(self, bits):
        self.widths.append(bits)
        return next(self.words)


class PoolOracle:
    """Finite TEST oracle; enumeration lives in the existing tiny reference."""
    def __init__(self, backend, bits=1, failure=False):
        self.pools = dict(zip(backend.residual_margins, backend.completions))
        self.bits, self.failure = bits, failure
        width = 1 << bits
        error = max(F((width % len(pool))*(len(pool)-width % len(pool)), len(pool)*width)
                    for pool in self.pools.values())
        self.contract = CompletionOracleContract(1 if failure else error, bits, 1)

    def draw(self, request, context):
        context.charge(1)
        word = context.word(self.bits)
        if self.failure and word:
            return None
        pool = self.pools[request.row_sums,request.column_sums]
        return pool[len(pool)*word//(1 << self.bits)]


class NeedWord(Exception):
    def __init__(self, bits):
        self.bits = bits


class PrefixWords:
    def __init__(self, prefix):
        self.prefix, self.index = prefix, 0

    def getrandbits(self, bits):
        if self.index == len(self.prefix):
            raise NeedWord(bits)
        expected,value = self.prefix[self.index]
        assert expected == bits
        self.index += 1
        return value


def finite_word_row(chain, state):
    """Enumerate the actual adaptive finite decision tree, with rational masses."""
    law = defaultdict(F)
    pending = [((),F(1))]
    while pending:
        prefix,mass = pending.pop()
        try:
            result = chain.step(state,PrefixWords(prefix))
        except NeedWord as request:
            width = 1 << request.bits
            pending.extend((prefix+((request.bits,word),),mass/width) for word in range(width))
        else:
            law[result.state] += mass
    return dict(law)


def ideal_trace_row(backend, index, beta):
    defects = [j for j,s in enumerate(backend.states) if not s.balanced]
    law = defaultdict(F)
    weight = backend.completion_counts[index]
    for neighbor in backend.neighbors[index]:
        entry = beta*backend.acceptance_counts[index][neighbor]/weight
        if not backend.states[neighbor].balanced:
            law[backend.states[neighbor]] += entry
        else:
            total = sum(backend.acceptance_counts[neighbor][j] for j in backend.neighbors[neighbor])
            for target in backend.neighbors[neighbor]:
                law[backend.states[target]] += entry*backend.acceptance_counts[neighbor][target]/total
    law[backend.states[index]] += 1-sum(law.values())
    return dict(law),defects


class GeneralDefectChainTests(unittest.TestCase):
    def test_canonical_slots_and_source_acceptance_match_actual_backend(self):
        fixtures = [((2,1),(2,1),2,1), ((4,4,1),(4,4,1),4,3),
                    ((2,2,1),(2,2,1),2,3), ((2,2),(3,1),3,1),
                    ((3,1),(2,2),3,1), ((2,0,0),(2,0,0),2,1)]
        saw_boundary = saw_two_centers = saw_rejection = False
        for rows,columns,U,L in fixtures:
            backend = build_rescaled_ideal_chain(TableProblem(rows,columns),U=U,L=L)
            chain = GeneralDefectChain(backend.problem,U=U,L=L,oracle=PoolOracle(backend),
                                       geometry_bits=1,star_trials=2)
            for index,state in enumerate(backend.states):
                self.assertEqual(chain.residual_margins(state),backend.residual_margins[index])
                if state.balanced:
                    continue
                slots = [chain.proposal(state,slot) for slot in range(chain.Q)]
                neighbors = [target for target in slots if target is not None]
                expected = {backend.states[j] for j in backend.neighbors[index]}
                self.assertEqual(set(neighbors),expected)
                self.assertEqual(len(neighbors),len(expected))
                saw_two_centers |= sum(target.balanced for target in neighbors)==2
                saw_boundary |= U in state.row_view or U in state.column_view
                self.assertIn(chain.repair(state),expected)
                for target in backend.neighbors[index]:
                    for completion in backend.completions[index]:
                        actual = chain.source_accepts(state,backend.states[target],completion)
                        self.assertEqual(actual,backend.completion_passes(index,target,completion))
                        saw_rejection |= not actual
        self.assertTrue(saw_boundary and saw_two_centers and saw_rejection)

    def test_exact_finite_word_kernel_equals_ideal_when_draws_are_exact(self):
        backend = build_rescaled_ideal_chain(TableProblem((2,1),(2,1)),U=2,L=1)
        oracle = PoolOracle(backend,bits=0)  # one-cell completion is deterministic
        chain = GeneralDefectChain(backend.problem,U=2,L=1,oracle=oracle,geometry_bits=2,star_trials=1)
        defects = [j for j,state in enumerate(backend.states) if not state.balanced]
        matrix = []
        for index in defects:
            ideal,_ = ideal_trace_row(backend,index,chain.beta)
            actual = finite_word_row(chain,backend.states[index])
            self.assertEqual(actual,ideal)  # four-neighbor stars have exact 2-bit ranks
            matrix.append(tuple(actual.get(backend.states[j],F(0)) for j in defects))
        stationary = tuple(F(backend.completion_counts[j],sum(backend.completion_counts[k] for k in defects))
                           for j in defects)
        kernel = ExactKernel(tuple(backend.states[j] for j in defects),tuple(matrix),stationary)
        self.assertTrue(kernel.is_stochastic())
        self.assertTrue(kernel.satisfies_detailed_balance())

    def test_weighted_finite_word_rows_obey_declared_trace_error(self):
        backend = build_rescaled_ideal_chain(TableProblem((4,4,1),(4,4,1)),U=4,L=3)
        chain = GeneralDefectChain(backend.problem,U=4,L=3,oracle=PoolOracle(backend,bits=1),
                                   geometry_bits=0,star_trials=2)
        saw_difference = False
        for index,state in enumerate(backend.states):
            if state.balanced:
                continue
            ideal,defects = ideal_trace_row(backend,index,chain.beta)
            actual = finite_word_row(chain,state)
            self.assertEqual(sum(actual.values()),1)
            self.assertGreaterEqual(actual[state],F(1,2))
            self.assertTrue(all(not target.balanced for target in actual))
            tv = sum(abs(actual.get(backend.states[j],0)-ideal.get(backend.states[j],0)) for j in defects)/2
            self.assertLessEqual(tv,chain.error.total_variation_bound)
            saw_difference |= tv>0
        self.assertTrue(saw_difference)
        eps = chain.oracle_contract.tv_error
        self.assertEqual(chain.error.initial_oracle,chain.Q*chain.beta*eps)
        self.assertEqual(chain.error.star_oracle,4*chain.beta*eps)
        self.assertEqual(chain.error.star_cap,2*chain.beta/F(4))

    def test_star_cap_failure_fresh_words_and_actual_work(self):
        backend = build_rescaled_ideal_chain(TableProblem((2,1),(2,1)),U=2,L=1)
        chain = GeneralDefectChain(backend.problem,U=2,L=1,oracle=PoolOracle(backend,failure=True),
                                   geometry_bits=2,star_trials=2)
        state = next(state for state in backend.states if not state.balanced)
        slot = next(slot for slot in range(chain.Q) if (target:=chain.proposal(state,slot)) is not None and target.balanced)
        rng = Words(slot,0,0,1,3,1)
        cap = chain.step(state,rng)
        self.assertEqual((cap.state,cap.outcome,cap.star_trials),(state,"star_cap",2))
        self.assertEqual((cap.oracle_calls,cap.oracle_failures,cap.oracle_work),(3,2,3))
        self.assertEqual(cap.fair_bits,chain.proposal_bits+7)
        self.assertEqual(rng.widths,[chain.proposal_bits,1,2,1,2,1])
        exited = chain.step(state,Words(slot,0,0,1,3,0))
        center = chain.proposal(state,slot)
        catalog = BalancedNeighborCatalog(backend.problem.row_sums,backend.problem.column_sums,center,U=2,L=1)
        self.assertEqual(exited.state,catalog.unrank(3))
        self.assertEqual((exited.outcome,exited.star_trials),("star_exit",2))
        failure = chain.step(state,Words(slot,1))
        self.assertEqual((failure.state,failure.outcome,failure.oracle_calls),(state,"oracle_failure",1))

    def test_empty_rectangle_bypass_and_immutable_oracle_outputs(self):
        backend = build_rescaled_ideal_chain(TableProblem((1,1),(1,1)),U=2,L=1)
        oracle = PoolOracle(backend,bits=0)
        oracle.draw = lambda request,context: (_ for _ in ()).throw(AssertionError("empty oracle must be bypassed"))
        chain = GeneralDefectChain(backend.problem,U=2,L=1,oracle=oracle,geometry_bits=2,star_trials=1)
        state = next(state for state in backend.states if not state.balanced)
        draw = chain.draw_completion(state,Words())
        self.assertEqual((draw.completion,draw.oracle_calls,draw.fair_bits),((),0,0))
        result = chain.step(state,Words((1 << chain.proposal_bits)-1))
        self.assertEqual((result.outcome,result.oracle_calls),("proposal_hold",0))
        row_view,column_view = list(state.row_view),list(state.column_view)
        snapshot = chain.validate_state(PhysicalState(row_view,column_view),require_defect=True)
        row_view[:] = column_view[:] = [0]*len(row_view)
        self.assertEqual(snapshot,state)
        bad = PhysicalState(state.row_view,tuple(float(v) for v in state.column_view))
        with self.assertRaises(TypeError): chain.validate_state(bad)
        with self.assertRaises(TypeError): chain.locations[chain.cells[0]] = 99
        with self.assertRaises(AttributeError): chain.U = 99
        with self.assertRaises(AttributeError): chain.oracle_contract = CompletionOracleContract(0,0,0)
        mixed = build_rescaled_ideal_chain(TableProblem((2,1),(2,1)),U=2,L=1)
        mutable = [list(row) for row in mixed.completions[0][0]]
        callback = PoolOracle(mixed,bits=0)
        callback.draw = lambda request,context: mutable
        owned = GeneralDefectChain(mixed.problem,U=2,L=1,oracle=callback,geometry_bits=0,star_trials=0)
        result = owned.draw_completion(mixed.states[0],Words())
        mutable[0][0] = 0
        self.assertEqual(result.completion,mixed.completions[0][0])

    def test_cooperative_oracle_caps_and_schedule_preflight(self):
        backend = build_rescaled_ideal_chain(TableProblem((2,1),(2,1)),U=2,L=1)
        oracle = PoolOracle(backend,bits=1)
        chain = GeneralDefectChain(backend.problem,U=2,L=1,oracle=oracle,geometry_bits=1,star_trials=1)
        oracle.draw = lambda request,context: context.word(2)
        rng = Words()
        with self.assertRaises(ComputationBudgetExceeded): chain.draw_completion(backend.states[0],rng)
        self.assertEqual(rng.widths,[])
        oracle.draw = lambda request,context: context.charge(2)
        with self.assertRaises(ComputationBudgetExceeded): chain.draw_completion(backend.states[0],Words())
        for budget in (GeneralDefectBudget(max_star_trials=1),GeneralDefectBudget(max_oracle_calls=1),
                       GeneralDefectBudget(max_fair_bits=1),GeneralDefectBudget(max_oracle_work=1)):
            with self.assertRaises(ComputationBudgetExceeded):
                GeneralDefectChain(backend.problem,U=2,L=1,oracle=PoolOracle(backend),
                                   geometry_bits=1,star_trials=2,budget=budget)

    def test_scope_padding_and_malformed_completion(self):
        backend = build_rescaled_ideal_chain(TableProblem((2,1),(2,1)),U=2,L=1)
        oracle = PoolOracle(backend)
        for problem,U,L in [(TableProblem((4,4,1),(4,4,1)),4,1),
                             (TableProblem((2,2),(2,2)),2,1),
                             (TableProblem((2,1),(2,1),structural_zeros=[(0,0)]),2,1)]:
            with self.assertRaises(ValueError):
                GeneralDefectChain(problem,U=U,L=L,oracle=oracle,geometry_bits=1,star_trials=1)
        chain = GeneralDefectChain(backend.problem,U=2,L=1,oracle=oracle,geometry_bits=0,star_trials=0)
        for malformed in ([[True]],[[1.0]],[[0]],(),iter(()),(iter((1,)),),((1,2),)):
            oracle.draw = lambda request,context,value=malformed: value
            with self.assertRaises((TypeError,ValueError)):
                chain.draw_completion(backend.states[0],Words())
        for error in (-1,F(11,10),0.1):
            with self.assertRaises((TypeError,ValueError)):
                CompletionOracleContract(error,1,1)
        rows,columns = [1],[1]
        request = CompletionRequest(rows,columns,2)
        rows[0] = columns[0] = 0
        self.assertEqual((request.row_sums,request.column_sums),((1,),(1,)))
        with self.assertRaises(TypeError): CompletionRequest((True,),(1,),2)

    def test_constant_padding_gate_for_large_completion_rectangle(self):
        class UnavailableOracle:
            contract = CompletionOracleContract(F(1), 0, 0)

            def draw(self, request, context):
                return None

        problem = TableProblem((2, 2, 2, 2, 2, 1), (2, 2, 2, 2, 2, 1))
        # The older residual-floor test would require L >= ceil(48/5)=10.
        with self.assertRaises(ValueError):
            GeneralDefectChain(problem, U=2, L=6, oracle=UnavailableOracle(),
                               geometry_bits=0, star_trials=0)
        chain = GeneralDefectChain(problem, U=2, L=7, oracle=UnavailableOracle(),
                                   geometry_bits=0, star_trials=0)
        self.assertEqual((len(chain.large_rows), len(chain.large_columns)), (5, 5))
        self.assertEqual(chain.oracle_contract.tv_error, 1)

    def test_compact_global_shape_bound_and_sparse_storage(self):
        self.assertEqual(defect_degree_bound(3,3,1,1),11)
        self.assertEqual(defect_degree_bound(100,100,98,98),981)
        self.assertEqual(defect_degree_bound(2,2,2,2),5)
        self.assertEqual(defect_degree_bound(3,2,3,1),7)
        for args in ((1,2,1,1),(2,2,3,1),(2,2,0,0),(2,2,True,1),(2,2,1.0,1)):
            with self.assertRaises((TypeError,ValueError)):
                defect_degree_bound(*args)
        backend = build_rescaled_ideal_chain(TableProblem((70,70,1),(70,70,1)),U=70,L=3)
        chain = GeneralDefectChain(backend.problem,U=70,L=3,oracle=PoolOracle(backend),
                                   geometry_bits=1,star_trials=1)
        self.assertEqual((chain.Q,chain.beta),(11,F(1,32)))
        for index,state in enumerate(backend.states):
            if state.balanced: continue
            descriptors = chain.proposal_descriptors(state)
            self.assertLessEqual(len(descriptors),chain.Q)
            self.assertTrue(all(move is None or (len(move)==2 and all(isinstance(v,int) for v in move))
                                for move in descriptors))
            targets = [chain.proposal(state,slot) for slot in range(chain.Q)]
            targets = [target for target in targets if target is not None]
            self.assertEqual(set(targets),{backend.states[j] for j in backend.neighbors[index]})
            self.assertEqual(len(targets),len(set(targets)))
            self.assertIsNone(chain.proposal(state,chain.Q))

    def test_unused_geometry_precision_does_not_allocate_word_budget(self):
        backend = build_rescaled_ideal_chain(TableProblem((2,1),(2,1)),U=2,L=1)
        chain = GeneralDefectChain(backend.problem,U=2,L=1,oracle=PoolOracle(backend,bits=0),
                                   geometry_bits=10**9,star_trials=0,
                                   budget=GeneralDefectBudget(max_fair_bits=16))
        self.assertEqual(chain.error.geometry_rounding,0)
        self.assertEqual(chain.max_fair_bits,chain.proposal_bits)


if __name__ == "__main__":
    unittest.main()
