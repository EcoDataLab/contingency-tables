"""Bounded independent deep-review checks; no existing test oracle is used."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from math import factorial
import random

from contingency115.tables import TableProblem, ProductWeights, ExactTableSampler, ExactWeightedTableSampler, ZeroMassError, InfeasibleTableError
from contingency115.block_sampler import BlockTableSampler, BlockWeightedSampler
from contingency115.small_completion import SmallCompletionOracle
from contingency115.general_defect_chain import CompletionRequest, CompletionContext, _Execution
from contingency115.lattice_completion import plan_lattice_completion, encode_completion, decode_completion, geometric_count_envelope

rng = random.Random(834791)
checks = Counter()

def matrix(flat, m, n):
    return tuple(tuple(flat[i*n:(i+1)*n]) for i in range(m))

def margins(t):
    return tuple(map(sum, t)), tuple(map(sum, zip(*t)))

def weight(t, activities, fact):
    result = F(1)
    for i, row in enumerate(t):
        for j, value in enumerate(row):
            result *= activities[i][j] ** value
            if fact:
                result /= factorial(value)
    return result

# Each candidate is generated cell-by-cell, independently of row DP or max flow.
for m, n, top, trials in ((1, 3, 2, 100), (3, 1, 2, 100), (2, 2, 2, 500), (2, 3, 2, 500), (3, 3, 2, 1000)):
    fibers = defaultdict(list)
    for flat in product(range(top+1), repeat=m*n):
        t = matrix(flat, m, n)
        fibers[margins(t)].append(t)
    all_keys = tuple(fibers)
    for trial in range(trials):
        rows, cols = rng.choice(all_keys)
        if trial % 10 == 0:
            rows = tuple(x + 1 if i == 0 else x for i, x in enumerate(rows))
        upper = matrix(tuple(rng.randrange(top+1) for _ in range(m*n)), m, n)
        lower = tuple(tuple(rng.randrange(upper[i][j]+1) for j in range(n)) for i in range(m))
        if trial % 4 == 0:
            lower = ((0,)*n,)*m
            upper = ((top,)*n,)*m
        zero_cells = [(i,j) for i in range(m) for j in range(n) if rng.randrange(20) == 0]
        p = TableProblem(rows, cols, upper, lower, zero_cells)
        expected = [t for t in fibers.get((rows,cols), []) if all(lower[i][j] <= t[i][j] <= upper[i][j] and ((i,j) not in zero_cells or t[i][j] == 0) for i in range(m) for j in range(n))]
        feasibility = p.feasibility()
        assert feasibility.feasible == bool(expected), (p, expected, feasibility)
        if expected:
            assert feasibility.table in expected
        for problem in (p, p.transpose()):
            want = expected if problem is p else [tuple(zip(*t)) for t in expected]
            for sampler_type in (ExactTableSampler, BlockTableSampler):
                sampler = sampler_type(problem)
                assert sampler.count() == len(want), (sampler_type, problem, want, sampler.count())
                seen = set()
                for rank in range(len(want)):
                    t = sampler.unrank(rank)
                    assert t in want
                    assert sampler.rank(t) == rank
                    seen.add(t)
                assert seen == set(want)
                checks['uniform_rank_tables'] += len(want)
                checks['uniform_cases'] += 1
        activities = tuple(tuple(rng.choice((F(0), F(1,2), F(1), F(2), F(3,2))) for j in range(n)) for i in range(m))
        for fact in (False, True):
            expected_mass = {t:weight(t, activities, fact) for t in expected}
            normalizer = sum(expected_mass.values(), F(0))
            w = ProductWeights(activities, fact)
            for sampler_type in (ExactWeightedTableSampler, BlockWeightedSampler):
                sampler = sampler_type(p, w)
                assert sampler.normalizer() == normalizer, (sampler_type, p, activities, fact, normalizer, sampler.normalizer())
                if normalizer:
                    for t in expected:
                        assert sampler.probability(t) == expected_mass[t]/normalizer, (sampler_type, p, t)
                    for _ in range(2):
                        assert expected_mass[sampler.sample(rng)] > 0
                else:
                    try:
                        sampler.sample(rng)
                    except (ZeroMassError if expected else InfeasibleTableError):
                        pass
                    else:
                        raise AssertionError('zero mass sample did not raise')
                checks['weighted_probabilities'] += len(expected) if normalizer else 0
                checks['weighted_cases'] += 1
    print('table shape complete', (m,n), dict(checks), flush=True)

class Word:
    def __init__(self, value): self.value = value
    def getrandbits(self, bits): return self.value

# Derive the expected fiber from Cartesian cells; count output words directly.
for m,n in ((0,0),(0,3),(3,0),(1,3),(3,1),(2,2)):
    for capacity in range(4):
        fibers = defaultdict(list)
        for flat in product(range(capacity+1), repeat=m*n):
            if not m or not n:
                rows,cols = (0,)*m,(0,)*n
                fibers[(rows,cols)] = [()]
            else:
                t = matrix(flat,m,n)
                fibers[margins(t)].append(t)
        for (rows,cols), expected in fibers.items():
            for bits in range(5):
                oracle = SmallCompletionOracle(max(rows+cols, default=0), bits)
                request = CompletionRequest(rows,cols,capacity)
                outcomes = Counter()
                for word in range(1<<bits):
                    context = CompletionContext(_Execution(Word(word), bits), oracle.contract)
                    outcomes[oracle.draw(request, context)] += 1
                    assert context.work_units <= oracle.contract.max_work_units
                assert set(outcomes) <= set(expected)
                tv = sum((abs(F(outcomes[t],1<<bits)-F(1,len(expected))) for t in expected), F(0))/2
                assert tv == oracle.request_tv_error(request), (request,bits,tv,oracle.request_tv_error(request))
                assert tv <= oracle.contract.tv_error
                checks['small_completion_requests'] += 1
    print('small shape complete', (m,n), dict(checks), flush=True)

def independent_fine_tables(rows, cols):
    if len(rows) == 1:
        yield (cols,)
    elif len(cols) == 1:
        yield tuple((r,) for r in rows)
    elif len(rows) == 2:
        for top in product(*(range(c+1) for c in cols)):
            if sum(top) == rows[0]:
                yield (top, tuple(c-x for c,x in zip(cols,top)))
    elif len(cols) == 2:
        for left in product(*(range(r+1) for r in rows)):
            if sum(left) == cols[0]:
                yield tuple((x,r-x) for r,x in zip(rows,left))
    else:
        raise AssertionError('independent fine oracle is for thin rectangles')

# Enumerate full fine fibers directly from row/column coordinates, without DP.
for rows,cols in (((0,),(0,)), ((0,),(0,0)), ((2,),(0,2)), ((0,0),(0,0)), ((1,1),(1,1)), ((0,2),(1,1)), ((0,0),(0,0,0)), ((1,2),(1,1,1)), ((1,1,1),(1,2))):
    original = TableProblem(rows,cols)
    original_tables = []
    for flat in product(range(max(rows+cols)+1),repeat=len(rows)*len(cols)):
        t=matrix(flat,len(rows),len(cols))
        if margins(t)==(rows,cols): original_tables.append(t)
    for k in (1,2,3):
        plan=plan_lattice_completion(original,k)
        fine_tables=independent_fine_tables(plan.fine.row_sums,plan.fine.column_sums)
        accepted=Counter()
        for fine in fine_tables:
            decoded=decode_completion(plan,fine)
            assert all(abs(error)<2 for row in decoded.rounding_errors for error in row)
            if decoded.accepted:
                assert decoded.table in original_tables
                assert encode_completion(plan,decoded.table,decoded.offsets)==fine
                accepted[decoded.table]+=1
        assert accepted==Counter({t:k**plan.dimension for t in original_tables}), (rows,cols,k,accepted)
        for t in original_tables:
            for flat in product(range(k),repeat=plan.dimension):
                offsets=matrix(flat,len(rows)-1,len(cols)-1)
                fine=encode_completion(plan,t,offsets)
                decoded=decode_completion(plan,fine)
                assert decoded.table==t and decoded.offsets==offsets
        checks['lattice_plans']+=1
print('PASS',dict(checks),flush=True)
