from collections import Counter
from fractions import Fraction as F
from itertools import product, permutations
from math import factorial, prod
from random import Random
from contingency115.tables import TableProblem, ProductWeights
from contingency115.workers import OrdinaryWorkerSampler, worker_linear_moments
from contingency115.cactus import CactusTableSampler, CactusWeightedSampler, NotCactusError
from contingency115.optimize import linear_bounds, InfeasibleTableError, verify_optimality
from contingency115.transport_bounds import integer_leaf_edge_owner

# Oracle sees cell bounds and margins only; no sampler/count/feasibility helper.
def cells(p):
 m,n=p.shape
 for flat in product(*(range(p.lower_bounds[i][j],p.upper_bounds[i][j]+1) for i in range(m) for j in range(n))):
  t=tuple(tuple(flat[i*n:(i+1)*n]) for i in range(m))
  if tuple(map(sum,t))==p.row_sums and tuple(sum(t[i][j] for i in range(m)) for j in range(n))==p.column_sums: yield t

class NeedRandom(Exception): pass
class Tape:
 def __init__(self,seq): self.seq=iter(seq)
 def randrange(self,stop):
  try:return next(self.seq)
  except StopIteration:raise NeedRandom(stop)

def branches(sampler):
 out=Counter(); todo=[((),F(1))]
 while todo:
  tape,mass=todo.pop()
  try:out[sampler.sample(Tape(tape))] += mass
  except NeedRandom as e:
   stop=e.args[0]
   assert stop<=100
   todo.extend((tape+(r,),mass/stop) for r in range(stop))
 return out

r=Random(20261106)
checked=0
for rows,cols in [((2,2),(2,2)),((0,2,1),(1,0,2)),((1,1,1),(1,2)),((0,0),(0,0)),((5,),(2,3)),((2,3),(5,))]:
 p=TableProblem(rows,cols); ts=list(cells(p)); weights={t:F(1,prod(factorial(x) for row in t for x in row)) for t in ts}; z=sum(weights.values()); law={t:w/z for t,w in weights.items()}
 assert branches(OrdinaryWorkerSampler(rows,cols))==law
 c=tuple(tuple(F(r.randrange(-5,6),r.randrange(1,5)) for _ in cols) for _ in rows)
 obs={t:sum(c[i][j]*t[i][j] for i in range(len(rows)) for j in range(len(cols))) for t in ts}; mean=sum(law[t]*obs[t] for t in ts); var=sum(law[t]*(obs[t]-mean)**2 for t in ts)
 got=worker_linear_moments(rows,cols,c); assert (got.mean,got.variance)==(mean,var)
 checked+=1
print('Exact urn branch laws and full-covariance moments:',checked)
checked=0
for _ in range(120):
 m,n=r.choice(((2,2),(2,3),(3,2))); fixture=tuple(tuple(r.randrange(3) for _ in range(n)) for _ in range(m)); rows=tuple(map(sum,fixture)); cols=tuple(map(sum,zip(*fixture))); caps=tuple(tuple(r.randrange(3) for _ in range(n)) for _ in range(m)); low=tuple(tuple(r.randrange(caps[i][j]+1) for j in range(n)) for i in range(m)); p=TableProblem(rows,cols,caps,low); ts=list(cells(p)); c=tuple(tuple(F(r.randrange(-9,10),r.randrange(1,8)) for _ in range(n)) for _ in range(m))
 try:bounds=linear_bounds(p,c)
 except InfeasibleTableError:assert not ts;continue
 vals=[sum(c[i][j]*t[i][j] for i in range(m) for j in range(n)) for t in ts]; assert (bounds.minimum.value,bounds.maximum.value)==(min(vals),max(vals))
 assert all(verify_optimality(p,c,b.table,b.certificate) for b in (bounds.minimum,bounds.maximum)); checked+=1
print('Optimizer independent cell enumeration:',120,'cases;',checked,'feasible')
for factorial_weight in (False,True):
 p=TableProblem([4,2,2],[2]*4,[[2]*4,[2,2,0,0],[0,0,2,2]])
 a=tuple(tuple(map(F,row)) for row in ((F(1,2),2,3,1),(1,2,1,1),(1,1,2,3))); ws=ProductWeights(a,factorial_weight); s=CactusWeightedSampler(p,ws); ts=list(cells(p)); weights={t:prod(a[i][j]**t[i][j]/(factorial(t[i][j]) if factorial_weight else 1) for i in range(3) for j in range(4)) for t in ts}; z=sum(weights.values()); assert s.normalizer()==z; assert all(s.probability(t)==w/z for t,w in weights.items()); assert CactusTableSampler(p).count()==len(ts)
print('Cactus 2-cycle normalizers and all 9 probabilities: both product laws pass')
p=TableProblem([2,2],[2,2]); s=CactusWeightedSampler(p,ProductWeights([[1,1],[1,1]],True)); assert branches(s)=={((0,2),(2,0)):F(1,6),((1,1),(1,1)):F(2,3),((2,0),(0,2)):F(1,6)}
print('Cactus factorial full choice-tree law: pass')
for bad in (-1, True, F(1,2), 0.5):

 try:s.sample(Tape([bad]))
 except (TypeError,ValueError) as error:print('Invalid weighted RNG',repr(bad),'rejected with',type(error).__name__)
 else:raise AssertionError('invalid source silently accepted')
print('Noninteger ownership',integer_leaf_edge_owner((F(1,2),F(3,2)),(F(3,2),F(1,2)),(2,)))
