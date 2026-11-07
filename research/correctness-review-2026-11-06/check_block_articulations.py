"""Independent sparse cell-box oracle and complete conditional RNG-tree audit."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from math import factorial
import random
from contingency115.tables import TableProblem, ProductWeights, ExactTableSampler, ExactWeightedTableSampler, ZeroMassError
from contingency115.block_sampler import BlockTableSampler, BlockWeightedSampler
rng=random.Random(420932)
checks=Counter()

def margin(t):
 return tuple(map(sum,t)),tuple(map(sum,zip(*t)))
def brute(lower,upper,rows,cols):
 m,n=len(rows),len(cols)
 variables=[(i,j) for i in range(m) for j in range(n) if lower[i][j]<upper[i][j]]
 result=[]
 for digits in product(*(range(lower[i][j],upper[i][j]+1) for i,j in variables)):
  t=[list(r) for r in lower]
  for (i,j),v in zip(variables,digits): t[i][j]=v
  if margin(t)==(rows,cols): result.append(tuple(map(tuple,t)))
 return result

def mass(t,act,fact):
 z=F(1)
 for i,row in enumerate(t):
  for j,v in enumerate(row): z*=act[i][j]**v/(factorial(v) if fact else 1)
 return z

patterns=[
 (3,4,[(0,0),(0,1),(1,0),(1,1),(0,2),(0,3),(2,2),(2,3)]),
 (4,3,[(0,0),(0,1),(1,0),(1,1),(2,0),(2,2),(3,0),(3,2)]),
 (3,6,[(i,j) for i in (0,1) for j in (0,1,2)]+[(i,j) for i in (0,2) for j in (3,4,5)]),
 (4,6,[(i,j) for i in (0,1) for j in (0,1,2)]+[(i,j) for i in (2,3) for j in (3,4,5)]+[(1,3)]),
 (4,5,[(0,0),(0,1),(1,0),(1,1),(1,2),(2,2),(2,3),(3,2),(3,3),(3,4)]),
]
for m,n,edges in patterns:
 for trial in range(30):
  # Positive constants fill missing edges; dense table storage must not make
  # those constants appear again in local factors or couple articulations.
  lower=[[rng.randrange(3) for j in range(n)] for i in range(m)]
  upper=[r.copy() for r in lower]
  base=[r.copy() for r in lower]
  for i,j in edges:
   upper[i][j]+=1
   base[i][j]+=rng.randrange(2)
  rows,cols=margin(base)
  expected=brute(lower,upper,rows,cols)
  p=TableProblem(rows,cols,upper,lower)
  block=BlockTableSampler(p)
  assert block.count()==len(expected),(p,len(expected),block.count())
  tables=[block.unrank(i) for i in range(block.count())]
  assert set(tables)==set(expected)
  assert [block.rank(t) for t in tables]==list(range(len(tables)))
  for b in block.blocks:
   projected=[b.project(t) for t in expected]
   assert all(margin(local)==(b.problem.row_sums,b.problem.column_sums) for local in projected)
  act=tuple(tuple(rng.choice((F(0),F(1,2),F(1),F(2),F(3,2))) for j in range(n)) for i in range(m))
  if trial%3: act=tuple(tuple(v or F(1) for v in row) for row in act)
  for fact in (False,True):
   values={t:mass(t,act,fact) for t in expected}
   z=sum(values.values(),F(0))
   s=BlockWeightedSampler(p,ProductWeights(act,fact))
   assert s.normalizer()==z,(p,act,fact,z,s.normalizer())
   if z:
    assert {t:s.probability(t) for t in expected}=={t:v/z for t,v in values.items()}
   else:
    try:s.sample(rng)
    except ZeroMassError:pass
    else:raise AssertionError('zero mass draw')
   checks['weighted_articulation_cases']+=1
   checks['weighted_articulation_probabilities']+=len(expected) if z else 0
  checks['articulation_cases']+=1
  checks['articulation_rank_tables']+=len(tables)
 print('pattern complete',(m,n),dict(checks),flush=True)

class Need(Exception):
 def __init__(self,stop):self.stop=stop
class Replay:
 def __init__(self,values):self.values=iter(values)
 def randrange(self,stop):
  try:value=next(self.values)
  except StopIteration:raise Need(stop)
  assert 0<=value<stop
  return value

def full_law(s):
 pending=[((),F(1))]
 law=defaultdict(F)
 paths=0
 while pending:
  prefix,chance=pending.pop()
  paths+=1
  assert paths<100000
  try:t=s.sample(Replay(prefix))
  except Need as need:
   assert need.stop<=1000,need.stop
   pending.extend((prefix+(value,),chance/need.stop) for value in range(need.stop))
  else:law[t]+=chance
 checks['complete_rng_tree_nodes']+=paths
 return dict(law)

for lower_shift in (0,1):
 m,n,edges=patterns[0]
 lower=[[0]*n for _ in range(m)]
 upper=[[0]*n for _ in range(m)]
 base=[[0]*n for _ in range(m)]
 for i,j in edges:
  lower[i][j]=lower_shift
  upper[i][j]=lower_shift+1
  base[i][j]=lower_shift+(j%2==0 if i==0 else j%2==1)
 # Fixed positive chords must contribute exactly once and cancel in the law.
 lower[1][2]=upper[1][2]=base[1][2]=2
 lower[2][0]=upper[2][0]=base[2][0]=1
 rows,cols=margin(base)
 expected=brute(lower,upper,rows,cols)
 p=TableProblem(rows,cols,upper,lower)
 act=((F(2),F(1),F(1),F(2)),(F(1),F(1),F(2),F(1)),(F(1),F(1),F(1),F(1)))
 for fact in (False,True):
  masses={t:mass(t,act,fact) for t in expected}
  z=sum(masses.values(),F(0))
  target={t:v/z for t,v in masses.items() if v}
  for sampler_type in (ExactWeightedTableSampler,BlockWeightedSampler):
   actual=full_law(sampler_type(p,ProductWeights(act,fact)))
   assert actual==target,(sampler_type,lower_shift,fact,actual,target)
   checks['complete_rng_laws']+=1
print('PASS',dict(checks),flush=True)
