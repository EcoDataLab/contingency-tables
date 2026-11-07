from collections import defaultdict
from fractions import Fraction as F
from itertools import product, combinations
from math import factorial, prod
from random import Random
from contingency115.tables import TableProblem
from contingency115.optimize import linear_bounds, verify_optimality, InfeasibleTableError, InfeasibleFlowError, verify_infeasibility
from contingency115.transport_bounds import integer_leaf_edge_owner, path_cut_coefficients, path_variance

def enum(p):
 m,n=p.shape
 for flat in product(*(range(p.lower_bounds[i][j],p.upper_bounds[i][j]+1) for i in range(m) for j in range(n))):
  t=tuple(tuple(flat[i*n:(i+1)*n]) for i in range(m))
  if tuple(map(sum,t))==p.row_sums and tuple(map(sum,zip(*t)))==p.column_sums:yield t

r=Random(115019)
for k in range(300):
 m,n=r.choice(((2,2),(2,3),(3,2)))
 fixture=tuple(tuple(r.randrange(3) for _ in range(n)) for _ in range(m))
 rows=tuple(map(sum,fixture));cols=tuple(map(sum,zip(*fixture)))
 caps=tuple(tuple(fixture[i][j]+r.randrange(2) for j in range(n)) for i in range(m))
 low=tuple(tuple(r.randrange(fixture[i][j]+1) for j in range(n)) for i in range(m))
 p=TableProblem(rows,cols,caps,low);tables=tuple(enum(p));assert tables
 costs=tuple(tuple(F(r.randrange(-7,8),r.randrange(1,6)) for j in range(n)) for i in range(m))
 vals=[sum(costs[i][j]*t[i][j] for i in range(m) for j in range(n)) for t in tables]
 bounds=linear_bounds(p,costs)
 assert (bounds.minimum.value,bounds.maximum.value)==(min(vals),max(vals))
print('300 feasible rectangular optimizer fibers: raw Cartesian extrema agree')

# Reject every edge absent from the explicitly generated leaf cliques, not merely check positives.
checked=0
for widths in ((0,), (1,2), (2,2), (1,2,1)):
 p=len(widths)
 for order in (tuple(range(p)),tuple(reversed(range(p)))):
  owners={}
  for depth,special in enumerate(order):
   for ell in range(1,widths[special]+1):
    other=tuple(j for j in range(p) if j!=special)
    for choices in product(*(range(widths[j]+1) for j in other)):
     a=dict(zip(other,choices));display=tuple(v for j,w in enumerate(widths) for v in ((ell,w+1-ell) if j==special else (a[j],w-a[j])))
     leaves=[]
     for j in order[depth:]:
      for idx in (2*j,2*j+1):
       t=list(display);t[idx]-=1
       if all(0<=x<=widths[k//2] for k,x in enumerate(t)):leaves.append(tuple(t))
     for x,y in combinations(leaves,2):owners[tuple(sorted((x,y)))]=(special,ell,tuple((j,a[j]) for j in order[:depth]))
  points=list(product(*(range(w+1) for w in widths for _ in range(2))))
  for x,y in combinations(points,2):
   assert integer_leaf_edge_owner(x,y,widths,order)==owners.get(tuple(sorted((x,y))))
   checked+=1
print('Integer ownership positive and negative pairs:',checked)

for length in range(1,7):
 for _ in range(20):
  masses=tuple(F(r.randrange(5),r.randrange(1,5)) for _ in range(length))
  if not any(masses):continue
  h=tuple(F(r.randrange(-7,8),r.randrange(1,6)) for _ in masses)
  total=sum(masses)
  cuts=tuple(sum(masses[a]*masses[b]*(b-a) for a in range(j+1) for b in range(j+1,length))/total for j in range(length-1))
  variance=sum(masses[a]*masses[b]*(h[a]-h[b])**2 for a in range(length) for b in range(a+1,length))/total
  assert path_cut_coefficients(masses)==cuts
  assert path_variance(masses,h)==variance
print('Transport cuts and variance: 120 direct pairwise identities')

from contingency115.cactus import CactusWeightedSampler
from contingency115.tables import ProductWeights, ZeroMassError
cases=0
for lower in (None,((1,0),(0,1))):
 p=TableProblem([2,2],[2,2],lower_bounds=lower);tables=tuple(enum(p))
 for flat in product((F(0),F(1,2),F(2)),repeat=4):
  a=(flat[:2],flat[2:])
  for use_factorial in (False,True):
   s=CactusWeightedSampler(p,ProductWeights(a,use_factorial))
   raw={t:prod(a[i][j]**t[i][j]/(factorial(t[i][j]) if use_factorial else 1) for i in range(2) for j in range(2)) for t in tables};z=sum(raw.values())
   assert s.normalizer()==z
   assert s.support_count()==sum(v>0 for v in raw.values())
   if z:
    assert all(s.probability(t)==v/z for t,v in raw.items())
   else:
    try:s.sample()
    except ZeroMassError:pass
    else:raise AssertionError('zero-mass sampler returned a table')
   cases+=1
print('Cactus exact product-law normalizers/support/probabilities:',cases,'zero/rational activity and lower-bound cases')
