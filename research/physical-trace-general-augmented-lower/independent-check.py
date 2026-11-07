"""Independent bounded enumeration of p-1 and the donor-label injection."""
import itertools, json
from pathlib import Path

root = Path(__file__).resolve().parent
cases = 0
strict_improvement = 0
max_gain = 0
improvement_witness = None
tight_witness = None
shapes = {}
for m in range(1, 4):
    for n in range(1, 4):
        cap = 3 if (m, n) == (2, 2) else 1
        shape_cases = 0
        for flat in itertools.product(range(cap + 1), repeat=m*n):
            X = [flat[i*n:(i+1)*n] for i in range(m)]
            r = list(map(sum, X))
            c = [sum(X[i][j] for i in range(m)) for j in range(n)]
            if min(r) == 0 or min(c) == 0:
                continue
            for U in range(max(r+c)+2):
                sr = [i for i in range(m) if r[i] < U]
                sc = [j for j in range(n) if c[j] < U]
                lr = [i for i in range(m) if i not in sr]
                cells = [(i,j) for i in range(m) for j in range(n)
                         if i in sr or j in sc]
                def valid(st):
                    s,t = st
                    if s == t:
                        return False
                    i,j = t[0],s[1]
                    if i in sr or j in sc:
                        return X[i][j] > 0
                    return (sum(X[i][k] for k in range(n) if i in sr or k in sc) < r[i]
                            and sum(X[k][j] for k in range(m) if k in sr or j in sc) < c[j])
                count = sum(valid(st) for st in itertools.product(cells, repeat=2))
                p = len(cells)
                c0 = max(len(sr)*max(n*len(sr)-1,0), len(sc)*max(m*len(sc)-1,0))
                assert count >= max(p-1,0), (X,U,count,p)
                if sr:
                    donor_col = {i: next(j for j in range(n) if X[i][j] > 0) for i in sr}
                    donor_row = {j: next(i for i in range(m) if X[i][j] > 0) for j in sc}
                    i0 = sr[0]
                    A = [((i,donor_col[i]),(i,j)) for i in sr for j in range(n) if j != donor_col[i]]
                    B = [((i0,donor_col[i]),(i,donor_col[i])) for i in sr if i != i0]
                    C = [(((i,j) if i != donor_row[j] else (i0,j)), (donor_row[j],j))
                         for i in lr for j in sc]
                    labels = A+B+C
                    assert all(s in cells and t in cells and valid((s,t)) for s,t in labels)
                    assert len(labels) == len(set(labels)) == p-1
                else:
                    assert p == m*len(sc)
                    assert c0 >= max(p-1,0)
                cases += 1
                shape_cases += 1
                if p-1 > c0:
                    strict_improvement += 1
                    if p-1-c0 > max_gain:
                        max_gain = p-1-c0
                        improvement_witness = dict(X=X,r=r,c=c,U=U,p=p,c0=c0,count=count)
                if p > 1 and count == p-1 and tight_witness is None:
                    tight_witness = dict(X=X,r=r,c=c,U=U,p=p,c0=c0,count=count)
        shapes[f'{m}x{n}'] = shape_cases
result = dict(status='passed',method='Independent ordinary SupportTest enumeration and explicit A/B/C label construction',
              scope='All positive-margin binary tables of dimensions 1..3 by 1..3; all 2x2 tables with entries 0..3. U ranges from 0 through max margin + 1.',
              cases=cases,cases_by_shape=shapes,strict_improvement_cases=strict_improvement,
              largest_p_minus_one_improvement_over_c0=max_gain,improvement_witness=improvement_witness,
              tight_witness=tight_witness,zero_by_zero_case='p=count=c0=0; truncated p-1=0',
              limitation='Finite diagnostic evidence; mathematical argument and compiled Lean theorem carry universal claim.')
(root/'independent-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
