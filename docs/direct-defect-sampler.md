# Direct bounded defect sampler

[`DyadicDefectChain`](../src/contingency115/defect_chain.py) implements the
[unit defect chain](defect-trace.md) without enumerating tables or physical
states. It supports positive ordinary equal-total margins, at least two rows
and columns, and **either every row margin below `U` or every column margin
below `U`**. The other side may reach or exceed `U`. Extra cell restrictions
and the general nonempty completion block are outside this implementation.

Each transition scans at most the table's cells, takes a fixed dyadic channel
draw, and either makes a local defect move, holds, or refreshes the repair
fiber. A refresh uses two fixed-length words to choose a supported receiver
and crossing labels. There are no random-retry loops, completion calls or
table-count calls. The tests use enumeration only as an independent oracle
on small fibers.

## Probability and work accounting

Write `p=mn`, `b=max(m,n)`, `smax=min(p,M)`, and
`e=ceil(log2(2*(2*(m+n-2)+1)))`. The ideal channel probability is
`beta=2^-e`. To approximate a uniform integer in `range(a)`, a fresh `k`-bit
word `w` gives `floor(a*w/2^k)`. If `r=2^k mod a`, its exact total variation
distance is

```
delta(a,k) = r*(a-r)/(a*2^k) <= a/(4*2^k).
```

This includes zero bits and `a>2^k`. A refresh at a table of support `s`
has row error at most `beta*min(1,delta(s,k)+delta(p-1,k))`. The uniform bound
reported by the implementation is

```
eta = beta * min(1, (smax+p-1)/(4*2^k)).
```

After `T` steps from the same initial defect, distance from the **ideal walk**
is at most `min(1,T*eta)`. This is not distance from stationarity. Indeed,
the executed finite-word kernel need not have uniform stationarity; the
exact tests exhibit that drift.

The sampler constructs an initial defect directly from a supplied feasible
table. Each attempt resets that state, advances the same random stream for
`T` steps, repairs its endpoint, and accepts a fresh `kt`-bit word below
`floor(2^kt*b/support)`. The stationary ideal terminal is uniform on tables
because the defect fiber has size `(p-1)*support`. Its success probability
is at least `b/smax`.

After `R` attempts, exhaustion returns the original feasible table as a flagged
fallback. With an ideal endpoint-mixing certificate `delta`, the complete
output error allowance is

```
TV <= (1-b/smax)^R + R*delta + R*T*eta + R*2^-kt.
```

The result exposes all four components. `delta` must bound the ideal dyadic
chain's endpoint from the constructed initial defect. It is a caller-supplied
mathematical premise; passing a small number does not verify it. The allowance
applies to the fallback law. It does not describe conditioning finite-bit
output on acceptance. `use_fallback=False` exposes exhaustion as `None`.

Preflight limits bound cells, input bits, attempts, total steps and total fair
bits before sampling. The complete bit reservation is
`R*(T*(e+2*k)+kt)`. Results report actual steps, refreshes, attempts and bits;
early acceptance reduces actual consumption. Each step takes `O(p)` integer
operations and `O(p)` storage. Integer bit costs and a compiled-machine runtime
are separate quantities.

The [complete both-small schedule](defect-sampler-composition.md) gives
explicit sufficient `R,T,k,kt,delta` for any rational target error. Its
allowances are extremely large and are intended for proof and cost accounting.

## Example and evidence

This example exercises a 20 by 5 table without constructing its state space:

```python
from random import Random
from contingency115.tables import TableProblem
from contingency115.defect_chain import DyadicDefectChain

problem = TableProblem([50] * 20, [200] * 5)
start = problem.feasibility().table
d = 10 + (20 + 1) * (5 + 1)
chain = DyadicDefectChain(problem, U=5*d**3, refresh_bits=24)
result = chain.sample(
    start, attempts=8, steps_per_attempt=1000, terminal_bits=24,
    endpoint_mixing_delta=1, rng=Random(115),
)
assert problem.validate_table(result.table) == result.table
print(result.attempts, result.physical_steps, result.fair_bits)
```

The example uses the safe, vacuous mixing allowance `delta=1`; its TV allowance
is therefore one. Its 1,000-step choice demonstrates execution and feasibility,
without an accuracy claim. A seeded pseudorandom source makes the example
reproducible; the mathematical laws assume words uniform conditional on all
earlier calls.

[Exact tests](../tests/test_defect_chain.py) check every finite-word transition
row on six small square/rectangular cases and three precisions against the
independently built physical graph. They verify the ideal kernel, inverse
fibers, exact rank error, observed finite-kernel drift, terminal correction,
fallback composition, RNG stream order and budget failures. One-side-small
fixtures include entries exactly equal to `U`. A separate AI-agent review found
no blocking issue and checked additional asymmetric examples.

```sh
PYTHONPATH=src python3 -m unittest discover -s tests -p test_defect_chain.py -v
```

The [rectangular derivation](rectangular-defect.md) improves the ideal gap
when both sides are below the cutoff. Formal identification of this Python
program, its finite-word kernels and the changed physical chain remains open.
