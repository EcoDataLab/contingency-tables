# Independent implementation review

Review provenance: “independent” here means a separate AI agent reviewing AI-produced research or code within this project. This is not outside human peer review. Compiler and execution receipts have the narrower scopes stated below.

Reviewed 8 October 2026. The audit report records SHA-256 hashes of the reviewed
implementation files and its own script, so the result can be tied to exact
source contents. This review covers `tables.py`, `kernels.py`, and `optimize.py`.

No actionable correctness defect was found in the reviewed implementation.
That conclusion combines manual inspection with the bounded, exact checks
below; it is not a proof of the entire implementation or a claim about large
instances.

## Finite independent checks

Run from the repository root:

```sh
PYTHONPATH=src python3 experiments/independent_crosscheck.py
```

The fixed seed is `11520261008`. The script writes
`reports/independent-crosscheck.json` and does not need NumPy or network access.
It is an additional research audit, separate from the unit test suite.

* For 160 bounded `2x3` and `3x3` constraint cases, a direct Cartesian product
  of cell values is filtered by margins. That independent fiber agrees with
  the DP count and lexicographic table enumeration. Cases include lower bounds,
  structural zeros and deliberately perturbed margins; 20 fibers are empty.
* Exact linear objective extrema from those explicit fibers agree with all
  280 min-cost-flow endpoints. Their certificates verify, and modifying each
  claimed objective bound causes rejection. Every emitted cut certificate is
  checked directly against its original constraints.
* Product-law normalizers are compared to an independent integer/Fraction
  calculation of the weight of each enumerated table, including factorial
  weights and zero activities. There are 73 zero-mass targets. For 67
  positive-mass targets, exact heat-bath stationary probabilities agree with
  those explicit weights and the positive-support states form one communicating
  class under the complete simple-cycle catalog. Null states are excluded from
  this connectivity claim.
* A permutation-based cycle oracle, which does not use the catalog's graph
  traversal or `Cycle.from_nodes`, agrees on all 512 binary `3x3` support
  patterns. It also agrees with all 204 simple cycles of complete `4x4`
  support. These are checks of catalog completeness in finite cases.

The two independent enumerations are intentionally exponential and small.
Some random fibers are singletons; the case counts do not indicate an equal
number of difficult sampling problems. The audit uses exact arithmetic and
does not infer exactness from sample frequencies.

## Manual source review

The review checked the following invariants against the code:

* Lower-bound subtraction preserves the flow feasibility problem, and
  structural-zero/lower-bound conflicts remain infeasible after transposition.
* Uniform unranking uses integer completion counts; weighted row selection
  uses its row weight times the exact child completion mass.
* DP state/transition exhaustion is sticky and cannot expose a partial count
  or consume randomness before completion. The documented budgets do not
  claim to bound arbitrary-precision arithmetic, feasibility work or wall time.
* Kernel inputs are distinct feasible states and match an independently
  computed exact fiber cardinality. Together these facts certify that the
  supplied state list is complete.
* Cycle probabilities are fixed independently of the current state. A
  zero-mass line holds; a positive-mass line uses its exact conditional law.
  Positive target states cannot transition to zero-weight states.
* The min-cost-flow solver starts from a residual network without negative
  cycles and augments along a simple shortest path of tight arcs. The final
  all-node potentials have the correct reduced-cost signs. The verifier checks
  an integer feasible witness and equality of its original objective with the
  dual bound, independently of optimizer state.
* Sampling exactness assumes the documented RNG contract: `randrange(stop)`
  returns a uniform integer in `range(stop)`. The default is `SystemRandom`;
  arbitrary user-supplied RNG implementations are not certified by this audit.

The stronger transport theorems have a separate mathematical review. These
implementation checks do not certify an implementation of OpenAI's full
polynomial-time sampler or FPRAS; the reference DP and explicit kernels are
small-instance tools.
