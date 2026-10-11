# Repair-and-accept proofs and defect-trace foundation

This additive research scope proves the repair terminal for **positive ordinary
margins, all strictly below `U`**, with nonempty row and column sets. It contains
the actual inverse-fiber bijection, a terminal consuming exactly `k` fair bits,
and its bounded-retry accuracy theorem. The [Python reference](../../src/contingency115/repair_accept.py)
uses that rule with the existing physical walker.

For `p=mn`, support size `s(A)`, and total `M`, put
`ell(A)=1+(p-1)s(A)`, `c=1+(p-1)max(m,n)`, and
`L*=1+(p-1)min(p,M)`. The actual repair fiber has size `ell(A)`.
At exact stationarity, accepting the repaired table with probability `c/ell(A)`
gives uniform accepted output and success at least `1/min(m,n)`.

The executed terminal accepts a uniform integer `j<2^k` exactly when
`j<floor(2^k c/ell(A))`. With independent endpoints within TV `delta` of uniform
physical stationarity and a fixed feasible fallback after `R` attempts, the
compiled bound is

```
TV(output, uniform tables) <= (1-c/L*)^R + R*(delta + 2^(-k)).
```

The approximation premise is explicit. These proofs do not supply a new mixing
schedule, connect the terminal to the encoded public machine, or price its
complete runtime. The [derivation and API guide](../../docs/repair-output.md)
explain those boundaries.

## Statements and hypotheses

Lean names below omit the initial `Math115.`. The exact elaborated statements
and dependency closures are retained in the [environment report](results/audit.stdout.json.gz).

| English claim | Lean statement | Hypotheses and scope |
|---|---|---|
| Actual repair fiber has size `1+(mn-1)s(A)` | [`AllSmallRepairFiber.reduced_repairTable_fiber_card`](formal/Math115/AllSmallRepairFiber.lean) | Finite ordered row/column types; every margin below `U`; an actual feasible table `A`. No assumed fiber count. |
| Actual defect-only repair fiber has size `(mn-1)s(A)` | `AllSmallRepairFiber.physical_defect_repair_fiber_card` | Same physical scope; balanced state excluded. |
| One `k`-bit threshold is within TV `2^-k` of the ideal coin | [`RepairAcceptanceCoin.finiteBitLaw_variation_lt`](formal/RepairAcceptanceThreshold.lean) | Natural `k,c,ell`, `0<ell`, `c<=ell`; uniform independent Boolean word. |
| Stationary acceptance is at least `1/min(m,n)` | [`RepairAcceptancePhysical.physical_stationary_success_lower`](formal/RepairAcceptancePhysical.lean) | Positive all-small margins, nonempty dimensions, and a supplied feasible table. |
| The actual physical repair terminal obeys the displayed retry bound | `RepairAcceptancePhysical.physical_finiteBit_retry_variation` | Same scope; endpoint law within TV `delta` of uniform physical states; independent retries; fixed feasible fallback. |
| Eliminating independent repair stars preserves the full unnormalized Poincare constant | [`FiniteStarTrace.poincare_transfer`](formal/Math115/FiniteStarTrace.lean) | Arbitrary finite balanced/defect sets and repair map; explicit full graph-energy decomposition and full Poincare inequality. Physical graph instantiation is not assumed proved here. |

The last theorem is a foundation for the reviewed [defect-chain derivation](../../docs/defect-trace.md).
That changed chain has a mathematical inverse-gap allowance `2500d^16`
(`5000d^16` with a dyadic proposal) for positive all-small margins and `m,n>=2`.
For square tables, retaining the shape gives `5000d^(31/2)` and
`10000d^(31/2)`, respectively.
Its numerical physical bound is not compiled in this packet. The general
selected/reference `80000d^17` theorem is unchanged.

## Reproduce the scoped verification

Use the pinned Lean 4.34.1 compiler and the repository's existing dependency
workflow. In a clean checkout, bootstrap and build the ordinary baseline first:

```sh
bash scripts/bootstrap_lean.sh
bash scripts/verify_lean.sh focused --serial
python3 research/repair-accept/verify.py --output .local/repair-accept-recheck
```

If the baseline is already built, only the last command is needed. `--lean`
can select the pinned compiler at another local path. The scoped runner requires
a new output directory, performs no downloads, and writes all new objects there;
it does not modify baseline objects or the default target. It also compiles two
small pinned upstream imports that the old target did not require.

The runner enumerates **all declarations defined in these six modules** from the
compiled environment, including private/generated declarations. It checks their
transitive axioms and retains complete dependency closures for the actual fiber
identity, the physical retry theorem, and the generic Poincare transfer. The
three headline names select explanatory closures, not the theorem inventory.
Only `propext`, `Classical.choice`, and `Quot.sound` are admitted. Imported object
hashes, compiler identity, exact source hashes, outcomes, and durations are saved.
The imported-object inventory and full environment report use lossless gzip
compression to keep machine-generated evidence compact.
The [compressed compiler outputs](results/compiler-output.json.gz) retain the
empty stdout/stderr records from this clean run.

The [verification receipt](results/verification.json) describes fresh ordinary
compilation of this research scope with trusted compiler and reused baseline
imports. It is not a fresh build of every dependency, a hosted Linux replay, or
Comparator acceptance. These sources are separate from the default sampler
target and do not enlarge its historical audit counts.

To exercise the implementation and finite trace identities:

```sh
make test
python3 experiments/defect_trace.py
```

`--spectral` adds optional NumPy diagnostics to the latter. Mathematical review
and implementation review were performed by separate AI agents; no outside
human review is claimed.

The [reference validation receipt](../../reports/repair-accept-validation.json)
records the full `make verify` result, the exact trace rerun, the executed API
example, and the checked implementation sources.
