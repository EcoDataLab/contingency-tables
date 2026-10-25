# Repairing auxiliary states before rejection

For ordinary tables whose positive row and column margins are all below the
cutoff, the existing auxiliary chain can use many outputs it currently discards.
Repair the state into a table, then correct for the size of that table's repair
fiber. This keeps the original chain and its inverse-gap bound, while reducing
a sufficient inverse-success allowance from quadratic in the number of cells to
at most the smaller table dimension.

**Evidence:** [compiled Lean proofs](../research/repair-accept/) of the actual
physical repair fibers, stationary success, and fixed-bit bounded-retry law;
an executable Python reference with exact finite tests; independent AI-agent
mathematical and code review. This output rule is not installed in the compiled sampler.
It neither lowers the verified `40,000d^17` unit-chain inverse-gap allowance nor
supplies a new complete machine-time exponent. The construction uses elementary
rejection sampling; no claim of a new general sampling technique is made.

## Statement and output rule

Let the shape be `m × n`, with `m,n ≥ 1`, positive integer row and column margins,
equal total `M`, and **every margin strictly below `U`**. There are no extra cell
bounds, structural zeros, or weights. Put `p=mn`. Let `N` count ordinary tables.
For the unit-weight all-small physical chain, let `R(x)` be its designated repair
and define

\[
 \ell(A)=1+(p-1)|\operatorname{supp}(A)|,\qquad
 c=1+(p-1)\max(m,n),\qquad
 L_* =1+(p-1)\min(p,M),\qquad \rho_0=L_*/c.
\]

Then `c ≤ ℓ(A) ≤ L_*` and `ρ₀ ≤ min(m,n)`. The terminal rule is:

1. Repair the physical state to `A=R(x)` and count its positive cells.
2. Draw an integer uniformly from `0,…,ℓ(A)−1` using fresh randomness.
3. Accept `A` exactly when that integer is less than `c`.

No table count, partition function, or search for the smallest repair fiber is
needed. Repair and support counting take `O(p)` elementary operations at an
endpoint. Singleton row/column fibers can instead be returned directly.

At exact stationarity the accepted table is uniform. If
`Z=Σ_A ℓ(A)` is the number of physical states, the success probability is

\[
 s={Nc\over Z}\ge {c\over L_*}=1/\rho_0\ge1/\min(m,n).
\]

The source's balanced-only terminal rule has success `N/Z`. Thus this correction
improves its stationary success by **exactly `c`**, on the stated branch.

## Why the fiber count and correction are exact

Write a defect as two views with `q−x=e_s−e_t`, where `s≠t` are cell labels.
Set `v=(row(t),column(s))`. The designated repair and its inverse are

\[
 A=x-e_t+e_v,\qquad x=A+e_t-e_v,\qquad q=A+e_s-e_v.
\]

For a fixed cell `v`, there are `mn−1` ordered pairs `(s,t)` with this crossing
and `s≠t`. Both inverse views are nonnegative exactly when `A_v>0`. This includes
the cases `v=s` or `v=t`: cancellation occurs in one view, but the other still
requires that positive entry. Row and column sums below `U` guarantee the
capacity bounds. The defect equation determines the ordered labels uniquely,
so inverse images are not counted twice. Adding the balanced state gives `ℓ(A)`.

Positive margins force at least one positive entry in each row and column;
integer entries give at most `min(p,M)` positive entries. These prove the fiber
bounds. Writing `p=ab`, `a=min(m,n)`, `b=max(m,n)`, gives
`[1+(p−1)p]/[1+(p−1)b] ≤ a`, hence the dimension bound.

The original stationary mass of a repair fiber is `ℓ(A)/Z`. Multiplication by
its acceptance probability `c/ℓ(A)` gives the same unconditional successful
mass `c/Z` for every table. If the true minimum fiber size is known, it can
replace `c`. That choice is optimal among rejection rules using this designated
repair: no table can receive more successful mass than its entire repair fiber.

## Finite walks and bounded attempts

Suppose the existing lazy unit chain has Poincaré constant at most `K`. Its
worst-start endpoint distance after `T` physical transitions is at most
`(1/2)√Z exp(−T/K)`. Run `R` independently restarted attempts, apply the terminal
rule, return the first accepted table, and use a fixed feasible table if all fail.
Coupling each endpoint to an independent stationary endpoint gives

\[
 \operatorname{TV}(\mathrm{output},\mathrm{Uniform})
 \le e^{-R/\rho_0}+{R\over2}\sqrt{NL_*}\,e^{-T/K}.
\]

For `0<ε<1`, the computable count bound `N≤B=(M+1)^p` permits

\[
 R=\lceil\rho_0\log(2/\varepsilon)\rceil,\qquad
 T=\left\lceil K\log\!\left({R\sqrt{BL_*}\over\varepsilon}\right)\right\rceil.
\]

The total error is at most `ε`. This is a bounded number of physical transitions;
it is not exact uniformity after a finite walk. At `U=5d³`, `L=3d` and
`d=10+(m+1)(n+1)`, the existing [unit-chain proof](physical-repair-refinement.md)
supplies `K=40,000d^17` when the stated all-small conditions hold.

The total transition allowance has leading factors `Kρ₀`, rather than
`KL_*`, with the displayed logarithms retained. It does not include a complete
bit-cost implementation.

### Fixed-bit terminal and compiled error bound

The implemented terminal replaces the ideal integer draw with **one `k`-bit
word** `j`, accepting when

\[
 j<\left\lfloor{2^k c\over\ell(A)}\right\rfloor.
\]

This uses no random-retry loop. Its acceptance probability rounds downward from
`c/ℓ(A)` by less than `2^-k`. If each independently restarted endpoint has total
variation at most `δ` from uniform physical stationarity, the first accepted
table with a fixed feasible fallback after `R` attempts obeys

\[
 \operatorname{TV}(\mathrm{output},\mathrm{Uniform})
 \le (1-c/L_*)^R+R(\delta+2^{-k}).
\]

This is the compiled theorem
`Math115.RepairAcceptancePhysical.physical_finiteBit_retry_variation`.
Its repair map is the actual reduced physical map, and its terminal denominator
is the support formula above. The proof derives the fiber bounds from positive
all-small margins. It assumes endpoint accuracy; it does not identify the
modified output with the existing encoded machine. Rounding can bias the law
conditioned on acceptance: the displayed bound is for the complete output with
fallback.

For `0<ε<1`, one sufficient allocation is
`R=ceil(ρ₀ log(3/ε))`, endpoint error `δ≤ε/(3R)`, and
`k≥ceil(log₂(3R/ε))`. The three terms then sum to at most `ε`. The walk bound
above can supply the endpoint premise for the stated chain.

### Reference implementation

[`RepairAcceptRule`](../src/contingency115/repair_accept.py) wraps the existing
enumerated physical walker. It resets the state at each attempt while advancing
one random stream, checks work caps before drawing, and reports actual attempts,
physical steps, bits, and exhaustion. Its `error_bound` method requires a supplied
endpoint error; it does not infer one from a short run.

```python
from contingency115.ideal_chain import build_rescaled_ideal_chain
from contingency115.repair_accept import RepairAcceptRule
from contingency115.tables import TableProblem

chain = build_rescaled_ideal_chain(TableProblem((2, 2), (2, 2)), U=3, L=1)
rule = RepairAcceptRule(chain)
fallback = rule.repair(0)
result = rule.run(attempts=8, steps_per_attempt=100, acceptance_bits=16,
                  fallback=fallback, seed=115)
print(result)
```

These small diagnostic settings demonstrate the API; they are not a claimed
mixing schedule. A seed supplies reproducibility, while the probability theorem
assumes independent fair words. Omitting `fallback` exposes exhaustion as
`table=None`. Scope checks reject zero margins, extra cell bounds, and large
blocks. The enumerated backend remains a small-instance reference.

## A useful alternative that did not beat the simple correction

Our initial candidate changed the chain's stationary law to
`π′(x)=1/[Nℓ(R(x))]`. Its repair is uniform with no final rejection. Starting from
the symmetric original kernel `P`, Metropolis acceptance
`min(1,ℓ(R(x))/ℓ(R(y)))` realizes that law. Comparing measures and edge
conductances transfers the inverse-gap allowance to
`K·ℓ_max/ℓ_min ≤ Kρ₀`.

Independent review identified the missing comparison: scaled rejection achieves
the same leading dimension allowance while keeping the original chain. Accepting
with just `1/ℓ(A)` would have missed that gain. We therefore prefer the simpler
terminal correction and have now formalized its finite-bit law. The reweighted chain is
retained as an experiment, without a claimed general advantage. Its numerical
gap is smaller on the tested nonconstant-fiber cases.

## Finite evidence and a local-move obstruction

[The experiment](../experiments/repair_reweighting.py) independently enumerates
row views and defect labels, reconstructs inverse fibers, and checks exact
stationary masses, stochasticity, detailed balance, and the energy comparison.
[The saved report](../reports/repair-reweighting.json) covers eleven cases.
Floating eigenvalue diagnostics, when requested, are labeled separately.
The diagnostic uses `U=max(margins)+1,L=1`; these small fixtures have the same
unit graph and proposal as at the ideal scales. That graph identity, rather
than arbitrary rescaling, is what permits comparison with the ideal-chain result.

| Margins | Tables | Physical states | Balanced-only success | Scaled repair success |
|---|---:|---:|---:|---:|
| `(1,1)` / `(1,1)` | 2 | 14 | `1/7` | `1` |
| `(2,2)` / `(2,2)` | 3 | 27 | `1/9` | `7/9` |
| `(2,2)` / `(2,1,1)` | 4 | 74 | `2/37` | `32/37` |
| `(1,1,1)` / `(1,1,1)` | 6 | 150 | `1/25` | `1` |

There is also a broader version of the [2×2 obstruction](ideal-two-by-two.md).
On its known physical graph with equal margins `t`, each edge changes the first
entry of the repaired table by at most one. For **any reversible chain on those
edges whose stationary repair is uniform**, this coordinate has variance
`t(t+2)/12` and energy at most `1/2`. Its inverse gap is therefore at least
`t(t+2)/6`, or `t(t+2)/3` for a half-lazy chain. This is a mathematical derivation
using the block decomposition, with finite edge checks. It is not a universal
sampling lower bound: direct sampling and nonlocal heat baths solve the 2×2
case easily. The original uncorrected repair law is not uniform for `t≥2`.

Reproduce the exact checks without NumPy:

```sh
PYTHONPATH=src python3 experiments/repair_reweighting.py --output .local/reports/repair-reweighting.json
```

Add `--spectral` for the optional NumPy diagnostics included in the saved report.
Tests also reject a reversed Metropolis ratio and inputs outside the positive
all-small scope. Zero margins require a different support lower bound or an
explicit preprocessing construction. General large-block completion fibers,
weighted laws, and bounded-cell problems are outside this result.

The remaining work for the unchanged chain is to connect the changed output
program to the existing encoded unit walker and price its full work. A separate
[defect-only chain](defect-trace.md) uses the same inverse-fiber construction to
derive a smaller `d^16` inverse-gap allowance in this restricted regime; its
physical Lean instantiation is still open. The selected/reference branch and the seven
[numerical draw certificates](composed-complexity.md) remain separate work.
