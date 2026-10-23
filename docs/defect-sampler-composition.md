# Bounded both-small defect sampler: complete error schedule and work allowance

This retained schedule restarts from a fixed state. The later
[spaced-attempt schedule](spaced-defect-sampling.md) pays for its cold burn once
and improves the operation allowance while preserving the same ideal chain.

11 October 2026. Mathematical composition for the direct reference implementation in `src/contingency115/defect_chain.py`. This uses the independently reviewed [variable-capacity gap derivation](rectangular-defect.md) on **positive ordinary both-small margins**, `m,n>=2`; it is not a compiled bit-machine cost theorem or a result for the nonempty completion branch.

The schedule below gives total variation error at most `epsilon`. At
`U=5d^3`, its walk and terminal take
`O(d^18 Lambda log d + d^17 Lambda^2)` integer arithmetic operations, where
`Lambda=1+log(1/epsilon)`. This counts the extra factors from worst-start
mixing, restarts, and per-step work; the inverse-gap exponent alone is not
the operation exponent. Integer bit costs and encoded-machine identification
remain separate. A second AI agent checked this composition against the
[implementation](../src/contingency115/defect_chain.py).

## Exact schedule

Let `epsilon` be rational with `0<epsilon<1`; put

`a=min(m,n)`, `b=max(m,n)`, `p=mn`, `S=min(p,M)`,

`h=2(m+n-2)+1`, `e=ceil_log2(2h)`, `q=2^e`, `beta=1/q`.

Here `ceil_log2(v)` means the least nonnegative integer `j` with `2^j>=v`, for positive rational `v`; it is computable by integer comparisons. For example the exact Python expression for positive integer `v` is `(v-1).bit_length()`.

Use the integer inverse-gap envelope

`K0=4q p^2 a^2 U^4`.

The reviewed rectangular proof gives full graph variance coefficient at most `4p^2a^2U^4`, so `K0` bounds the ideal dyadic trace's inverse gap. Also `q<=4h<=8(m+n)<=16p/a`, hence `K0<=64p^3aU^4`.

Define

`L0=ceil_log2(4/epsilon)`,
`R=a L0`,
`BU=ceil_log2(U+1)`,
`LR=ceil_log2(4R/epsilon)`,
`T=K0 (p BU+LR)`,
`k=ceil_log2(max(1, R T (S+p-1)/(q epsilon)))`,
`kt=LR`,
`delta=epsilon/(4R)`.

Pass `refresh_bits=k`, `attempts=R`, `steps_per_attempt=T`, `terminal_bits=kt`, and the supplied **ideal** endpoint bound `endpoint_mixing_delta=delta` to the reference sampler. Its configured budgets must cover `RT` transitions and `R[T(e+2k)+kt]` fair bits. This is a numerical schedule to reason about; do not execute its astronomical allowances as a benchmark.

## 1. Stationary rejection exhaustion

At exact defect stationarity, repair followed by acceptance probability `b/support(A)` has exactly uniform table output conditional on success. Its success probability is at least `b/S>=1/a`. Independently restarted ideal stationary attempts consequently fail with probability at most

`(1-b/S)^R <=exp(-R/a) <=2^-L0 <=epsilon/4`.

The code's `stationary_exhaustion=(1-F(b,S))**R` is the corresponding exact rational upper bound. A fixed feasible fallback changes the final law by at most this exhaustion probability.

## 2. Ideal endpoint mixing

Write `N_D` for the number of defect states. Both views have `p` coordinates in `0,...,U`, so

`N_D<=(U+1)^(2p)`.

The ideal dyadic chain is uniform, reversible, half-lazy and has gap at least `1/K0`. The usual finite-chain L2-to-TV bound from any starting defect therefore gives

`TV(endpoint, Uniform(D)) <=½ sqrt(N_D) exp(-T/K0)`.

Since `T/K0=p BU+LR`, `e^-x<=2^-x` for `x>=0`, and `(U+1)^p<=2^(p BU)`,

`TV <=½ 2^-LR <=epsilon/(8R) <=delta`.

Thus `R delta<=epsilon/4`. The slightly stronger `epsilon/(8R)` was not needed for the four equal error allocations. The dimension factor `p BU` must remain in `T`; dropping it would invalidate worst-start mixing.

More generally, `T=ceil(K)[p BU+ceil_log2(4R/epsilon)]` works for any certified `K>=1`: `ceil(K)/K>=1`, so the same calculation applies. `K0` avoids needing a fractional power of `d` or an irrational `C_B` in the actual schedule.

## 3. Finite refresh words

For a uniform k-bit word, `floor(stop*word/2^k)` differs from uniform on `0,...,stop-1` in exact TV

`tau(stop,k)=r(stop-r)/(stop*2^k)`, where `r=2^k mod stop`.

Hence `tau(stop,k)<=stop/(4*2^k)`. Support and label draws use fresh words. Coupling their joint law to the exact product law gives error at most the sum of the two TVs. Their deterministic inverse-repair map cannot increase TV.

Refresh occurs on exactly one channel, with probability `beta`; all other transition branches are exact. Therefore the worst row error satisfies

`eta<=beta min(1,(S+p-1)/(4*2^k)) <=beta(2p-1)/(4*2^k)`.

This is exactly the constructor's `transition_tv_bound`, with the first expression using the sharper support bound. The chosen `k` ensures

`RT eta <= RT(S+p-1)/(4q2^k) <=epsilon/4`.

Sequential kernel coupling costs at most `T eta` per attempt, even though the approximate implemented kernel need not be symmetric and need not preserve the uniform physical stationary law. No stationarity claim about that approximate kernel is required.

## 4. Finite terminal words

For repaired support size `s`, the code accepts a fresh `kt`-bit word below `floor(b2^kt/s)`. Its acceptance probability rounds `b/s` downward by less than `2^-kt`. A coupling of the terminal accept/hold decision therefore costs at most this quantity at every endpoint. Across all attempts,

`R2^-kt <=epsilon/4`.

The code uses one advancing fair-word stream across transitions, refreshes, terminal tests and attempts. Assuming each fair word is uniform conditional on all previous calls, this supplies the fresh randomness needed by these couplings and the independent stationary comparison attempts. Resetting the state without resetting that stream is correct.

## Combined output law

Imagine all `R` attempts planned in advance, then return the first success or the fixed feasible fallback. This has the same output law as the code's early return. Couple each actual attempt to a stationary ideal endpoint and its exact terminal decision. A union bound gives

`TV(output, Uniform(tables))`

`<= (1-b/S)^R + R delta + RT eta + R2^-kt <=epsilon`.

This is the code's four-component `DefectSampleError` bound. It concerns the default fixed-fallback output law. If `use_fallback=False`, exhaustion returns `None`; conditioning on success requires a separate conditional-law estimate and should not be described as this same unconditional table-output theorem.

## Reference work and fair bits

Every transition scans or validates at most `O(p)` entries, constructs at most `O(m+n)` channels, and performs a constant number of uniform-word arithmetic operations. Repair and terminal support counting are `O(p)` integer operations. A feasible fallback can be supplied; ordinary equal-total margins also admit the elementary greedy construction with `O(p)` storage initialization and at most `m+n-1` nonzero assignments.

Thus the walk/terminal work is `O(pR(T+1))` **integer arithmetic operations**. Let `Lambda=1+ln(1/epsilon)`. Since

`R=O(a Lambda)`,

`T=O(p^3 a U^4 [p log(U+1)+log(R/epsilon)])`,

the explicit shape-aware operation envelope is

`O(p^4 a^2 U^4 Lambda [p log(U+1)+Lambda+log p])`.

Its leading mass-log term is `O(p^5 a^2 U^4 Lambda log(U+1))`. Using `a^2<=p`, `p<=d` and `U=5d^3` gives

`O(d^18 Lambda log d + d^17 Lambda^2)`.

The planned fair-bit bound is exactly

`R[T(e+2k)+kt]`.

Here `e=O(log p)`, `k=O(log d+Lambda)` and `kt=O(log d+Lambda)` at the ideal scales. This bit count is separate from the integer-operation count and from the internal cost of processing those bits.

Python shifts, multiplication, floor division, validation and `Fraction` normalization use arbitrary-size integers. They are not constant-time machine operations. In particular, refresh arithmetic handles k-bit words; state values use `O(log U)` bits; the exact reported exhaustion rational can have `O(R log p)` numerator/denominator bits. The constructor and result error arithmetic also have their own cost. None of those bit costs has been composed with a literal formally identified bounded-word program here. Consequently the operation allowance is not the original sampler's numeric complete runtime degree, and should not be labeled a compiled bit-machine exponent.

## Scope and verification limit

The Python class accepts a broader one-side-small branch, but the gap premise used above is the new **both-small** rectangular proof. Passing the constructor's scope check alone does not establish this mixing schedule. The entire proof also assumes ordinary unrestricted margins and conditionally uniform fair words. No nonempty completion oracle, general large-margin branch, cap or weighted law is covered.
