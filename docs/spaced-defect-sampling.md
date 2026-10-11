# One burn-in, spaced terminal marks

Mathematical derivation, 11 October 2026, reviewed by separate AI agents. The bounded implementation is in [defect_chain.py](../src/contingency115/defect_chain.py). The finite hybrid lemma now has a [fresh scoped Lean proof](../research/spaced-attempts/); its physical spectral specialization, approximation extension and machine-runtime integration remain open. A general finite reversible Markov lemma removes repeated cold starts. It handles a weighted stationary law and an arbitrary exact terminal output kernel. The gap theorem is unchanged; the gain comes from composing rejection and mixing differently.

The later [resolvent refinement](resolvent-rejection.md) removes the mark-count logarithm from spacing. Its stronger proof and optional implementation have separate AI review and exact checks, but are not covered by the hybrid Lean receipt below.

## General lemma

Let `X,Y` be finite, let `pi(x)>0`, and let `P` preserve `pi`. Assume `P` is reversible and half-lazy, with inverse-gap allowance `K>=1`. Thus its centered L2(pi) contraction after `t` steps is at most `exp(-t/K)`.

Let `A(x,y)>=0` be a subprobability terminal kernel, with `a(x)=sum_y A(x,y)<=1`. Acceptance returns `y`; rejection has probability `f(x)=1-a(x)` and **leaves the current chain state x unchanged**. Suppose

`pi A = s nu`, with `s>=s0>0` and `nu` the desired probability law on Y.

Run a burn-in from any initial law, whose endpoint is at TV distance at most `delta0` from `pi`. Mark that endpoint. After each rejection, continue the **same** chain for `t` transitions and mark again, for at most `R>=1` marks. If all marks fail, return a fixed fallback output. Then

`TV(output,nu) <= delta0 + (1-s)^R + (R-1)/4 * exp(-t/K)`.

More generally, replace the exponential by any certified centered L2 contraction `rho` of the spacing block. If each executed transition differs uniformly from P by at most `eta` in row TV, and each executed terminal accept/output kernel differs by at most `zeta` in TV, the bound becomes

`delta0 + (1-s)^R + (R-1)rho/4 + W eta + R zeta`,

where `W` is the planned total transition count, including burn-in. Early stopping only reduces actual work; it does not require a different probability bound.

This statement does **not** assert that the chain remains stationary after rejection or that an unspaced first accepted output has law nu.

## Proof: retain unnormalized failure mass

For positive measures of equal mass, use `TV(mu,lambda)=1/2 sum_x |mu(x)-lambda(x)|`. Start the analysis at exact pi; the initial burn-in error will be charged once by applying the same future algorithm kernel to the two initial distributions.

Let `mu` be the **unnormalized** distribution of the surviving state after a common actual prefix: `mu(x)` is the joint probability that every previous mark failed and the state is x. Initially `mu=pi`. Multiplication by `f<=1` and a stationary Markov transition each preserve domination:

`0<=mu<=pi` implies `mu diag(f)<=pi` and `mu P<=pi P=pi`.

Therefore every such survivor has density `g=mu/pi` in `[0,1]`. Its mass is `m=sum_x mu(x)`. Since `g^2<=g`,

`||g-m||_(2,pi)^2 = E_pi[g^2]-m^2 <=m(1-m)<=1/4`.

Reversibility makes the density of `mu P^t` equal to `P^t g`. Centered L2 contraction and Cauchy-Schwarz give

`TV(mu P^t,m pi) <=1/2 ||P^t(g-m)||_(2,pi) <=rho/4`.

Both measures here have **the same mass m**. No conditioning or division by a possibly tiny survival probability occurs. The argument is valid for arbitrary positive pi, and does not involve pi_min or the state count.

Define hybrids `H_j`, `j=0,...,R-1`: the first `j` inter-mark blocks use the actual `P^t`, and all subsequent blocks use the complete-refresh kernel `Pi(x,w)=pi(w)`. The initial mark is the same exact stationary mark for every hybrid.

For consecutive hybrids, the common actual prefix has the same already-absorbed output measure and the same surviving subprobability mu. At the one differing block, replace `mu P^t` by `m pi`. Their TV is at most `rho/4`. The common future accept/reject/fallback algorithm is a stochastic output kernel, hence contracts this same-mass TV. Summing the `R-1` differences proves

`TV(H_(R-1),H_0)<=(R-1)rho/4`.

In `H_0`, each candidate is drawn freshly from pi. The stationary terminal kernel has successful output law `s nu`, so

`law(H_0)=[1-(1-s)^R]nu+(1-s)^R PointFallback`.

Its TV distance from nu is at most `(1-s)^R`. An initial endpoint error `delta0` is charged exactly once by output-kernel contraction. Uniform transition and terminal perturbations add at most `W eta` and `R zeta` by sequential coupling of the planned bounded algorithm, even though the executed approximate kernel need not have stationary law pi. This proves the lemma.

For a finite reversible half-lazy chain with gap at least `1/K`, diagonalization in L2(pi) gives eigenvalues in `[0,1-1/K]` on the centered subspace, so `rho<=(1-1/K)^t<=exp(-t/K)`. That is the only spectral input.

## Explicit obstruction to naive first acceptance

Take `pi=(1/2,1/3,1/6)` and `P=(I+Pi)/2`, where every row of Pi is pi.
This chain is reversible and half-lazy, with centered contraction exactly
`1/2`. At state x, return label x with acceptance probability
`a=(1/3,1/2,1)`. The stationary successful masses are all `1/6`, so one
stationary mark succeeds with probability `1/2` and gives uniform output.

Starting at exact pi and trying eight marks **without intervening transitions**,
with fallback label zero, instead gives

`output=(385/768,85/256,1/6)`, `TV(output,uniform)=43/256`.

The incorrect independent-attempt exhaustion bound would be only `1/256`.
Even continuing with one transition between marks, indefinitely until the first
acceptance, gives `(9/23,8/23,6/23)`, at TV distance `5/69` from uniform.
The [exact rational reproducer](../experiments/marked_chain_audit.py) checks both
counterexamples, along with survivor domination, block contraction, and the
finite corrected bounds. Spacing controls bias; finite spacing does not make
repeated rejection an exact sampler.

## Both-small defect specialization and exact integer schedule

Use positive ordinary both-small margins, `m,n>=2`, and the reviewed dyadic defect trace. Let

`a=min(m,n)`, `b=max(m,n)`, `p=mn`, `S=min(p,M)`,

`h=2(m+n-2)+1`, `e=ceil_log2(2h)`, `q=2^e`, `beta=1/q`,

`K0=4q p^2a^2U^4 <=64p^3aU^4`.

Its stationary law is uniform on defects. Repair and exact acceptance probability `b/support(A)` give the uniform table target and stationary success at least `b/S>=1/a`. Rejection leaves the actual defect state unchanged; repairing merely computes a candidate table.

For rational `0<epsilon<1`, choose

`L0=ceil_log2(4/epsilon)`, `R=a L0`,

`BU=ceil_log2(U+1)`, `BURN=K0(p BU+L0)`,

`LB=ceil_log2(2R/epsilon)`, `SPACE=K0 LB`,

`W=BURN+(R-1)SPACE`,

`k=ceil_log2(max(1, W(S+p-1)/(q epsilon)))`,

`kt=ceil_log2(4R/epsilon)`.

Run one BURN block, mark, then SPACE between subsequent marks, with no state reset. Use k-bit finite refresh words and kt-bit terminal words.

Defects are unique pairs `(x,q)` with `2p` entries in `0,...,U`, so `N_D<=(U+1)^(2p)`. This explicitly includes the possible defect labels and their multiplicities. Consequently

`delta0<=1/2 sqrt(N_D)exp(-BURN/K0)<=1/2*2^-L0<=epsilon/8`.

Also `rho<=exp(-SPACE/K0)<=2^-LB`, and

`(R-1)rho/4 <=epsilon/8`.

The two mixing terms total at most `epsilon/4`. The other three error groups are

`(1-b/S)^R<=epsilon/4`,

`W eta <=W(S+p-1)/(4q 2^k)<=epsilon/4`,

`R2^-kt<=epsilon/4`.

Thus the actual rounded sampler with a fixed feasible fallback has TV error at most epsilon. An entirely rational error certificate is

`(1-b/S)^R + 1/(2*2^L0) + (R-1)/(4*2^LB) + W*eta + R/2^kt`.

The uniform row perturbation eta is the constructor's bound `beta min(1,(S+p-1)/(4*2^k))`. The terminal rounding is less than `2^-kt`. These exact-word estimates are unchanged from the existing restarted composition; only the planned transition count and the ideal mixing certificate change.

## Cost gain: schedules, not a new gap

Let `Lambda=1+ln(1/epsilon)`. The cold burn is now paid once:

`W=O(K0[p log(U+1)+Lambda+a Lambda(log p+Lambda)])`.

Each transition and terminal uses `O(p)` integer operations. The new shape-aware work envelope is

`O(p^5aU^4 log(U+1)+p^4a^2U^4 Lambda(log p+Lambda))`.

The smaller initial-accuracy term `p^4aU^4 Lambda` is absorbed by the second term. At `U=5d^3`, `p<=d`, and `a<=sqrt(p)`, this becomes

`O(d^(35/2) log d+d^17 Lambda(log d+Lambda))`.

This is uniform over arbitrary rectangular aspect ratios within the both-small scope. It improves the prior restarted operation allowance `O(d^18 Lambda log d+d^17 Lambda^2)` by avoiding repeated cold `p log U` mixing costs. The ideal inverse-gap allowance stays the same.

Planned fair bits are bounded by `W(e+2k)+Rkt`. Arbitrary-size integer arithmetic, Fraction normalization, the rational epsilon representation, and encoded program identification still have their own costs. This is neither a compiled bit-machine exponent nor a guarantee for the broader constructor's one-side-small or nonempty completion branch.

## Executable interface and evidence

`both_small_spaced_schedule(problem, U=..., epsilon=Fraction(...))` constructs
these integer parameters without executing a walk. Its result exposes the
inverse-gap allowance, burn-in and spacing lengths, word widths, two separate
mixing premises, and planned steps/fair bits. It validates both-small scope;
the broader one-side-small constructor alone does not justify this schedule.
For example, inspecting the bounds is cheap:

```python
from fractions import Fraction
from contingency115.tables import TableProblem
from contingency115.defect_chain import both_small_spaced_schedule

schedule = both_small_spaced_schedule(
    TableProblem((2, 2), (2, 2)), U=3, epsilon=Fraction(1, 8))
print(schedule.planned_steps, schedule.planned_fair_bits)
# 28200960 1635655770
```

These conservative numbers are not practical performance predictions. The
schedule does not increase execution budgets. To execute a chosen bounded
plan, construct `DyadicDefectChain` with its `refresh_bits`, then call
`sample_spaced` with the corresponding attempts, burn-in, spacing, terminal
bits, `burnin_mixing_delta`, and `spacing_l2_contraction`. The latter is a
centered L2 operator bound, not an endpoint TV bound. Arbitrary values passed
to the API remain premises; the routine cannot establish them from observed
outputs. The original restarted `sample` API remains available and shares the
execution loop.

Focused tests enumerate every finite-word output of a two-mark plan, compare
it with independently composed transition kernels, and distinguish continuing
from restarted behavior. They also check exact error allocations, advancing
randomness, early stopping, and budget rejection before random draws. Reproduce
the separate finite Markov experiment with

```sh
python3 experiments/marked_chain_audit.py --output .local/reports/marked-chain.json
```

The [saved report](../reports/marked-chain.json) contains nine exact finite
schedules and the negative examples. Complete physical Lean assembly of the
rectangular bound, this new dependent-attempt lemma, and the encoded sampler
remain open. The generic lemma itself also accommodates the weighted general
terminal, but no complete general-branch implementation or cost composition
is claimed here.
