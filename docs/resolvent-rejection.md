# Killed-resolvent refinement of spaced rejection

Mathematical derivation, 11 October 2026, reviewed by separate AI agents. The bounded implementation is an opt-in mode of [defect_chain.py](../src/contingency115/defect_chain.py). The [finite killed-chain exhaustion bound](../research/spaced-attempts/#finite-killed-chain-exhaustion) now has a fresh Lean compilation and dependency audit. The infinite first-acceptance bias and full resolvent theorem remain reviewed mathematics; the earlier finite hybrid lemma has its separate receipt. The new bound controls the entire first-accept output law, not merely the exhaustion probability. It replaces spacing proportional to `K log(R/epsilon)` by spacing proportional to `K log(1/epsilon)`, independently of success probability and mark count. The cold-start term and the gap theorem are unchanged.

## Precise theorem

Let X,Y be finite, `pi(x)>0`, and let Q be a reversible stationary Markov kernel that is positive semidefinite on L2(pi). Assume its centered operator norm is at most `rho<1`. This holds for `Q=P^t` when P is reversible and half-lazy, with `rho<=exp(-t/K)` from inverse-gap allowance K.

Let `A(x,y)>=0` be a terminal subkernel, `a(x)=sum_y A(x,y)<=1`, and let rejection leave the chain state unchanged. Set `f=1-a`, `s=pi a>0`, and assume the exact stationary successful output identity `pi A=s nu`.

Starting at pi, mark immediately; after rejection evolve by Q and mark again. The infinite first accepted output law `xi_infinity` satisfies

`TV(xi_infinity,nu) <=rho sqrt(1-s)/[2(1-rho)^2] <=rho/[2(1-rho)^2]`.

After at most R marks with a fixed fallback, the finite output law satisfies

`TV(xi_R,nu) <=rho/[2(1-rho)^2] + [1-(1-rho)s]^R`.

A sharper exhaustion term is `(1-s)[1-(1-rho)s]^(R-1)`. If s is only known to be at least s0, replace s by s0 in the simple R-th-power term.

After an approximate initial burn-in and bounded transition/terminal approximations, add `delta_burn+W eta+R zeta`, with the same uniform row-TV and terminal-TV hypotheses used by the existing additive-hybrid proof. Nothing asserts that conditioning on rejection preserves stationarity.

## 1. Spectral killing and failure normalization

Use column-vector densities relative to pi. The failure-then-move density operator is **QF**, where `F=diag(f)`: multiplication by f first, then Q acts on the density because Q is reversible. Measures instead evolve as row vectors by **FQ**. The two orientations must not be interchanged in the resolvent.

The centered spectral bound gives the Loewner inequality

`Q<=rho I+(1-rho)Pi`, where `Pi g=(pi g)1`.

Let `H=sqrt(F) Q sqrt(F)`. It is positive semidefinite and self-adjoint. For any u,

`<u,Hu> <=rho ||sqrt(f)u||^2+(1-rho)<sqrt(f)u,1>^2`

`<= [rho+(1-rho)(1-s)]||u||^2`.

Thus `||H||<=lambda:=1-(1-rho)s<1`.

The probability that the first R marks all fail, with only R-1 intervening Q blocks, is exactly

`m_R=<sqrt(f), H^(R-1) sqrt(f)>`.

This equals `1-s` at R=1. It is at most `(1-s)lambda^(R-1)<=lambda^R`, since `1-s<=lambda`. In particular, absorption occurs almost surely and the expected number of marks satisfies

`E[number of marks]=1+sum_(R>=1) m_R`

`<=1+(1-s)/[(1-rho)s] <=1/[s(1-rho)]`.

No inverse of F or sqrt(F) is used: coordinates with a=0 or a=1 are allowed. For a identically one, immediate acceptance is exact and the sharper failure bound is zero.

## 2. Visitation density and its centered norm

The pre-mark visitation density is the convergent finite-state series

`w=sum_(j>=0)(QF)^j 1`.

Convergence follows from the preceding summable survivor masses and positive pi: each coordinate's visit sum is bounded by the total expected marks divided by its positive pi weight. Write `m=pi w` and `h=w-m`. The series satisfies

`w=1+Q(fw)`, `m<=1/[s(1-rho)]`, and `pi(aw)=1`.

The last equality is absorption normalization: sum the accepted mass over every mark. It is essential; without it the output-bias comparison would be between measures of different mass.

Since Q-Pi kills constants,

`h=(Q-Pi)(fw)`.

Center f, expand `fw=mf+fh`, and use `0<=f<=1`:

`||h|| <=rho[m sqrt(Var_pi(a))+||(I-Pi)(fh)||]`

`<=rho[m sqrt(s(1-s))+||h||]`.

Consequently

`||h|| <=rho m sqrt(s(1-s))/(1-rho)`.

The mean m can be large when acceptance is rare; the next step weights the output discrepancy by a and cancels that apparent success penalty.

## 3. Arbitrary output kernel and the factor one half

For any output event B, put `A_B(x)=sum_(y in B)A(x,y)`. The infinite accepted mass is `xi_infinity(B)=pi(w A_B)`. Since `pi A_B=s nu(B)` and `pi(aw)=1`,

`xi_infinity(B)-nu(B)=<h, A_B-nu(B)a>`.

Where a>0 let `z=A_B/a`; where a=0 define z=0. Then `0<=z<=1`. Under the probability measure `pi(x)a(x)/s`, its mean is nu(B), so

`||A_B-nu(B)a||^2 =pi[a^2(z-nu(B))^2]`

`<=s Var_(pi a/s)(z) <=s nu(B)(1-nu(B))<=s/4`.

Cauchy-Schwarz gives `|xi_infinity(B)-nu(B)|<=sqrt(s)||h||/2`. Taking the supremum over B and using the preceding bound on m proves

`TV(xi_infinity,nu)<=rho sqrt(1-s)/[2(1-rho)^2]`.

This is a bound between **probability measures**, with the usual TV convention `sup_B |mu(B)-nu(B)|=half L1`. It applies to arbitrary randomized terminal outputs, not just returning the chain state or a deterministic repair.

## 4. Finite marks, burn-in and rounded execution

Couple the R-mark algorithm to its infinite continuation using the same first R marks. Their outputs can differ only if all R marks fail. Hence their TV is at most m_R. This supplies the finite theorem, including the correct actual killed-chain exhaustion term.

Apply the same bounded output algorithm to the actual post-burn distribution and pi; stochastic-kernel contraction charges delta_burn once. Couple rounded transitions and terminal decisions sequentially over the planned W transitions and R marks; these add at most W eta and R zeta. Reversibility is needed only for the ideal spectral proof, not for the rounded implemented chain.

## 5. Exact integer schedule

For rational `0<epsilon<1`, choose

`L0=ceil_log2(4/epsilon)`, `LP=ceil_log2(8/epsilon)`, `rbar=2^-LP`,

`R=ceil(L0/s0)`, `SPACE=K0 LP`.

Here K0 is any integer inverse-gap allowance. The ideal spacing contraction is at most rbar. Since rbar<=1/8, its infinite-output bias is at most rbar, and therefore at most epsilon/8. The killed failure bound is

`[1-(1-rbar)s0]^R <=exp[-R(1-rbar)s0] <=exp[-3L0/4] <=2^-L0<=epsilon/4`.

For the last inequality, `exp(3/4)>=1+3/4+(3/4)^2/2=65/32>2`. This uses the existing conservative base-two restart count; no extra marks are needed to offset correlation. For the unit chain, keep exactly the old `R=a L0`. Since R>=6 there, the new `LP=ceil_log2(8/epsilon)` is at most the old `ceil_log2(2R/epsilon)`. The burn-in, mark count and terminal word width are unchanged, while planned transitions and refresh word width never increase. The gain is strict whenever those two spacing logarithms differ.

Retain a burn-in with delta_burn<=epsilon/8. The burn plus absorption-bias group then costs at most epsilon/4. Allocate W eta<=epsilon/4 and R zeta<=epsilon/4. This yields total error at most epsilon.

For the positive both-small defect chain, use s0=b/S, or its conservative lower bound 1/a, where `a=min(m,n), b=max(m,n), S=min(p,M)`. With the same safe coordinate count as before,

`BURN=K0[p ceil_log2(U+1)+L0]`, `W=BURN+(R-1)SPACE`,

`k=ceil_log2(max(1,W(S+p-1)/(q epsilon)))`,

`kt=ceil_log2(4R/epsilon)`.

The new exact rational certificate is

`[1-(1-rbar)s0]^R + 1/(2*2^L0) + rbar/[2(1-rbar)^2] + W eta + R/2^kt`.

**Do not reuse** the old `(1-s0)^R` exhaustion term: first-accept samples are correlated. The old additive `(R-1)rho/4` spacing certificate remains valid and may be cheaper for very short plans. Selecting the better certified schedule is legitimate.

If s0=1, a is identically one under positive pi and one post-burn mark suffices; no spacing or retry loop is required.

## 6. Honest cost comparison

Let `Lambda=1+ln(1/epsilon)`. For local step cost c and terminal cost at most c, the new work is

`O(c K[log(1/pi_min)+Lambda+s0^-1 Lambda^2])`.

The previous additive-hybrid schedule instead has marked-phase work proportional to `c K s0^-1 Lambda[log(s0^-1)+log Lambda+Lambda]`. The resolvent removes both success-probability and mark-count logarithms from spacing. It does not remove the first cold-start logarithm, does not change K, and does not change the epsilon dependence from bounded-word rounding.

With the earlier both-small shape bound `K<=64p^3aU^4`, c=O(p), and `s0>=1/a`, the envelope becomes

`O(p^5aU^4 log(U+1)+p^4a^2U^4 Lambda^2)`.

At `U=5d^3`, this is `O(d^(35/2)log d+d^17 Lambda^2)`, compared with the existing `O(d^(35/2)log d+d^17 Lambda(log d+Lambda))`. The main cold-start dimension exponent stays the same.

The lemma also accepts the later effective-width and general weighted trace K without changing that gap premise. Its weighted cold-start logarithm still depends on the actual pi_min; counting states alone is insufficient for nonuniform pi. Planned fair bits are `W(e+2k)+Rkt` for the unit direct walker. Integer bit complexity and encoded-machine identification remain separate.

## Sources and limits

The spectral and killed-chain framework is classical; the full output-discrepancy derivation is given above rather than inferred from a quasistationary approximation. Primary references checked live are Aldous and Fill, [Dirichlet/spectral and killed-chain characterizations](https://www.stat.berkeley.edu/~aldous/RWG/Book_Ralph/Ch3.S6.html), and their [flow/Cheeger inequalities](https://www.stat.berkeley.edu/~aldous/RWG/Book_Ralph/Ch4.S5.html). No novelty or priority claim is made.

The exact rational audit covers nonconstant acceptance, zeros and ones, randomized output kernels, full resolvent normalization and finite-R exhaustion. Separate counterexamples show linear dependence on rho cannot be generically replaced by a vanishing-success factor, and a gap-only cold-start bound cannot lose its log(1/pi_min) term. The rare-acceptance and cold-start constructions are derived in [spacing obstructions](spacing-obstructions.md). Their exact checks are included in the report. The compiled hybrid lemma and killed-chain exhaustion bound do not by themselves compile the infinite first-acceptance bias or full resolvent argument.

## Executable mode and reproduction

Pass `bound_method="resolvent"` to `both_small_spaced_schedule` and to
`sample_spaced`. The returned schedule records this method. The default
`"hybrid"` mode retains its original behavior and certificate; the two modes
share the same bounded execution loop. The resolvent mode rejects `rho>=1`
and pairs its bias with the killed-chain failure term above.

For margins `(2,2)` on each side, `U=3` and epsilon `1/8`, the old schedule
plans 28,200,960 transitions and 1,635,655,770 fair bits. The new mode plans
22,228,992 transitions and 1,289,281,626 bits. These are conservative planned
allowances, not measured speed or a recommendation to execute such a walk.

The [exact rational report](../reports/resolvent-rejection.json) checks 33
kernel/acceptance configurations, including zero and certain acceptance,
randomized output kernels, rare-hit bias, and cold-start obstructions.
Separate AI review checked the proof and implementation. Reproduce with:

```sh
python3 experiments/resolvent_rejection.py --output .local/reports/resolvent-rejection.json
```
