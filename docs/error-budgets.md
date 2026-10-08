# Error budgets, exact correction, and bounded weight evaluation

**Status: analytic derivations with executable exact-arithmetic checks.** These
refinements use the original manuscript scales unless an alternative bound is
explicitly supplied. They do not depend on the proposed localized transport
theorem or reduced scales. They are not new Lean proofs, a completed universal
sampler/FPRAS, or a measured runtime improvement.

The implementation is [`budgets.py`](../src/contingency115/budgets.py), with
[`test_budgets.py`](../tests/test_budgets.py) and a deterministic
[`comparison report`](../reports/budget-comparison.json). Reproduce with:

```sh
PYTHONPATH=src python3 -m unittest discover -s tests -p test_budgets.py -v
PYTHONPATH=src python3 experiments/budget_report.py --output reports/budget-comparison.json
```

All schedule decisions use integers and rational numbers. Floating-point fields
in the report are marked as display-only. The tests include independent finite
output-law enumeration, minimal integer-threshold checks, variance extremizers,
negative controls, and exact probability identities. These tests corroborate the
derivations below; finite checks do not prove a universal statement.

## Pinned sources and scope

The baseline is OpenAI `math` commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`:

- [Sampling algorithms and law tabulation][sampling]: equations
  `outer-error`, `bit-schedule`, `cached-dense-law`, `implemented-kernel`,
  `outer-geometric-law`, and `residual-integers`.
- [Dense sampling][dense]: the proof of `lem:mixing`, `prop:bin-gap`,
  `dense-lipschitz`, `dense-penalty`, `dense-total-error`, and
  `dense-denominator-bounds`.
- [Bounded-table weight evaluation][counting]: `bin-conductance`,
  `bin-mixing`, `inner-parameters`, `inner-walk-length`, `oracle-telescope`,
  and the correction-arithmetic argument.
- [Compiled exact parameters][exact-lean] still use the original precision
  policy. Their `marginBinaryLength` parameter must not silently be equated
  with the manuscript's capacity-based `b`.

`inverse_gap_bound` in the APIs is an obligation, not a certificate produced by
the code. The input must bound the inverse gap of the actual finite, lazy,
reversible ideal chain. The mass and success bounds must also apply to that
chain. A numerical eigenvalue estimate does not supply a rigorous bound.
The new outer and dense default bounds are extracted from the original
manuscript proof, not from any conjectural improvement elsewhere in this repo.

## 1. Retain the stronger mixing inequality already in the proof

The source's spectral argument reaches

$$
 \|P^t(x,\cdot)-\pi\|_{\rm TV}
 \le\tfrac12\sqrt{\pi(x)^{-1}-1}\exp(-t/K).
 \tag{1}
$$

It then weakens the prefactor to $\pi_{\min}^{-1}$. We retain (1).
If $\pi_{\min}^{-1}\le2^s$, it is sufficient for TV error
$2^{-\ell}$ to take

$$
 t=\left\lceil qK\max\{0,s/2+\ell-1\}\right\rceil,
 \qquad q=7/10.
 \tag{2}
$$

Here $\ln2<q$: the degree-four Taylor sum of $e^{7/10}$
already exceeds 2. Thus $e^{-qv}\le2^{-v}$ for $v\ge0$.
This replaces floating-point logarithms with an exact rational calculation
and halves the log-mass allowance. A known singleton should simply be handled
deterministically.

For conductance constants we also use $\ln2\ge2/3$. One elementary
proof integrates
$1/x\ge4/3-4x/9$ on $[1,2]$; the difference is
$(2x-3)^2/(9x)$.

## 2. Outer sampler schedules

The source has success at least $1/[2(1+d^2)]$,
$\pi_{\min}^{-1}\le(C+1)^{2d}\le2^{2db}$, and uniform
dense-call error $2^{-h}$. Keep its independent trials, fresh
completion draws, first-success rule, and feasible fallback. Combining (1)
with the same coupling proof bounds error by

$$
 e^{-J/[2(1+d^2)]}
 +\tfrac J2\,2^{db}e^{-T/K}
 +J(T+1)2^{-h}.
 \tag{3}
$$

For requested accuracy $2^{-k}$, choose

$$
\begin{aligned}
 J&=\left\lceil2q(1+d^2)(k+2)\right\rceil,\\
 \ell_o&=k+2+\lceil\log_2J\rceil,\\
 T&=\left\lceil qK(db+\ell_o-1)\right\rceil,\\
 h&=k+2+\lceil\log_2[J(T+1)]\rceil.
\end{aligned}
\tag{4}
$$

Each term of (3) is at most $2^{-k-2}$; their sum is at most
$3\,2^{-k-2}<2^{-k}$. Approximate transitions need not preserve
the ideal stationary distribution: the argument couples the finite trajectory
until its first disagreement, as the original paper does.

The default uses the source's explicit, original-scale bound

$$
 K_6=128d^2\bigl[(1+2d^2)4d^2(d^{20}+1)^6+2\bigr].
$$

For the review's example $r=c=(3,3)$, $d=19,b=104,k=20$:

| Schedule | Trials | Transitions per trial | Dense accuracy bits |
|---|---:|---:|---:|
| Published powers | 2,736,741 | about $8.66\times10^{259}$ | 2,003,815,696 |
| Initial review, existing $K_6$ | 15,928 | about $5.43\times10^{167}$ | 594 |
| Equation (4), same $K_6$ | 11,150 | about $1.92\times10^{167}$ | 592 |

These remain enormous worst-case allowances. The four-table example is trivial
to enumerate directly. The comparison isolates proof slack and makes no claim
about practical speed or the complete bit-cost exponent.

## 3. Dense sampling, constants, and finite-bit draws

Before relaxation, the dense conductance proof gives

$$
 \kappa_B\ge\frac{\ln2}{1024d^2K_0}
 \ge\frac1{1536d^2K_0},\qquad K_0=4B.
$$

Thus the same Cheeger argument permits
$K_B=2(1536d^2K_0)^2$, rather than the source's displayed
$2(10^5d^2K_0)^2$. This is a factor
$(100000/1536)^2\approx4238.55$ in that inverse-gap allowance.
The weights also give the generic log-mass allowance

$$
 s_B=4Ad+d\lceil\log_2(4B)\rceil,
 \qquad\pi_{B,\min}^{-1}\le2^{s_B}.
 \tag{5}
$$

For requested dense accuracy $2^{-h}$, take

$$
\begin{aligned}
 J_D&=\lceil64q(h+2)\rceil,\\
 \ell_D&=h+2+\lceil\log_2[J_D(1+d)]\rceil,\\
 H_D&=\lceil qK_B(s_B/2+\ell_D-1)\rceil.
\end{aligned}
\tag{6}
$$

The failure term obeys
$(63/64)^{J_D}\le e^{-J_D/64}\le2^{-h-2}$.
Give the bin draw and each of at most $d$ offsets error
$2^{-\ell_D}$. All draw discrepancies then total at most
$J_D(1+d)2^{-\ell_D}\le2^{-h-2}$. The sum is at most
$2^{-h-1}$, leaving half the target budget unused.

For $d=19,h=20$ with the original scales, the initial review's
$H_D\approx1.19\times10^{44}$ falls to approximately
$9.84\times10^{39}$; trials fall from 1,408 to 986. The reduction
in this transition allowance is approximately 12,109, combining the extracted
conductance constant, prefactor, and rational log conversion. It is not a
runtime measurement.

### Exact offset error, saving up to two bits

Let $Q=2^r=aw+t$, $0\le t<w$. For
$U$ uniform on $\{0,\ldots,Q-1\}$, the map
$\lfloor wU/Q\rfloor$ has $t$ outcomes with $a+1$
preimages and $w-t$ with $a$. Direct summation gives

$$
 \operatorname{TV}=\frac{t(w-t)}{wQ}\le\frac{w}{4Q}.
 \tag{7}
$$

For tolerance $\zeta\in(0,1)$, it suffices to use
$r=\max\{0,\lceil\log_2[w/(4\zeta)]\rceil\}$.
When $w$ is a power of two, $\log_2w$ bits give an exact
draw and can be used if fewer. Width one needs zero bits. This is a bounded
map, with no rejection loop. Fewer offset bits generally change the law, even
though the same error target remains valid.

### One acceptance bit for an adjacent bin move

The source proves that $p$ is $(d/B)$-Lipschitz in sup norm.
For neighboring bins $v,v'$, under the original scales
$Ad/B=d^{-3}\le1$, so

$$
 |Ap(v)-Ap(v')|\le1
 \quad\Longrightarrow\quad
 |\lfloor Ap(v)\rfloor-\lfloor Ap(v')\rfloor|\le1.
$$

An acceptance probability is therefore either one or one half; it needs at
most one fair bit. The source allows $8Ad$ bits. This tightens the
denominator and reserved-bit allowance without changing the kernel. For
$d=19$, the uniform per-transition allowance drops from 19,808,800
bits to 9, including proposal bits. This says nothing about how many unused
bits an optimized implementation of the original program actually reads.

The bounded paper has the same local conclusion: its penalty is
$1/8$-Lipschitz, and $a/H\le1$, so neighboring floor
exponents differ by at most one rather than its global allowance $H$.
New generic scales must re-establish the relevant local Lipschitz bound.

## 4. Exact correction: separate the two precision requirements

Suppose the *actual* approximate output law on the complete feasible fiber is
$p_k$, with TV error at most $\eta=2^{-k}$ from uniform.
Let $M$ be the fiber size, $M\le M_*$, and choose a rare
probability $\delta=2^{-D}$. The exact sufficient condition is

$$
 (1-\delta)(1/M+\eta)\le1/M
 \quad\Longleftrightarrow\quad
 \eta\le\frac\delta{M(1-\delta)}.
$$

Consequently the smallest integer precision obtained from the bound $M_*$
is

$$
 k=\left\lceil\log_2\bigl[M_*(2^D-1)\bigr]\right\rceil.
 \tag{8}
$$

The public approximate sampler requires $k\ge1$; the implementation
enforces that. A known singleton can be returned directly. The threshold
utility computes (8) without constructing $2^D$, by comparing integer
bit lengths and one shifted count bound. A non-power-of-two count bound may
save another bit compared with $D+\lceil\log_2M_*\rceil$.

Independently, if the correction branch has certified conditional expected cost
$2^{adb}\operatorname{poly}(d,b,k)$, set

$$
 D=adb+s,\qquad s\ge0.
 \tag{9}
$$

The exponential factor in its unconditional expectation is exactly
$2^{-s}$. The review used $s=1$; $s=0$ already suffices
for polynomial expected cost. With only $M_*\le2^{db}$, use
$k=D+db$. Thus the original manuscript exponent $a=500$
supports a linear-in-$db$ precision policy at the source level.

For the example $d=19,b=104$, the published accuracy parameter is
1,017,696,497,792. The review reduced it to 989,977. Taking $s=0$
gives 989,976; the elementary bound $M_*\le4$ gives 988,002.
The latter is about 1.03 million times smaller than the published precision
parameter, not a million-fold runtime improvement.

The manuscript's operation count $2^{10db}\operatorname{poly}(d,b,k)$
with polynomial operand lengths suggests a smaller source-level cost exponent.
The API permits a supplied exponent, but 10 is **not** treated here as a proved
compiled-machine bound. The default remains 500, and a revised program still
requires its own cost argument and conversion to public input lengths.

### Count bounds that do not enumerate the fiber

Weak compositions give

$$
 M\le\prod_i\binom{r_i+n-1}{n-1},\qquad
 M\le\prod_j\binom{c_j+m-1}{m-1}.
$$

For any fixed row $i_0$ and column $j_0$, all entries outside
that row and column determine the remaining entries through the margins.
The map to those free entries is injective, hence

$$
 M\le\prod_{i\ne i_0,\,j\ne j_0}(\min\{r_i,c_j\}+1).
 \tag{10}
$$

The code minimizes these bounds, including all choices of reference row and
column. Their binary lengths and arithmetic work are polynomial in the margin
encoding and dimensions. They upper-bound capped subfibers too, but they do
not test capped feasibility. For $(3,3);(3,3)$, (10) is 4, the
actual count.

### Residual identity and a short-circuit gate

If $p_k(z)=a_z/2^R$, the residual integer weights remain

$$
 n_z=2^{R+D}-M(2^D-1)a_z,\qquad
 \sum_z n_z=M2^R.
 \tag{11}
$$

Equation (8) makes them nonnegative, and
$(1-\delta)p_k(z)+\delta n_z/(M2^R)=1/M$ exactly.
The supplied numerator list must include **every target table**, including
tables of zero approximate probability. Using only the positive support would
silently change $M$ and the target distribution.

For the all-zero gate, stop at the first one. Its rare probability is still
$2^{-D}$, while expected gate reads are
$\sum_{i=1}^D2^{-(i-1)}=2-2^{1-D}<2$. Its worst case is still
$D$. Subsequent draws use fresh independent bits. The implementation
and tests enumerate all short gate strings and all small dyadic laws, including
negative residuals that must be rejected.

## 5. A stronger concentration bound for the independent inner oracle

Keep the source's
$\sigma=\xi_{\rm in}/[50(H+1)]<1/200$.
The ratio observables lie in $[1/2,1]$; the final correction lies in
$[1/8,4]$. Samples within each average are independent because each
uses a fresh walk and fresh conditional offsets. We apply concentration to
the independent **ideal** samples, then couple the implementation to those
samples. No independent-sample claim is made about the outer correlated chain.

### Hoeffding, with its actual constant

For an observable in $[a,b]$, mean $\mu\ge a>0$, Hoeffding
gives

$$
 \Pr(|\overline X-\mu|>\sigma\mu)
 \le2\exp\left[-N\sigma^2/C_H\right],
 \quad C_H=\frac{(b-a)^2}{2a^2}.
$$

Thus $C_H=961/2$ for the correction and $C_H=1/2$ for a
ratio. The initial review's coefficient 1024 was sufficient but loose.

### Bernstein, using the mean-dependent variance

Since $(X-a)(b-X)\ge0$,

$$
 \operatorname{Var}X\le(b-\mu)(\mu-a),\qquad
 \frac{\operatorname{Var}X}{\mu^2}
 \le\frac{(b-a)^2}{4ab}.
 \tag{12}
$$

The second inequality follows by completing a square in $1/\mu$,
or multiplying through by $4ab\mu^2$. For the correction its
right side is $961/128$. It is attained by an endpoint distribution
with probability $1/33$ at 4 and $32/33$ at $1/8$, so
this universal relative-variance bound cannot be decreased.

For completeness, the needed Bernstein inequality follows from a short mgf
argument. If $\mathbb EY=0$, $|Y|\le L$, and
$\mathbb EY^2\le v$, then for $0\le\lambda L<3$,

$$
 \mathbb E e^{\lambda Y}
 \le1+\frac{v\lambda^2}{2(1-\lambda L/3)}
 \le\exp\left[\frac{v\lambda^2}{2(1-\lambda L/3)}\right].
$$

Expand the exponential, use
$\mathbb E|Y|^j\le vL^{j-2}$, and
$j!\ge2\cdot3^{j-2}$ for $j\ge2$. Independence multiplies
mgfs. If $v=0$, the variable is deterministic and the tail bound is
immediate. For $v>0$, applying Markov's inequality with
$\lambda=t/(v+Lt/3)$, then repeating for $-Y$, gives

$$
 \Pr(|\overline Y|>t)
 \le2\exp\left[-\frac{Nt^2}{2v+(2/3)Lt}\right].
 \tag{13}
$$

For $Y=(X-\mu)/\mu$, (12) applies and
$|Y|\le(b-a)/a$. Consequently the correction and ratio denominators
in (13) are bounded by

$$
 C_T=\frac{961}{64}+\frac{62}{3}\sigma<16,
 \qquad C_R=\frac14+\frac23\sigma.
 \tag{14}
$$

This is a further improvement over merely replacing Chebyshev with Hoeffding.
It uses neither an estimated variance nor a distributional approximation.

### Separate counts for the different observable ranges

Set

$$
 L_\theta=\left\lceil\log_2\frac{8(H+1)}\theta\right\rceil,
 \quad
 N_T=\left\lceil qC_TL_\theta/\sigma^2\right\rceil,
 \quad
 N_R=\left\lceil qC_RL_\theta/\sigma^2\right\rceil.
 \tag{15}
$$

Each ideal empirical mean fails its relative tolerance with probability at
most $2\,2^{-L_\theta}$; the union over at most $H+1$
means is at most $\theta/4$. A common count $N_T$ remains
available. The default gives the narrower ratio range fewer samples, about
60 times fewer as $\sigma\to0$.

There are at most $HN_R$ ratio-bin draws, $N_T$ correction-bin
draws, and $dN_T$ scalar correction offsets. Thus the sufficient
total draw count is

$$
 Q=HN_R+(d+1)N_T.
 \tag{16}
$$

Ratio averages need no offsets. This avoids the source's overcount
$(d+1)(H+1)N$. Give each bin and scalar-offset draw TV error at most
$\theta/(8Q)$; their combined coupling discrepancy is at most
$\theta/8$. Deterministic correction rounding retains its allocated
pointwise relative error $\sigma$. The source's product-error bound,
feasibility handling, positivity, and unconditional output range then still
apply. Total exceptional probability is at most $3\theta/8<\theta$.

### Shorter bin walks

The bounded paper's conductance proof gives
$\kappa\ge1/(1024d^2B)$ before weakening to
$1/(10^4d^2B)$. Its inverse-gap allowance can therefore be
$K_{\rm bin}=2(1024d^2B)^2$, a factor approximately 95.37 smaller.
Also $\pi_{a,\min}^{-1}\le2^HB^e$, $e\le d$, so use

$$
 s=H+d\lceil\log_2B\rceil,
 \quad \ell=\left\lceil\log_2\frac{8Q}\theta\right\rceil,
 \quad t=\left\lceil qK_{\rm bin}(s/2+\ell-1)\right\rceil.
 \tag{17}
$$

This retains the source's actual logarithmic mass bound rather than
$H+dB$, as well as the stronger spectral prefactor. The new inner
sample and walk counts have logarithmic dependence on $1/\theta$,
while retaining polynomial dependence on accuracy and the other parameters.
No claim is made that the complete outer FPRAS gains this dependence without
its call schedule and failure allocation being audited as well.

For the report's abstract oracle tuple $d=19,B=1000,H=100$,
$\xi=10^{-3},\theta=10^{-6}$, relative to the initial review:

| Allowance | Reduction factor |
|---|---:|
| Samples in the final correction average | about 97.42 |
| Samples in each ratio average | about 5,851.43 |
| Upper bound on all bin/offset draws | about 9,083.48 |
| Upper bound on all bin transitions | about 42.9 million |

This tuple is a conditional schedule illustration, not the scales of a
particular feasible input or a benchmark of a running counting implementation.
It must not be presented as a practical speedup.

## 6. Changed-law and machine-level obligations

The tabulator must calculate the law of the **actual revised program**. The
same finite-state propagation design works algebraically with revised counts:
cache each dense output law; propagate the implemented small-state kernel;
apply terminal unpadding and first-success/fallback maps. Include deterministic
empty and singleton blocks, ignored random bits, shorter successful runs,
dyadic offsets, all rejected proposals, and both fallback masses.

For example, with $q_B=\lceil\log_2(8d)\rceil$, one acceptance
bit, scalar widths at most $2^b$, and (7), a common denominator allowance
is

$$
\begin{aligned}
 Q_0&=q_B+1,& r_{\max}&=\max\{0,b+\ell_D-2\},\\
 R_1&=H_DQ_0+dr_{\max},& R_D&=J_DR_1,\\
 R_T&=T(R_D+q_s)+R_D,& R&=JR_T,
 \qquad q_s=\lceil\log_2(32d^2)\rceil.
\end{aligned}
\tag{18}
$$

`dyadic_denominator_budget` computes these allowances. It does not compute the
numerators of the revised full sampler. Padding shorter paths with unread
independent bits preserves their law; replacing that law with old cached
numerators does not. The enumerated spaces remain independent of requested
accuracy in the source construction, but all integer-length, loop-count, and
machine-realization bounds still need to be carried through for an integrated
implementation. In particular, passing arithmetic tests here does not update
the upstream compiled sampler or its Lean theorems.

## Deferred follow-up: spend more of the product-error budget

This checkpoint deliberately retains the source's $\sigma$. A reviewed
next step is $\sigma=\xi/[(H+2)(1+\xi)]<1/10$. If at most
$n\le H+2$ multiplicative factors each lie in
$[1-\sigma,1+\sigma]$, Bernoulli's inequality and the geometric
series give
$(1-\sigma)^n\ge1-n\sigma\ge1-\xi$ and
$(1+\sigma)^n\le1/(1-n\sigma)\le1+\xi$.
The source's rounding estimates also remain valid in this range. Integrating
and testing that policy is deferred. In particular, the displayed common
Bernstein bound $C_T<16$ would no longer hold throughout the larger
range; retain its exact rational formula (or the safe constant 18).

[sampling]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/algorithms.tex
[dense]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/build/sections/dense.tex
[counting]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/evaluation.tex
[exact-lean]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactSamplingParameters.lean
