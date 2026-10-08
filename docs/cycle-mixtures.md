# Certified mixtures of cycle heat baths

Choosing cycle probabilities carefully improves the gap on our 42-table synthetic commuting example. This improves a **finite reference kernel**, not the asymptotic theorem in #115. The mixture probabilities are fixed by the input and target law; they never depend on the current table.

Here the conditional-worker target is the **bounded, structurally constrained, activity-weighted conditional-Poisson law** in the synthetic fixture. Its activities are not separable into row and column factors. It differs from an ordinary unbounded worker-assignment urn baseline and does not inherit that baseline's closed-form moments.

The earlier example found that uniform selection from all 24 simple cycles was worse than uniform selection from the 12 rectangles. We can now separate three effects: adding possible moves, choosing their probabilities, and the cost of executing a move.

## Exact results

The entries below are certified intervals for the Poincare spectral gap. Lower endpoints are exact terminating rationals; upper endpoints are rounded **outward** from exact rational Rayleigh quotients. They are not floating-point eigenvalue error bars.

| Fixed mixture | Uniform tables | Conditional-worker law |
|---|---:|---:|
| Equal selection of 12 rectangles | [0.103869, 0.103870233] | [0.111515, 0.111516398] |
| Tuned rectangle probabilities | [0.164036, 0.164037163] | [0.176501, 0.176502119] |
| Equal selection of all 24 cycles | [0.097826, 0.097827542] | [0.104207, 0.104208362] |
| Tuned probabilities over all 24 cycles | **[0.169974, 0.169975463]** | **[0.183580, 0.183581879]** |

The last mixture improves the gap by at least **63.6407%** for the uniform law and **64.6215%** for the conditional-worker law, relative to equal rectangle selection. Every stationary probability and transition probability used to certify this comparison is rational.

We also certify upper bounds applying to **every** fixed mixture in each candidate family:

| Candidate family | Uniform-table gap at most | Conditional-worker gap at most |
|---|---:|---:|
| All mixtures of the 12 rectangles | 0.164046118 | 0.176506534 |
| All mixtures of the 24 simple cycles | 0.169978130 | 0.183583379 |

Thus the tuned larger catalogs beat even the best rectangle-only mixture by at least **3.6135%** and **4.0074%**, respectively. Their achieved gaps are within **0.000004130** and **0.000003379** of the best possible gaps in the 24-cycle family. This is a bound on distance from the optimum, not a claim that the supplied probabilities are exact optimizers.

The report contains all cycle signs in order, all rational mixture probabilities, the target masses, integer witness vectors, and exact rational bounds. The tuned mixtures give positive probability to 20 cycles under the uniform law and 17 under the worker law. Their expected numbers of cells in the selected cycle are **4.3519** and **4.186928**, versus 4 for rectangles and 5 for equal selection from all cycles. These are descriptive operation-size proxies, not measured transition costs. Finding or sampling the feasible line, evaluating weights, and preprocessing the catalog can dominate runtime.

## What the certificate proves

Let $P$ be the exactly checked transition matrix and $\pi$ its target distribution. Restrict to the positive target support and set

$$
D=\operatorname{diag}(\pi),\qquad L=D(I-P),\qquad
C=D-\pi\pi^\mathsf{T}.
$$

For a function $f$ on the states, $f^\mathsf{T}Lf$ is the Dirichlet energy and $f^\mathsf{T}Cf$ its variance. Therefore

$$
\operatorname{gap}(P)\ge\gamma
\quad\Longleftrightarrow\quad L-\gamma C\succeq0.
$$

Both $L$ and $C$ have zero row sums. Write $A=L-\gamma C$ and subtract the last coordinate of an arbitrary vector from every coordinate. Because $A\mathbf1=0$, this does not change its quadratic form, and the resulting vector has last coordinate zero. Consequently, $A$ is positive semidefinite exactly when its last-row/last-column principal block is positive semidefinite.

[`mixtures.py`](../src/contingency115/mixtures.py) checks the block with exact symmetric fraction-free elimination. A positive common denominator converts it to an integer matrix. The Bareiss recurrence performs exact integer divisions and has the signs of successive LDL pivots. A negative pivot fails. A zero pivot is accepted only if its remaining row is zero, as any positive semidefinite matrix with a zero diagonal entry must have a zero corresponding row. The accepted matrix supplies the lower certificate; no eigenvalue tolerance is involved.

For an integer witness vector $f$ of positive variance, the rational Rayleigh quotient

$$
R(P,f)=\frac{f^\mathsf{T}D(I-P)f}{\operatorname{Var}_\pi(f)}
$$

is an upper bound on the gap. This gives the other endpoint of each interval.

For the family-wide upper bound, let $P_i$ be the available conditional heat baths, and choose rational witness probabilities $a_j$ and rational vectors $f_j$. For every state-independent mixture $P_w=\sum_i w_iP_i$,

$$
\operatorname{gap}(P_w)
\le\sum_j a_jR(P_w,f_j)
=\sum_iw_i\sum_ja_jR(P_i,f_j)
\le\max_i\sum_ja_jR(P_i,f_j).
$$

Every quantity on the right is computed exactly. The witness can be found numerically without making the resulting bound a numerical approximation. These dual witnesses apply only to mixtures of the specified components, not to every possible Markov kernel on this state space.

A conditional heat bath is a self-adjoint orthogonal projection in $L^2(\pi)$. Its spectrum is nonnegative, as is that of a convex mixture. Thus the algebraic gap here also controls absolute spectral relaxation. The reusable checker permits other reversible kernels; for those, its algebraic-gap certificate alone says nothing about a negative eigenvalue near $-1$. A unit test makes this distinction explicit with a periodic two-state chain of algebraic gap 2.

## Search and reproduction

The numerical search uses a smoothed minimum-eigenvalue objective, projected ascent on the probability simplex, and a decreasing smoothing parameter. Probabilities are then rounded to a common denominator of one million while preserving an exact sum of one. Search directions provide integer Rayleigh witnesses and a rational combination of witnesses for the family upper bound. Search traces and float64 gap diagnostics are labeled separately in the JSON.

Fastest-mixing optimization is established work. Boyd, Diaconis, and Xiao formulate fastest-mixing chains as convex and semidefinite optimization problems, including prescribed stationary distributions: [*Fastest Mixing Markov Chain on a Graph*, SIAM Review 46(4), 667–689 (2004)](https://web.stanford.edu/~boyd/papers/pdf/fmmc.pdf). Here the feasible set is the smaller convex hull of input-fixed conditional heat baths. We claim an exact, reproducible application to this fixture, not a new optimization principle.

From the repository root, generate the report with the optional NumPy research dependency installed:

```sh
OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  PYTHONPATH=src python3 experiments/cycle_mixtures.py
```

Replay the saved rational certificate with only the standard library:

```sh
PYTHONPATH=src python3 -S experiments/cycle_mixtures.py \
  --replay reports/cycle-mixtures.json
PYTHONPATH=src python3 -m unittest discover -s tests -p test_mixtures.py -v
```

The replay reconstructs the complete fiber and each component kernel, verifies source/input hashes and state order, then checks **8 gap intervals, 4 family-wide upper bounds, and 6 strict comparisons**. Floating-point search traces are not relied on by the verifier. A search on a different numerical backend may propose different rational probabilities; the exact certificates, rather than bit-for-bit search reproduction, decide whether they work. [`cycle-mixtures.json`](../reports/cycle-mixtures.json) is the complete saved certificate.

The tests independently compare the PSD checker against all principal minors of all **729** symmetric $3\times3$ matrices with entries in $\{-1,0,1\}$. They also cover rational singular matrices, a 201-bit cancellation, zero-mass states, periodic and disconnected chains, malformed probabilities, a sharp two-state gap, and a three-component family whose exact optimum is $1/2$.

## Use for CBEI/LEHD

This supplies a way to test candidate move-selection rules on small, fully specified commuting tables before considering a larger sampler. The exact target law stays fixed during optimization, so a better gap does not change expected VMT or make either target law empirically correct. The two optimized mixtures differ because the stationary laws differ.

The experiment enumerates the full fiber and all simple cycles and constructs dense matrices. Those steps can be exponential, and exact arithmetic can grow large even for a modest state count. The certificate API caps matrix dimension; it does not cap integer bit lengths, elapsed time, or memory. There is no large-instance rapid-mixing guarantee, Lean proof of this implementation, calibrated travel result, or end-to-end runtime benchmark in this result.

This research and implementation were produced with AI assistance and remain open to independent review.
