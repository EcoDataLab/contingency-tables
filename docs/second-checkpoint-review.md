# Independent review of the second #115 refinements

Review date: 8 October 2026. Upstream is pinned to
openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
This continues the [first review](independent-review.md), with particular
attention to the actual ordinary-table, physical-energy, and oracle interfaces.
It separates mathematical deductions from the status of their Lean integration.

The strongest new ordinary-table result is a sharp lower bound on the whole
survival distribution of a marked entry. It strengthens the earlier threshold
bound and implies a sharp lower bound on its mean. The schedule changes also
survive review against the source's correction arithmetic. The full
$O(d^{25})$ ideal-chain inverse-gap bound still requires the transport and repair
integration described below; it is not a running-time claim for a complete
sampler.

## 1. A sharp survival bound for an ordinary table entry

Let $X$ be uniform on the nonempty set of all nonnegative integer
$m\times n$ tables with fixed margins. Fix an entry $X_{ij}$ whose row and
column margins are at least an integer $a\ge1$, and put
$e=(m-1)(n-1)$. For $1\le t\le a$,

$$
 \boxed{\Pr(X_{ij}\ge t)\ \ge
 \prod_{k=0}^{t-1}\frac{a-k}{a+e-k}
 =\frac{\binom{a+e-t}{e}}{\binom{a+e}{e}}.}
 \tag{1}
$$

Consequently,

$$
 \boxed{\Pr(X_{ij}<t)\le
 1-\prod_{k=0}^{t-1}\frac{a-k}{a+e-k}
 \le\frac{te}{a+e},\qquad
 \mathbb E X_{ij}\ge\frac{a}{e+1}.}
 \tag{2}
$$

These are ordinary uniform-table statements. Cell caps, structural zeros,
and arbitrary weights do not satisfy the switching or shift hypotheses.
For example, forbidding the marked entry in an otherwise feasible $2\times2$
table with positive equal margins makes its zero probability one, contradicting
these bounds if they are applied outside their domain.

### Conditioning preserves exactly the required table model

Condition on $X_{ij}\ge k$. Subtracting $k$ from this single entry is a
bijection onto the ordinary table fiber obtained by decreasing its row and
column margins by $k$. It preserves the uniform law. The new incident
margins are at least $a-k$.

The refined all-donor switching lemma at threshold one gives

$$
 \Pr(X_{ij}=k\mid X_{ij}\ge k)
 \le\frac{e}{a-k+e},\qquad 0\le k<a.
 \tag{3}
$$

Multiplying the complementary conditional probabilities proves (1). One
can avoid conditional probabilities and possible empty-fiber concerns entirely.
Write $F_k$ for the number of original tables with $X_{ij}\ge k$.
The shift bijection and the zero-entry cardinal inequality give

$$
 (a-k+e)(F_k-F_{k+1})\le eF_k,
 \quad\text{hence}\quad
 (a-k+e)F_{k+1}\ge(a-k)F_k.
 \tag{4}
$$

This statement remains meaningful for empty fibers. For $k<a$, its positive
factor $a-k$ also shows that $F_k>0$ implies $F_{k+1}>0$. Starting with
$F_0>0$ permits division only where justified.

### Simplifying the product without a loose union bound

Put $N=a+e$ and $R_t=\prod_{k=0}^{t-1}(a-k)/(N-k)$.
If $e=0$, every factor equals one, and a singleton row or column forces
$X_{ij}\ge a$. For $e\ge1$, induction gives $R_t\ge1-et/N$.
Indeed, the multiplier $(a-t)/(N-t)$ is nonnegative for $0\le t<a$, and

$$
 \left(1-\frac{et}{N}\right)\frac{a-t}{N-t}
 -\left(1-\frac{e(t+1)}{N}\right)
 =\frac{et(e-1)}{N(N-t)}\ge0.
 \tag{5}
$$

This argument also works when the linear lower bound is negative. It proves
the second inequality in (2), whose denominator $a+e$ is stronger than the
earlier $a-t+1+e$. The product bound stays within $[0,1]$ even when the
unclipped linear expression exceeds one.

For the mean, the nonnegative integer tail identity and (1) give

$$
 \mathbb E X_{ij}
 \ge\sum_{t=1}^{a}\frac{\binom{a+e-t}{e}}{\binom{a+e}{e}}
 =\frac{\binom{a+e}{e+1}}{\binom{a+e}{e}}
 =\frac{a}{e+1}.
 \tag{6}
$$

The middle identity follows by summing Pascal's identity over successive
upper indices. It also covers $e=0$; the mean statement trivially extends
to $a=0$.

### Sharpness and its precise meaning

For any integers $a\ge1$ and $e\ge1$, take a $2\times(e+1)$ table with
row margins $(a,ea)$ and every column margin equal to $a$. Its first row is
uniform over all weak compositions of $a$ into $e+1$ parts: each part is
automatically at most $a$, and the second row is then determined.

There are $\binom{a+e}{e}$ tables, of which
$\binom{a+e-t}{e}$ have a specified first-row entry at least $t$. Thus
equality holds in the whole survival bound and in the mean bound. For
$e=1$, equality also holds in the linear tail bound at every threshold.
This proves sharpness among statements using only $a$ and $e$ over all
table shapes. It does not assert sharpness for each separately fixed shape.

In particular, (1) is a stochastic comparison with that weak-composition
coordinate, not merely a bound at one threshold. Beyond $t=a$, the
comparison distribution has zero survival probability, so the comparison
continues trivially.

## 2. Applying the bound to the actual padded fiber

The marked cells are padded by $L$ themselves. Therefore, if their original
incident margins are at least $U$, both incident margins in the enlarged
ordinary table fiber are at least $U+L$. Apply the switching bound there,
not in a conditional large-block completion fiber whose residual margins
could be smaller.

The earlier simple switching inequality at $a=U+L,t=L$ gives failure at
most $Le/(U+1)$ for each marked cell. For $g$ marked cells, a union bound
gives

$$
 \Pr(\text{unpadding fails})\le\frac{gLe}{U+1}.
 \tag{7}
$$

As $g,e\le d$, the scales

$$
 A=16d^2,\quad B=16d^3,\quad L=32d^3,\quad U=64d^5
 \tag{8}
$$

ensure failure below one half. The old sufficient denominator $U-L+1$
does not justify (8); using it would be a genuine hypothesis error. The new
code correctly separates the enlarged-margin conditions from that older
certificate and connects (7) to upstream large padding and ordinary tables.

The linear bound in (2) gives the further improvement

$$
 \Pr(\text{unpadding fails})\le\frac{gLe}{U+L+e}.
 \tag{9}
$$

For known dimensions, $g\le mn$ gives the explicit sufficient choice

$$
 U=\max\{2L,\,2Lmn(m-1)(n-1)-L-(m-1)(n-1)\}.
 \tag{10}
$$

Using the full dimension bound avoids a circular definition in which $U$
depends on the number of cells classified as large by that same $U$.
For singleton dimensions $e=0$, the table is deterministic and (10) chooses
$U=2L$. The scale helper is a certificate, not a reason to sample that case.

Replacing $128d^5$ by $64d^5$ decreases the leading $U^4$ gap allowance
by a factor tending to 16. It leaves the exponent 25 unchanged and does
not imply a measured sixteenfold speedup.

### An obstruction to lowering this threshold's order

The independently reviewed construction in [padding-barrier.md](padding-barrier.md)
uses ordinary $2\times n$ margins $(U,(n-1)U)$ with all column margins $U$.
After padding every cell by $L$, its success probability satisfies

$$
 \Pr(\text{unpadding succeeds})
 \le\frac{U+1}{U+1+Ln(n-1)}.
 \tag{11}
$$

To check the counting argument, write the first row as $y$ with total
$U+nL$ and coordinate upper bound $U+2L$. Success is equivalent to
$y=L+z$ with $z\ge0$ and $\sum z=U$. From each success, choose
$j\ne k$ and $h\in\{0,\ldots,L-1\}$, and move $y_j-h$ from $j$ to $k$.
The target is feasible and has exactly one first-row coordinate below $L$,
so it determines $j,h$. Each source has $Ln(n-1)$ outgoing labels.

For a fixed target and recipient $k$, the number of inverse moves is
$(Y_k-2L+h+1)_+$. With $a_k=Y_k-L\ge0$ for $k\ne j$ and
$b=L-h-1\ge0$, one has $\sum a_k=U+b+1$. If any positive inverse term
exists, $\sum(a_k-b)_+\le\sum a_k-b=U+1$; otherwise the indegree is
zero. Double counting proves (11). Additional second-row failures at the
target do not interfere with recovering its unique deficient first-row cell.
For $n=2$, there are exactly $U+1$ successes and $2L$ failures, so (11)
is an equality.

Any fixed positive lower bound on success therefore requires
$U=\Omega(Ln^2)$. Since the source dimension is $d=3n+13$ on this family
and the present dense construction uses $L=\Theta(d^3)$, the threshold
order $d^5$ cannot be decreased merely by sharpening the rejection estimate
for this same padding construction. This is not a lower bound on the
spectral gap itself, on other padding methods, or on sampler running time.

The associated exact counting implementation was also reviewed. Its
inclusion-exclusion sum has the correct cap-exceedance shift $U+2L+1$,
and its preflight guards bound the number of terms, binomial lower arguments,
and stored count/term/partial-sum bit lengths before binomial evaluation.
Those guards do not claim to bound every internal temporary in Python's
binomial implementation. Seven padding tests passed independently, including
direct incidence enumeration, the necessary-but-insufficient threshold example,
and rejection before any binomial call.

## 3. Larger oracle tolerance, sharper support, and actual annealing index

The reviewed implementation and derivation are in
[budgets.py](../src/contingency115/budgets.py) and
[error-budgets.md](error-budgets.md). For actual annealing index $0\le j\le H$
and requested relative accuracy $0<\xi<1/4$, the new policy is

$$
 \sigma=\frac{\xi}{(j+2)(1+\xi)}<\frac1{10}.
 \tag{12}
$$

There are $j+1$ ideal empirical-mean factors and one additional factor for
rounding the positive correction average. Put $r=j+2$. Then

$$
 (1-\sigma)^r\ge1-r\sigma\ge1-\xi,\qquad
 (1+\sigma)^r\le\frac1{1-r\sigma}\le1+\xi.
 \tag{13}
$$

The upper bound follows from $\binom r k\le r^k$ and the geometric series.
Independence between error factors is unnecessary. Independence within
each ideal sample average is still required by concentration; fresh walks
and fresh offsets provide it in the manuscript's ideal oracle.

The source's correction arithmetic remains valid throughout this larger
tolerance range. Its exponent lies in $[-2,2]$. Rounding to the nearest
grid with denominator the smallest power of two at least $32/\sigma$
incurs exponent error at most $\sigma/64$, hence relative exponential
error at most $\sigma/32$. Bisection of $[0,8]$ to depth
$\lceil\log_2(512/\sigma)\rceil$ has midpoint error at most
$\sigma/128$, hence another relative error at most $\sigma/32$ against
$2^\beta\ge1/4$. The total is at most $\sigma/16<\sigma$.
This also preserves the original unconditional output interval.

The old correction Bernstein constant below 16 cannot be reused blindly:
at $j=0$, as $\xi\uparrow1/4$, its exact published-support coefficient
tends to $16399/960>16$. The implementation retains the exact rational
coefficient instead.

Under the source's actual bin hypotheses, the correction support can be
improved to

$$
 \frac9{20}\le T\le\frac{10}{9}.
 \tag{14}
$$

Each bin-population factor is within $1/(100d)$ of one, and there are at
most $d$ factors; hence their product lies in $[99/100,100/99]$.
For $H>0$, the scaled penalty is $1/8$-Lipschitz and $j/H\le1$, so
$\beta=\lfloor jD(v)/H\rfloor-jD(s)/H\in[-9/8,1/8]$.
As $(11/10)^8>2$, $2^\beta\in[5/11,11/10]$, proving (14).
The $H=0$ case has $j=0$ and the source oracle returns its exact initial
mass without this division.

The resulting Bernstein denominators are

$$
 C_T=\frac{14161}{32400}+\frac{238}{243}\sigma,
 \quad C_R=\frac14+\frac23\sigma.
 \tag{15}
$$

With separate sample counts $N_T,N_R$, all coupled draws are bounded by
$Q=jN_R+(d+1)N_T$; ratios need no scalar offsets. Every bin law used at
this index has inverse minimum mass at most $2^jB^d$, giving logarithmic
allowance $j+d\lceil\log_2B\rceil$. This compares the same target at a
shorter index-specific schedule, not different annealing targets.

Numeric inputs $d,B,H$ do not prove the physical bin-population or Lipschitz
hypotheses. The support policy records that obligation explicitly. A custom
positive support is likewise a caller hypothesis. For a custom support
narrower than $[1/2,1]$, the correction count can be smaller than the ratio
count; the common-allocation path correctly takes their maximum. Constant
supports are rejected and should be treated deterministically by an integrated
oracle.

## 4. What the new Lean modules establish

The review inspected theorem statements and proof structure against the
upstream definitions. Compilation and axiom-audit receipts are maintained
by the main verification workflow; source inspection alone is not a build.

| Module | Reviewed mathematical interface | Remaining boundary |
|---|---|---|
| SmallEntrySwitching.lean | Actual upstream Table and fourCycle; all donor pairs and amounts; inverse labels; donor capacity derived from margin equations; refined cardinal and probability bounds | Uniform ordinary fibers only; shifted-fiber product is a separate theorem |
| SmallEntryTail.lean and SurvivalAlgebra.lean | Actual shift bijection, zero-entry recurrence, stronger linear and product cardinal/probability bounds, and lower mean bound | Ordinary uniform fibers; sharpness witnesses remain a separate mathematical argument |
| ScaleCertificate.lean | Quantified integer scale conditions, floor widths, density and volume inequalities; distinct old and enlarged-margin certificates | Numerical sufficient conditions do not alone prove the entire reparameterized sampler |
| PaddedMarginBridge.lean | A marked cell's own padding increases both incident margins; strong union bound on actual enlarged Table; successful unpadding bijection; concrete 64 and shape-aware success thresholds | Does not itself identify graph stationary mass or establish a gap |
| PhysicalLeafEnergy.lean | Exact image of literal leaf edges, assembly injectivity, boxed fixed-total truncation, physical support, canonical owners, global energy disjointness, boxed hard limit, and global adjacent-contrast bound | Exposure/path variance, full repair comparison, and final chain Dirichlet form remain to integrate |

The actual all-donor switching, stronger linear and product tails, entry mean,
numeric scale, padded-margin, and physical-energy modules have been reported
successfully compiled by their authors. The physical author's expanded audit
of sixteen principal statements and the scale author's final audit of twelve
targets report only propext, Classical.choice, and Quot.sound. The main
checkpoint audit covers 68 declarations, including 66 new declarations. The Lean
mean proof uses the same actual recurrence but telescopes the potential
$F_k(a-k)$ directly, then injects counted survival levels into entry units;
it does not require a formal binomial summation identity.

Several distinctions are essential in the physical module. Its local graph
is the image of literal leaf edges, not the induced graph on the union of
leaf vertices. Oriented edge sums are divided by two consistently. A shared
edge recovers the exposed cell, adjacent level, and earlier prefix; it does
not recover irrelevant future values in an arbitrary ambient assignment.
The finite owner type therefore stores only the earlier prefix and fixes a
canonical suffix enumeration. This removes genuine duplicate owner keys.

The box/total truncation identity concerns the literal local energy.
The auxiliary kernel in conditional repair must retain its source box and
fixed-total restriction. An unrestricted hard-context auxiliary sum would be
an unjustified replacement. Zero endpoint weights pose no problem for finite
energy sums. The local conditional transport theorem requires positive child
masses; the final owner-contrast theorem handles a zero child separately,
where its minimum-mass factor vanishes.

The schedule theorem has a separate formal interface issue:
the upstream CompanionOracleEstimator uses
innerTolerance(epsilon,j) = epsilon / (200*(j+1)), and its GoodEstimate
includes already rounded observed factors. Its compiled accuracy theorem
does not automatically accept (12). A new proof must connect the actual
sample blocks, target products, deterministic rounding, and cost bounds to
the revised tolerance. The manuscript-level product proof establishes the
necessary analytic estimate; it is not that interface proof.

## 5. The remaining route to an ideal inverse-gap theorem

No counterexample was found to the stated conditional $O(d^{25})$ derivation.
During this review, the physical agent's later extension closed the local
soft-to-hard bridge and actual adjacent-mean inequality. It keeps literal leaf
energy and the boxed fixed-total auxiliary kernel, assumes the two limiting
child masses positive, and permits other limiting weights to vanish. The
coefficient is $2+n(U+1)^2/2$, using the continuous quarter bound; it does
not yet replace that expression by the slightly sharper discrete floor.

The source interface still needs the following connected proof:

1. Prove the sharper path variance estimate for the actual child-mass interval
   support and connect the adjacent local quantities to the exposure variance
   decomposition, including zero-mass cases.
2. Sum the physical child energies using the canonical owner theorem, apply
   the full source repair comparison, and identify the resulting graph energy
   with the actual lazy-chain Dirichlet form at the selected scales.
3. Connect the dense numerical conditions and the actual padded-fiber
   success theorem to the revised sampler, including empty or singleton
   branches and the changed definitions of capacity and binary-length bounds.

The conditional coefficient behaves as $O(d^5U^4)$, so (8) gives
$O(d^{25})$. The padding obstruction does not prove this exponent optimal:
the $U^4$ transport/repair dependence or the construction itself may admit
further changes. Nor does this coefficient measure the cost of implementing
one ideal transition, approximate dense completion, complete output-law
tabulation, or the exact sampler's rare branch. Those remain separate
implementation and machine-cost obligations.

## 6. Ordinary worker sampling and exact linear moments

The review inspected [workers.py](../src/contingency115/workers.py), its tests,
and [worker-baseline.md](worker-baseline.md). This sampler returns the classical
conditional-independence law with mass proportional to the reciprocal product
of cell factorials. It does not sample aggregate tables uniformly. The separate
API accepts ordinary margins only, with no bounds, structural-zero mask, or
nonseparable activities. Strictly positive row-times-column activities cancel
under fixed margins, but arbitrary interactions do not.

The law proof counts label sequences assigned without replacement to row
positions. Each complete sequence has probability $\prod_j c_j!/N!$, and
exactly $\prod_i r_i!/\prod_{ij}X_{ij}!$ sequences aggregate to table $X$.
Reserving the largest row for deterministic completion merely changes the
position order; filling the sole remaining category removes choices that
cannot affect the output. The stale Fenwick tree after that shortcut is safe:
no subsequent random category selection can occur. Zero totals, one positive
row or column, and enormous deterministic margins are handled without a
numeric-worker loop.

Exactness requires each requested integer to be uniform conditional on the
previous draws, not merely marginally uniform. The author clarified this
assumption after review. Reproducible seeded experiments are implementation
checks under that mathematical random-source model, not a claim that a fixed
seed itself is a random law.

The constructor's draw allowance is conservative and is checked before any
draw or dense output allocation. It never accepts only favorable branches
that happened to fit a runtime cutoff. The limit counts integer RNG calls,
not bits, wall time, or arbitrary-size input validation. Numeric worker count
controls the general bound, so this is not a replacement for the #115
polynomial-in-binary-input theorem.

The full-covariance moment formula was independently derived from position
indicators. At a single position, the covariance between labels $j,l$ is
$(Nc_j\mathbf1_{j=l}-c_jc_l)/N^2$. At distinct positions it is the negative
of that quantity divided by $N-1$. There are $r_i\mathbf1_{i=k}$ shared
positions between rows $i,k$ and $r_ir_k-r_i\mathbf1_{i=k}$ distinct pairs.
For $N>1$, summing gives

$$
 \operatorname{Cov}(X_{ij},X_{kl})=
 \frac{(Nr_i\mathbf1_{i=k}-r_ir_k)
       (Nc_j\mathbf1_{j=l}-c_jc_l)}{N^2(N-1)}.
 \tag{16}
$$

Expanding the quadratic form in arbitrary signed rational coefficients
produces exactly the four terms used by the implementation. In particular,
row-plus-column additive coefficients have zero variance. The $N=0$ and
$N=1$ branches are deterministic and bypass both divisions. The calculation
uses $O(mn)$ rational operations without looping over workers, so huge margins
can be practical for moments while the sampling budget rejects them.

The sharp uniform-table mean bound also makes the model distinction concrete.
For ordinary $2\times2$ row and column margins both equal to $(a,M)$ with
$M\ge a$, the marked entry ranges over $0,\ldots,a$. The uniform aggregate
law gives mean $a/2$, independently of $M$, while the ordinary worker law
gives $a^2/(a+M)$. For $a=1,M=99$, the rare-row/rare-column intersection
has probability $1/2$ under the first law and $1/100$ under the second.
Both preserve the same exact controls. This is a model distinction, not
evidence that either law predicts a particular commuting population.

The note's attribution to existing software is supported by the official
[SciPy random_table documentation](https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.random_table.html)
and [R r2dtable documentation](https://stat.ethz.ch/R-manual/R-devel/library/stats/html/r2dtable.html),
checked during review. These distinguish the baseline's implementation role
from any claim to a new sampling distribution or fastest classical algorithm.

## 7. Clearing denominators in the linear optimizer

The change in [optimize.py](../src/contingency115/optimize.py) multiplies every
cost by a single positive least common multiple of its rational denominators.
Every path cost, distance comparison, equality tie, and residual negative-cycle
condition is therefore preserved. The tight-path breadth-first recovery makes
the same choices. Dividing the final integer potentials by that denominator
restores the original objective's exact dual certificate. Fixed cells and the
lower-bound shift retain their original rational objective contributions.

The independent verifier still uses the supplied original costs and checks
primal feasibility, reduced-cost signs, and exact primal/dual equality. The
shared work limit still covers residual arc examinations in both endpoint
solves, including final potential construction. Clearing denominators adds
setup and potentially large-integer work outside that counter; the public
documentation correctly excludes setup, operand size, memory, and wall time
from its meaning. The common denominator's bit length is at most the sum of
the input denominator bit lengths; this is not a constant-size integer claim.

A separate differential check loaded the previous Fraction-path implementation
and compared it to the new integer-path implementation on 300 deterministic
generated cases. These included signed coprime rational costs, 200-bit
numerators, singleton dimensions, zero margins, lower bounds, caps, infeasible
support, and deliberately small work budgets. All 244 successful results
matched in full: witness tables, endpoint values, row/column potentials,
augmentation counts, and work counters. The other 56 cases returned identical
infeasibility or budget errors. This finite check supports the algebraic
preservation argument; it does not establish a new complexity theorem.


## 8. Exact finite-instance cycle-mixture certificates

The review inspected [mixtures.py](../src/contingency115/mixtures.py), the
search/replay experiment, and [cycle-mixtures.md](cycle-mixtures.md). The
finite-dimensional argument supports the stronger comparison: on this
42-table fixture, one specified mixture including longer cycles has a gap
larger than every fixed rectangle-only mixture. The near-optimality claim
applies to the convex hull of the specified 24 heat baths.

The lower certificate checks
$A=D(I-P)-\gamma(D-\pi\pi^\mathsf T)\succeq0$ exactly. Detailed balance
makes $A$ symmetric. Positive target support is closed: if $\pi_i>0$ and
$\pi_j=0$, detailed balance forces $P_{ij}=0$. On that support, $A$ has
zero row sums, so subtracting any vector's last coordinate times the constant
vector proves equivalence to positive semidefiniteness of one principal block.
This is not an assumption that every principal minor is checked numerically.

Clearing denominators by a positive multiplier preserves positive
semidefiniteness. At each positive pivot, the symmetric Bareiss update is a
positive multiple of the ordinary Schur complement. A zero diagonal pivot
with a nonzero remaining row disproves positive semidefiniteness by a
two-coordinate quadratic form; a zero row can be removed. Retaining the
previous nonzero pivot when skipping such a row is consistent with elimination
on the remaining principal submatrix. All divisions are checked exactly.
The matrix and inputs are the certificate; pivot counts alone are only a
replay receipt.

The universal upper certificate is also valid without requiring orthogonal
witnesses. For each nonconstant rational vector $f_j$, the algebraic gap is
at most its Rayleigh quotient. A convex average of such quotients still
bounds the gap from above. The quotient is linear in $P$ when the common
stationary law and witness are fixed. Thus for any component probabilities
$w_i$ and witness probabilities $a_j$,

$$
 \operatorname{gap}\!\left(\sum_iw_iP_i\right)
 \le\sum_j a_jR\!\left(\sum_iw_iP_i,f_j\right)
 \le\max_i\sum_j a_jR(P_i,f_j).
 \tag{17}
$$

No minimax equality or numerical optimizer convergence is needed for this
upper bound. It combines with the separate exact lower certificate to prove
the strict comparison and optimality slack.

For these specific components, a heat bath is conditional expectation on
a partition into feasible cycle lines, hence an orthogonal projection in
$L^2(\pi)$. Convex mixtures have nonnegative spectrum. The algebraic gap
therefore controls absolute spectral relaxation here. For arbitrary reversible
kernels, a negative eigenvalue can obstruct mixing despite a large algebraic
gap; the periodic two-state negative control correctly prevents that broader
interpretation.

The report's weighted law includes the fixture's cell activities, bounds,
and structural zeros. It is distinct from the ordinary conditional-independence
worker baseline in Section 6. In particular, that baseline's moment formula
must not be applied to this weighted bounded law.

The reviewer independently replayed the saved report using Python with
site packages disabled: all eight gap intervals, four universal family upper
bounds, and six strict comparisons verified. All twelve displayed rounded
gap upper bounds are outward, all four stated lower percentage improvements
are conservative, and both stated optimality slack bounds exceed their exact
rational values. Ten core mixture tests also passed. After the author renamed
the receipt field to maximum_stored_entry_bits, the reviewer repeated the
standard-library replay and rejected eight independently modified reports:
inflated lower bound, constant upper witness, invalid probability sum,
forged universal bound, altered fixture hash, altered source hash, exaggerated
strict comparison, and inconsistent PSD receipt. The renamed field measures
stored matrix entries; temporary multiplication and subtraction intermediates
can be larger. That clarification does not change certificate validity.


## Verification recorded for this checkpoint

The substantive conclusions above use proofs and explicit source interfaces,
not finite experiments as substitutes for universal arguments. This reviewer
independently reran 24 budget, 12 scale, 16 worker, 18 optimizer, five
commute-scaling, ten core mixture, and seven padding tests: all 92 passed. The
stored budget-comparison report also equals a fresh call to the current
report implementation exactly. The source-specific correction tests include
actual rational bisection and bin-population calculations; the scale tests
include the sharp composition witnesses and forbidden-cell negative control.
Worker and padding report source hashes also match the current source files.
Current Lean verification receipts are maintained by the main workflow.
