# One width power removed by retaining the correction stencil

11 October 2026. Reviewed mathematical assembly, with [compiled local transport,
hard-limit and scalar components](../research/retained-root/). Retaining the
negative correction terms removes one width power: the rational defect-chain
inverse-gap allowance becomes `32p⁴V³`. Combining it with [constant padding](constant-padding.md)
gives **`42592d¹⁰` for arbitrary rectangular shapes**, under the conditions below.
The complete global physical gap theorem has not been compiled. Reviews used
separate AI agents; no outside human review or novelty claim is made.

## Abstract path lemma

Let z_0,...,z_N be positive unimodal weights, N>=1. Let c_0,...,c_(N+1) be
nonnegative, and assume `c_l <= K max(z_(l-1),z_l)` for 1<=l<=N, K>=0.
The endpoint terms c0,c_(N+1) need NO such bound. Define

`Xi_l=1/z_(l-1)+1/z_l +2c_l/(z_(l-1)z_l)`
`     -c_(l-1)/z_(l-1)^2-c_(l+1)/z_l^2`.

Assume Xi_l>=0 and that an observable h and nonnegative energies E_l satisfy
`(h_(l-1)-h_l)^2 <= Xi_l E_l`. Then its unnormalized weighted variance satisfies

`Var_z(h) <= [N(N+1)+2KN] sum_(l=1)^N E_l`.

### Resistance reduction

Choose a mode m, so z is nondecreasing on 0,...,m and nonincreasing on m,...,N.
The source no-valley property already implies this monotonicity: for i<j<=m,
z_j>=min(z_i,z_m)=z_i, and symmetrically to the right.

Put `R(i,m)=sum_(edges between i,m) Xi_l`. Weighted Cauchy--Schwarz gives
`(h_i-h_m)^2 <= R(i,m) sum_(edges between i,m) E_l`.
One can prove this directly without divisions by Xi: telescope h_i-h_m, bound
each increment by sqrt(Xi_l E_l), then use finite Cauchy--Schwarz. Thus zero Xi
causes no exceptional case. Centering at h_m bounds weighted variance above by
the sum over i of z_i(h_i-h_m)^2. An edge on the left has coefficient at most

`Gamma_L=sum_(i=0)^(m-1) z_i R(i,m)`
`       =sum_(l=1)^m S_l Xi_l`, `S_l=sum_(i=0)^(l-1) z_i`.

The maximum is attained at the edge incident to m, because Xi_l>=0 and adding
outward starting vertices adds nonnegative terms. The corresponding right-side
coefficient is Gamma_R, obtained by reversing the path. It suffices to bound
these two numbers. If m=0 there is no left side; if m=N there is no right side.

### Summation by parts on the increasing side

The base term obeys

`sum_(l=1)^m S_l(1/z_(l-1)+1/z_l) <=sum_(l=1)^m 2l=m(m+1)`.

Indeed each weight in S_l is at most z_(l-1)<=z_l.

Collect the coefficients of c_j in the correction part. The two exterior
terms c0 and c_(m+1) have nonpositive coefficients and can be discarded.
For 1<=j<=m-1, abbreviate `a=z_(j-1),b=z_j,S=S_j`. Its exact coefficient is

`D_j=2S/(ab)-(S+b)/b²-(S-a)/a²`
`   =-S(a-b)²/(a²b²)+(b-a)/(ab)`.

Since S>=a, a<=b, and c_j>=0,

`c_j D_j <= c_j[(b-a)/(ab)-(b-a)²/(ab²)]`
`         = c_j(b-a)/b² <= K(b-a)/b <=K`.

No sign split on D_j is necessary. This bounds the m-1 interior terms by
(m-1)K.

For the anchor boundary c_m, its coefficient is

`D_m=2S_m/(ab)-(S_m-a)/a²`, `a=z_(m-1),b=z_m`.

The identity

`D_m-(S_m+a)/(ab)=(a-b)(S_m-a)/(a²b)<=0`

gives

`c_m D_m <=c_m(S_m+a)/(ab)<=K(S_m/a+1)<=K(m+1)`.

The final inequality uses S_m<=m a. For m=1 there are no interior terms, and
the same boundary proof applies. Therefore

`Gamma_L <=m(m+1)+(m-1)K+(m+1)K=m(m+1)+2Km`.

Reverse the path to obtain
`Gamma_R <=(N-m)(N-m+1)+2K(N-m)`.
Both are at most N(N+1)+2KN. This proves the lemma.

## Physical source assembly

Fix one actual row-major context and let the current pair's uniform capacity
be V. Its positive child support is an interval alpha,...,beta with diameter
N<=V. Shift the child indices to 0,...,N. Source `context_child_minimum` supplies
no-valley and hence unimodality as above.

Use the same **boxed** kernel throughout this argument. If `f=contextHard`
for this context and `Ms` is the suffix-width list, fix

`g=truncate f (bounds (fun _=>V) Ms) (V+Ms.sum)`.

For original child level l, define c_l as `correctionKernel Ms g` evaluated
at the deficient current pair `(x,q)=(l-1,l)`, retaining the entire suffix.
Equivalently it is the sum of completion weights times
`x_t(V+1-x_t)` over single-excess later-slot profiles t. All its terms are
nonnegative. Normal pairs automatically lie in `[0,V]`; a nonzero exceptional
moment forces `1<=x_t<=V`. The deficient root and one excess suffix pair have
the required total `V+Ms.sum`. Thus this boxed correction is the exact physical
moment sum. Truncation removes only exceptional endpoints whose multipliers
are zero. Define the out-of-positive-child-support c terms by the same
literal profiles; invalid removals have value 0. These exterior terms can be
positive and must not be dropped by pretending they are nonexistent.

At root display `(l,V+1-l)`, removing false/false, false/true, true/true leaves
current pairs `(x,q)=(l-2,l-1),(l-1,l),(l,l+1)` respectively. Therefore the actual
root correction matrix has entries

`B00=c_(l-1), B01=c_l, B11=c_(l+1)`.

This is the same fixed context/kernel; only the current pair changes. For
invalid double removals the corresponding boundary c is0. At a boundary of
positive CHILD support that lies inside the coordinate box, the exterior c is
its actual nonnegative value, not necessarily0.

Each exceptional later-slot type injects under source repair into one of the
two neighboring children and does not decrease completion weight. Its moment
multiplier is at most `Q_V=floor((V+1)^2/4)`. If r later slots remain, this gives

`0<=c_l<=r Q_V max(z_(l-1),z_l)`

for each positive adjacent child pair. This is the EXISTING conditional repair
argument, using the existing **boxed** `auxiliary_mass_le_adjacent`; no bound
for the exterior c terms is needed. The uniform small-capacity hypothesis
`hB` identifies the leaf edges with the graph, and the ordinary-completion cap
hypothesis `hcap` supplies this repair comparison. These global hypotheses
are not discharged merely by the local transport theorem. Put K=r Q_V.

The actual pinned `IntegerRecursivePotential.recursivePotential_bound` bounds
the recursive potential by the hole potential MINUS the FULL root correction
bilinear form. With root coefficients (1/a,-1/b), this upper bound is exactly
Xi_l. Applying the existing transport Cauchy--Schwarz and literal leaf-energy
identity therefore gives

`(mean_(l-1)-mean_l)^2 <= Xi_l E_owner(l)`.

Apply it first to the positive softened weights. The four correction entries,
the endpoint masses, and the leaf energy are finite sums with pointwise hard
limits. Positive limiting adjacent child masses keep the only denominators
continuous. Recursive potentials are nonnegative, so their finite upper bound
Xi remains nonnegative in the limit. Passing to the hard inequality needs no
convergence of currents. It is INVALID to substitute quadraticAuxiliaryKernel
while retaining negative diagonal signs; the actual correction kernel is used.

Apply the abstract path lemma directly to the context's conditional variance;
first using the old generic sum-of-owner-contrasts bound would retain its
unnecessary width-square factor. The new context coefficient is

`N(N+1)+2r N Q_V <= V(V+1)+2(p-1)VQ_V=:CT_new`.

The exact conditional-variance telescoping and unchanged display ownership
charge each physical leaf edge once, giving

`Var_transversal <=CT_new E_exchange`.

All energies use unordered physical edges once. This changes neither the graph
nor its weights, state normalizers, repair map, trace or output law.

## General gap envelope

The existing effective-width equivalence permits the same proof at uniform
V=max(2,1+max_small min(r_i,c_j)); original cutoff/padding stay in the physical
implementation. For integer V>=2, `Q_V<=V²/2`: check V=2 directly and use the
continuous maximum for V>=3. Since V(V+1)<=V³,

`6<=CT_new<=pV³`.

The existing square-root repair inequality gives

`C_full=CT_new+(p sqrt(CT_new)+1)^2<=2p²CT_new<=2p³V³`

for p>=2. One elementary envelope uses sqrt(CT_new)<=CT_new/2 (CT_new>=4),
then (p²+p+1)CT_new+1<=2p²CT_new.

Shape-aware rational normalization is `4Q_shape C_full`, with Q_shape<=4p-3;
therefore

`K_rational<=32p⁴V³`, `K_dyadic<=64p⁴V³`.

At the OLD ideal cutoff U=5d³,V<=U,p<=d, this gives

`K_rational<=4000d^13`, `K_dyadic<=8000d^13`.

## Smaller padding gives a general d¹⁰ envelope

Take ordinary equal-total natural margins with `m,n>=2`,
`d=10+(m+1)(n+1)`, and preselect **`U=11d²,L=7`**. Classify large lines at
that cutoff; no favorable block classification is assumed. If the resulting
completion rectangle has `R` rows and `C` columns, put `g=RC` and keep the
**full table's** donor count `e=(m-1)(n-1)` in the padding-growth bound.
Then `g,e<=d`, so

`47gLe <=329d² <=32(U+1)` and `U>=2L`.

The existing sequential-padding certificate gives padded/original count
ratio at most two. The new actual reference-move theorem gives half
acceptance at `L>=7`, for every nonempty completion block, with the same cap
premise. Singleton blocks use their deterministic between map; an empty
completion block uses the existing unit-chain comparison.

For a nonempty positive defect space, `p>=2`, `p<=d` and `V<=U`.
Consequently the reviewed trace bound gives

`K_rational <=32d⁴(11d²)³ =42592d¹⁰`,

`K_dyadic <=64d⁴(11d²)³ =85184d¹⁰`.

The last scalar implications are compiled as `rational_uniform_d10` and
`dyadic_uniform_d10`. A layout with no positive defect state needs a separate
direct branch; it is not assigned an artificial spectral gap. Zero margins
are allowed by the ordinary counting statements, while the current Python
joint-output terminal still requires positive margins.

The current generic completion program is proved at larger dimension-dependent
floors, so it cannot simply be called at `L=7`. Blocks up to 2×2 have the
separate bounded small-completion provider. A suitable general completion
backend, the full global physical Lean assembly, complete outer schedule,
and encoded runtime composition remain open.

## Reproduce and review

The [formal packet](../research/retained-root/) maps English claims to exact
Lean statements and saved dependency closures. [Exact rational checks](../reports/retained-root.json)
cover 3,000 abstract stencil sums (236 also satisfy nonnegative Xi) and
40 actual mixed-completion contexts:

```sh
PYTHONPATH=src python3 experiments/retained_root.py --output .local/reports/retained-root.json
```

These finite checks support the implementation and boundary cases; the
arbitrary-parameter assertion rests on the proof above. The next formal
steps are the mode-anchor summation by parts, same-box moment/repair cap,
conditional-variance telescoping and physical edge ownership, followed by
trace normalization. A human MCMC or Lean review of those interfaces would
be especially useful.
