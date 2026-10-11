# A quadratic-width bound from the optimal path constant

11 October 2026. Independently reviewed mathematics by separate AI agents.
The path coefficient improves from `N(N+1)+2KN` to **`N(N+1)+2K`**.
Combined with the same physical transport and constant padding, this gives
an arbitrary-aspect **d⁸ inverse-gap allowance**, and **d⁷ on bounded-aspect
rectangles**. These are inverse-gap powers, not machine-time exponents.
The complete variational theorem and full original-graph variance now compile.
The new weighted defect trace still needs Lean assembly. No human review or
novelty claim is made.

## Theorem

Let `z_0,...,z_N > 0` be unimodal, `N ≥ 1`, and `K ≥ 0`. Let all
`c_0,...,c_(N+1) ≥ 0`; for `1 ≤ l ≤ N`, assume only
`c_l ≤ K max(z_(l-1),z_l)`. Define

```
Xi_l = 1/z_(l-1) + 1/z_l + 2c_l/(z_(l-1)z_l)
       - c_(l-1)/z_(l-1)^2 - c_(l+1)/z_l^2.
```

Suppose `Xi_l ≥ 0`. If `E_l ≥ 0` and
`(h_(l-1)-h_l)^2 ≤ Xi_l E_l`, then

```
Var_z(h) ≤ [N(N+1) + 2K] Σ_(l=1)^N E_l,
Var_z(h) = Σ_i z_i (h_i - Σ_j z_j h_j / Z)^2,
Z = Σ_i z_i.
```

Thus the proposed `O(N²+K)` estimate holds under exactly the abstract input
conditions. Exterior `c` bounds and a desired Poincare hypothesis are not
required. This proof improves the optimal path constant; the old mode-anchor
certificate itself may still have order `KN`.

## 1. Positive-resistance variational problem

Fix `ε > 0` and put `r_l = Xi_l + ε > 0`. For a vector `v`, define
`Q_r(v) = Σ_l (v_(l-1)-v_l)^2/r_l`.

On the finite-dimensional subspace `Σ z_i v_i = 0`, minimize `Q_r(v)`
subject to `Σ z_i v_i² = 1`. This sphere is nonempty: since `N ≥ 1`, the vector
`(1/z_0,-1/z_1,0,...)` is nonzero and has weighted mean zero, and rescaling it
gives unit weighted norm. The constraint sphere is compact, so a minimizer
`g` exists. Its energy `λ` is positive: energy zero forces every adjacent
value equal, and weighted mean zero then forces the vector to be zero,
contradicting its unit norm.

Lagrange multipliers (or differentiating the Rayleigh quotient on the
mean-zero subspace) give, for every mean-zero test vector `v`,

```
Σ_l (g_(l-1)-g_l)(v_(l-1)-v_l)/r_l = λ Σ_i z_i g_i v_i.
```

There is no factor of two: both quadratic derivatives have that same factor.
For a general test vector, subtracting its weighted mean leaves its adjacent
differences unchanged and leaves the right side unchanged because `g` has
weighted mean zero. Therefore the displayed identity holds for all `v`.

Put `u_l = Σ_(i<l) z_i g_i`, including `u_0 = u_(N+1) = 0`.
Testing with the indicator of `{0,...,l-1}` gives the exact flux relation

```
g_(l-1)-g_l = λ r_l u_l.
```

In particular `u_l(g_(l-1)-g_l) = λ r_l u_l² ≥ 0`, with no assumption
that the minimizing eigenvector is monotone. Multiplying the flux relations
into the energy yields

```
Var_z(g) = 1 = λ Σ_l r_l u_l².
```

The minimizing property guarantees `Var_z(v) ≤ Q_r(v)/λ` for every vector
`v`, after subtracting its weighted mean. This property is proved here from
the finite variational problem; it is not an input hypothesis.

## 2. Base resistance contribution

Let `L_l = Σ_(i<l) z_i`, `R_l = Z-L_l`, and `C_l=L_l R_l/Z`.
Weighted Cauchy--Schwarz, applied to the centered indicator
`1_(i<l)-L_l/Z`, gives

```
u_l² ≤ C_l Var_z(g).
```

Choose a mode `m`. For `l ≤ m`, unimodality gives
`L_l ≤ l z_(l-1)` and `z_(l-1) ≤ z_l`; hence
`C_l(1/z_(l-1)+1/z_l) ≤ 2l`.
For `l > m`, use
`R_l ≤ (N+1-l) z_l` and `z_l ≤ z_(l-1)` to obtain the reverse bound
`≤ 2(N+1-l)`. Summing gives

```
Σ_l (1/z_(l-1)+1/z_l) u_l²
 ≤ [m(m+1)+(N-m)(N-m+1)] Var_z(g)
 ≤ N(N+1) Var_z(g).
```

Also `C_l ≤ Z/4`, so `ε Σ_l u_l² ≤ ε N Z Var_z(g)/4`.

## 3. Exact correction summation and its square identity

Collecting coefficients of each `c_l` in `Σ Xi_l u_l²` gives the exterior
terms `-c_0 u_1²/z_0²` and `-c_(N+1) u_N²/z_N²`, which are nonpositive.
For an interior index, write

```
a = z_(l-1), b = z_l, u = u_l,
x = g_(l-1), y = g_l,
u_(l-1) = u-a x, u_(l+1) = u+b y.
D_l = 2u²/(ab) - (u-a x)²/a² - (u+b y)²/b².
```

These are identities, including `l=1,N`, because the exterior prefix values
are zero. The following two algebraic identities are exact:

```
b D_l = 2u(x-y)
        - b [u(b-a)/(ab)-x]^2 - b y²,
a D_l = 2u(x-y)
        - a [u(a-b)/(ab)+y]^2 - a x².
```

Use the first when `a ≤ b` and the second when `b ≤ a`. Thus

```
max(a,b) D_l ≤ 2u(x-y).
```

The flux identity already proved ensures the right side is nonnegative.
If `D_l ≤ 0`, then `c_l D_l ≤ 0 ≤ 2K u(x-y)`. If `D_l > 0`, the given
cap on `c_l` gives `c_l D_l ≤ K max(a,b) D_l ≤ 2K u(x-y)`.
Therefore, after summing and using the flux relation,

```
Σ_l c_l D_l ≤ 2K λ Σ_l r_l u_l² = 2K Var_z(g).
```

Neither exterior term is replaced by zero; both are simply discarded in
their valid nonpositive direction. No bound on their sizes is used.

## 4. Complete estimate and the zero-resistance limit

Combining the base, correction, and `ε` terms gives

```
Σ_l r_l u_l² ≤ [N(N+1)+2K+εNZ/4] Var_z(g).
```

Since `Var_z(g)=λ Σ_l r_l u_l²` is positive,
`1/λ ≤ N(N+1)+2K+εNZ/4`.

For the original arbitrary `h,E`, the local hypotheses give
`(Δh_l)²/(Xi_l+ε) ≤ E_l`, including `Xi_l=0`, where the hypothesis forces
`Δh_l=0`. Hence the variational estimate gives

```
Var_z(h) ≤ [N(N+1)+2K+εNZ/4] Q_r(h)
         ≤ [N(N+1)+2K+εNZ/4] Σ_l E_l.
```

This holds for every `ε>0`. All other quantities are finite and fixed;
taking `ε ↓ 0` proves the claim. This handles arbitrary zero `Xi` entries
without dividing by them or assuming nonconstant admissible observables.

## Physical coefficient and shape-dependent scales

Use the same boxed context, actual correction kernel, `hB`, `hcap`,
soft-to-hard limit and owned leaf energy as in the
[retained-root assembly](retained-root-transport.md#physical-source-assembly).
For the general dimension bound, work directly at the original uniform
capacity `U`. A small cell has an original incident margin below `U`, so its
positive balanced-child support has diameter at most `U−1`. The calculation
below therefore applies with `V=U` without changing the graph or context.

For the sharper instance bound, the
[effective-width equivalence](effective-defect-width.md) reconstructs the
whole context at `V=max(2,1+max_small min(r_i,c_j))`. Its moment multiplier
changes with `V`; the old `U` kernel is not retained while substituting a
smaller moment bound. That graph and energy equivalence remains a reviewed
physical argument.
The [compiled packet](../research/retained-root/) now derives the actual
same-box correction cap from the existing auxiliary repair theorem.
For `r` later slots, set `K=r Q_V`, where `Q_V=floor((V+1)²/4)`.

Without an additional support refinement, `N≤V` gives
`CT≤V(V+1)+2(p−1)Q_V≤(5/4)pV²` for `p,V≥2`.
This already gives `40p⁴V²` rational / `80p⁴V²` dyadic.
The physical support is smaller: a positive balanced child is an actual
small cell and is at most the minimum of its original incident margins.
The original-capacity and effective-width constructions above both give
`N≤V−1`. The literal original small-line constraints remain in force under
padding. Consequently

```
CT ≤ (V−1)V + 2(p−1)Q_V ≤ pV².
```

Apply the existing repair inequality at the envelope `T=pV²≥8`:
`C_full=T+(p sqrt(T)+1)²≤2p²T≤2p³V²`.
The actual degree normalization is unchanged, so

```
K_rational ≤ 32p⁴V²,     K_dyadic ≤ 64p⁴V².
```

Positive-support restriction, conditional-variance telescoping, physical edge
ownership, repair and trace normalization must all use this same context.
The general physical Lean theorem has not yet been assembled.

For arbitrary outer shape `m,n≥2`, put `d=10+(m+1)(n+1)` and `s=m+n−2`.
The [reciprocal padding-growth proof](reciprocal-padding-growth.md) permits
preselection of `U=11ds,L=7` before classifying large rows and columns.
Apply the original-capacity result with `p≤d,V=U`:

```
K_rational ≤ 3872 d⁶s²,    K_dyadic ≤ 7744 d⁶s².
```

This is useful for non-square tables as well as square ones. Whenever
`s²≤A d` for a fixed aspect class, it gives `3872A d⁷` rational and
`7744A d⁷` dyadic. If the aspect ratio is at most a fixed `κ≥1`,
`A=κ+1/κ+2` suffices; square tables take `A=4`, and rectangles up to
2:1 take `A=9/2`.
For completely arbitrary aspect ratios, `s≤d` gives `3872d⁸` rational and
`7744d⁸` dyadic. The stronger `3s+13≤d` also gives the simple rounded
allowances `431d⁸` and `862d⁸`. Constants here follow the stated preselected
cutoff; they are not fitted to finite instances.

These statements concern the nonempty positive defect branch. A zero-variance
singleton support needs no spectral estimate. When the completion rectangle
is empty, the same boxed variance/repair argument uses unit weights and
accepted edge conductance one. Its harmonic defect trace has `E_min=E_accepted`
exactly and degree allowance `Q≤2(m+n)−3≤4p−3`, so the stated constants remain
valid (with a factor of two to spare). This uses the defect trace's new
normalization; it does not improve the separately compiled old `unitChain`
with its original step size. The unit weight/energy identities are compiled;
this new trace specialization remains part of the reviewed physical assembly.
Zero margins are permitted by the ordinary counting lemmas, while the current
Python joint-output terminal retains positive margins.

## Computation, formalization and completion availability

The proof above holds for arbitrary parameters. The supplementary
[exact rational matrix checks](../reports/retained-spectrum.json) test
regularized path Poincare inequalities, including nonzero exterior corrections
and zero resistances. They do not replace the variational proof.

The [formal packet](../research/retained-root/) now compiles the complete
abstract spectral theorem, including its attained Rayleigh minimum, prefix
covariance estimates, correction summation and zero-stencil limit. It also
compiles exact positive-support restriction, the actual boxed correction cap,
physical support bounds and scalar envelopes. The newer
[physical assembly](physical-spectral-chain.md) also compiles the actual
context, exposure/edge ownership and full repair variance, then gives a d⁹
bound for the original normalized chain at the smaller scales. The changed
defect trace still needs its actual neighbor-degree and harmonic-normalization
proofs. Historical receipts stay tied to their original sources and scopes.

The [frozen earlier complete sampler](legacy-completion-backend.md) supplies
an accurate arbitrary-margin completion law even at outer `L=7`. Its internal
padding is independent of the new outer padding. This resolves mathematical
backend availability; the new adapter, fresh-word allocation, call cap and
encoded outer integration still need implementation and verification.
Composing that backend does not establish a faster complete sampler.
