# Sequential padding using the reciprocal zero-cell bound

11 October 2026. Independently reviewed mathematics by separate AI agents,
with compiled scalar lemmas and exact count checks. This improves the
preselected cutoff for bounded-aspect rectangles and gives an exact
obstruction to a subquadratic cutoff for unrestricted thin shapes.

## 1. Exact one-increment count comparison

Let m,n>=2, with unrestricted nonnegative integer margins r,c of equal
total. Write N(r,c) for the ordinary UNIFORM table count. Increment r_i
and c_j by one, obtaining target margins r',c'. Put a=r_i+1, b=c_j+1.
Adding one to cell ij bijects the old tables with target tables whose
marked cell is positive. Every target fiber is nonempty by equal totals.

The compiled `Research.ReciprocalZero.zero_entry_probability_reciprocal`
has alpha=(n-1)/(a+n-1), beta=(m-1)/(b+m-1), and yields

    Pr_target(X_ij>=1) >= (1-alpha)(1-beta)
                         = ab/[(a+n-1)(b+m-1)].

Thus the exact natural-count inequality is

    N(r',c') (r_i+1)(c_j+1)
       <= N(r,c) (r_i+n)(c_j+m).                    (1)

Dimension orientation is important: n-1 goes with the ROW margin and
m-1 with the COLUMN margin. This uses the product correction in the
reciprocal zero-cell theorem. Dropping it gives a weaker survival bound
and does not prove this multiplicative one-increment formula.

The subtract-one bijection and source counts are the existing
SmallEntryTail.shifted_card / small_card_add_survival identities used in
Math115.PaddingGrowth.one_unit_count_growth. Replacing its zero-entry
bound is the new physical counting bridge; this bridge has an English
proof and exact finite checks here, not a newly compiled Lean theorem.

## 2. All successive increments and exact incident-margin products

Choose cutoff U BEFORE classifying the input. Let R,C be its actual large
row/column counts. Pad every cell of the R-by-C large rectangle by L>=0
units. There are q=RC L increments. Every marked cell has ORIGINAL
incident margins at least U. Earlier increments only raise those margins.

At the kth increment incident to a particular row i, the first factor in
(1) is 1+(n-1)/(r_i+k). Every large row receives exactly CL increments.
Every large column receives exactly RL increments. Consequently, regardless
of the order of the marked-cell increments,

    P/N <= product_(large row i) product_(k=1..CL)
                 [1+(n-1)/(r_i+k)]
           * product_(large column j) product_(k=1..RL)
                 [1+(m-1)/(c_j+k)].                (2)

P and N are padded and original ORDINARY table counts. This retains all
increments, including singleton blocks. Empty blocks have q=0 and P=N.
The product in (2) can be evaluated by binomial ratios:

    product_(k=1..h) [1+a/(u+k)]
      = binom(u+h+a,a)/binom(u+a,a).

This supplies an instance certificate when actual marked margins are
large, but the following frozen-floor consequence suffices uniformly.

Put H=U+1>0, s=m+n-2. Since r_i,c_j>=U, (2) gives

    P/N <= [(H+n-1)(H+m-1)/H^2]^q.

The elementary AMGM polynomial identity gives

    4(H+n-1)(H+m-1) <= (2H+s)^2,

with difference (m-n)^2. Therefore

    P (2H)^(2q) <= N (2H+s)^(2q).                 (3)

Apply the already compiled PaddingGrowthAlgebra.count_le_twice_of_growth
with exponent 2q, denominator 2H (its formal U parameter is 2H-1), and
increment parameter s. Its hypothesis is

    47*(2q)*s <=32*(2H), equivalently 47qs<=32H.    (4)

It follows that P<=2N, including q=0. The formal parameter U'=2H-1 here
is only a scalar denominator; it is not a replacement physical cutoff.

The old donor-pair comparison remains independently valid with
e=(m-1)(n-1). Hence a sufficient checked cutoff for a prescribed block is

    U=max(2,2L,ceil(47 RC L min(e,s)/32)-1).        (5)

For min(e,s)=e use the old source growth theorem. For min(e,s)=s use
(1)-(4). This is not a claim that the old donor-pair theorem itself has
a smaller donor count. Classification must still be checked at this U;
classifying at an earlier cutoff and assuming persistence is invalid.

## 3. Preselected shape cutoff and inverse-gap consequence

Take d=10+(m+1)(n+1), U=11d s, L=7. This is chosen using only outer shape,
then the actual R,C are classified. Since RC<=mn<=d,

    47qs=47*7*RC*s <=329ds <352ds+32=32(U+1).

Thus (4) holds. Also U>=14, so the existing conservative width/padding
guard is retained. Constant-padding actual directed acceptance at L=7
applies to every nonempty completion block, with its unchanged source-cap
premise. The paper cap M+dL+U+2 still exceeds every physical residual
total M+RC L, so no restrictive completion law is introduced. Singleton
and empty completion blocks retain their existing branches.

For a nonempty positive defect space, the [quadratic-width argument](retained-root-spectrum.md)
gives `K_rational≤32p⁴V²`, with `p≤d,V≤U`. Thus

```
K_rational ≤ 3872 d⁶s²,     K_dyadic ≤ 7744 d⁶s².
```

If `s²≤A d` for a fixed aspect class, this is `3872A d⁷` rational and
`7744A d⁷` dyadic. Square tables can take `A=4`; the claim also covers
any fixed non-square aspect ratio. For arbitrary `m,n≥2`,

```
d−3s=(m−2)(n−2)+13≥13,
```

so the rounded general allowances `431d⁸` and `862d⁸` follow. The simpler
`3872d⁸` / `7744d⁸` envelopes use only `s≤d`.

The full physical gap theorem remains reviewed mathematics. The compiled
scalar statements do not assume or prove the missing global assembly. The
[frozen complete sampler](legacy-completion-backend.md) supplies mathematical
completion availability at `L=7`; the new adapter, call schedule and encoded
composition remain open. Zero margins are allowed by the count bounds;
the current joint-output terminal retains positive margins. No gap is
assigned to an empty defect space.

## 4. Exact thin obstruction to a general subquadratic cutoff

Fix N>=3,U>=2,L>=1. Let T=2U+NL. Consider an N-by-3 input with

    rows=(T,...,T), columns=(U-1,U,NT-2U+1).

Precisely its first column is small at cutoff U; all N rows and the other
two columns are large. Thus p=N and g=2N. Put D(t,N)=binom(t+N-1,N-1).
Choose entries x_i,y_i in the first two columns as weak compositions of
U-1 and U. Their sum in ANY row is at most 2U-1<T, so the third entry
T-x_i-y_i is automatically nonnegative. Its column total is automatically
correct. Hence the exact original table count is

    N_original=D(U-1,N)D(U,N).

After padding the N-by-2 large rectangle by L, rows are T+2L, and the
first two column totals are U-1 and U+NL. Their combined total is
2U+NL-1<T+2L, so again every pair of weak compositions gives an actual
padded table. Therefore

    P=D(U-1,N)D(U+NL,N),
    P/N_original=product_(k=1..N-1) [1+NL/(U+k)].   (8)

Each factor is at least 1+NL/(U+N-1). The finite binomial/Bernoulli
inequality, applied to these nonnegative factors, proves

    P/N_original >=1+(N-1)NL/(U+N-1).             (9)

Consequently P<=2N_original REQUIRES

    U >= (N-1)(NL-1).                            (10)

This is an explicit necessary bound for every N,U,L in this family,
not a conclusion inferred from seven finite examples. For fixed L>=1,
its right side grows quadratically in N. Since d=4N+14, no preselected
cutoff o(d^2) can keep P/N<=2 uniformly on this unrestricted thin family.
Here V=U,p=Theta(d),g=Theta(d), and Q_shape=Theta(p); using the uniform
quadratic-width envelope alone therefore retains the d8 power.

These dense completion weights happen to be constant, but the completion
rectangle is nonempty and the physical graph is the GENERAL branch. A
defect with positive donor views has degree 4N-6, and fully positive small
profiles attain quadratic designated-repair load when U-1>=N. Constant
completion weights do not identify this graph with the empty-rectangle
unit graph. Nevertheless (10) is a count-growth obstruction, not a lower
bound on the actual chain inverse gap or on every possible sampler.

A supplementary genuinely weighted family uses rows all U with columns
(U-1,U,(N-2)U+1). Its row-cap constraints are real. Independent composition
tail bounds in the reproducer lower-bound its true padded count; they also show
large ratios at U=N^(3/2). This supplementary family is not needed for
the exact universal-cutoff obstruction (8)-(10).

## Evidence and compiled scope

The [exact reproducer](../experiments/reciprocal_padding_growth.py) checks
one-increment counts including zero margins, normalized zero probabilities,
complete padding paths including empty blocks, shape budgets, independent DP
counts for the thin family, and larger rational certificates. The
[saved report](../reports/reciprocal-padding-growth.json) records the exact
quantities and verification scope. Floats are display values only.

```sh
PYTHONPATH=src python3 experiments/reciprocal_padding_growth.py \
  --output .local/reports/reciprocal-padding-growth.json
```

[`GrowthScalar.lean`](../research/retained-root/formal/Research/GrowthScalar.lean)
compiles the AM–GM reduction, conversion of the doubled-power count bound
to a factor of two, cutoff budget, and shape-dependent scalar consequences.
The [packet receipt](../research/retained-root/) has the exact statement and
hypothesis map. The reciprocal-zero/subtract-one count bridge and successive
marked-cell assembly are proved above but not newly compiled as a complete
physical counting theorem. The earlier width-cubic scalar consequences remain
valid and retain their names.
