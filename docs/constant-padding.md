# Reciprocal zero-cell bound for uniform unrestricted tables

11 October 2026. The ordinary-table probability bound and its actual physical
half-acceptance specialization are [compiled in Lean](../research/constant-padding/),
with environment-derived dependency audits and separate AI-agent reviews.
No outside human review or novelty claim is made. This gives the constant
padding used in the [reviewed general d⁸ gap derivation](retained-root-spectrum.md).

Let R,C>=2, let row/column margins be nonnegative integers with equal totals,
and assume the ordinary unrestricted table fiber is nonempty. Let a be the
marked row margin and b the marked column margin. Under the uniform law,

    P(X_ij=0) <= alpha+beta-alpha*beta <= alpha+beta,
    alpha=(C-1)/(a+C-1), beta=(R-1)/(b+R-1).

The denominators are positive even when a or b is zero.

## 1. Weighted switching gives an adjacent-count inequality

Let N_t be the number of tables with marked entry t. For 0<=t<min(a,b),

    (a-t)(b-t) N_t
      <= (a-t+C-2)(b-t+R-2) N_(t+1).                 (1)

For every source X with X_ij=t and every k!=i,l!=j, perform the unit switch

    X_il -=1; X_kj -=1; X_ij +=1; X_kl +=1.

Weight this switch by X_il*X_kj. Pairs with a zero arm have zero weight and
are omitted; all other switches are feasible for unrestricted nonnegative
tables. Source total weight is exactly

    sum_(k!=i,l!=j) X_il*X_kj = (a-t)(b-t).

The map (X,k,l)->(Y,k,l) is a bijection onto target triples with Y_ij=t+1 and
Y_kl>=1: reverse the four changes. Its source weight equals
(Y_il+1)(Y_kj+1). Summing over the allowed target pairs and then bounding by
all pairs gives

    sum_(k!=i,l!=j,Y_kl>=1) (Y_il+1)(Y_kj+1)
      <= (sum_(l!=j)(Y_il+1)) (sum_(k!=i)(Y_kj+1))
       = (a-t+C-2)(b-t+R-2).

Summing over Y proves (1). This is an exact weighted double count, rather than
an assertion that arbitrary signed adjustments have equal rejection rates.
Bounded cells or structural zeros can make the forward switch invalid, so
this proof does not extend to such fibers without further work.

## 2. Lower-bound the counts by composition survival sequences

For k>=0 define

    F_k = binom(a-k+C-2,C-2) / binom(a+C-2,C-2), 0<=k<=a;
          0, k>a.
    G_k = binom(b-k+R-2,R-2) / binom(b+R-2,R-2), 0<=k<=b;
          0, k>b.

Here F_0=G_0=1. For k<a, F_(k+1)/F_k=(a-k)/(a-k+C-2);
for k<b the analogous G ratio is (b-k)/(b-k+R-2).
By induction using (1), N_k>=N_0 F_k G_k for 0<=k<=min(a,b).
Outside that range F_k G_k=0. Thus, writing S=sum_(k>=0) F_k G_k,

    sum_t N_t >= N_0 S, so P(X_ij=0)<=1/S.          (2)

This also holds if N_0=0. If a=0 or b=0, the sequences and conclusion still
work; no recurrence step or division by a-t or b-t is required.

## 3. Finite convolution bounds the reciprocal sum

The adjacent ratios of F decrease with k; include the final ratio 0 at its
support boundary. Consequently F_(i+j)<=F_i F_j for all i,j>=0. To see this
when i+j<=a, compare each ratio in the product from i to i+j-1 with the ratio
from 0 to j-1. Past the support the left side is zero, and if either right
factor vanishes, so does the left. G obeys the same inequality.

Let A=sum_i F_i and B=sum_j G_j. These are finite sums. Split their product
into i<=j and j<i:

    AB = sum_(i<=j) F_i G_j + sum_(j<i) F_i G_j
       <= sum_(i,t>=0) F_i G_i G_t
          + sum_(j>=0,t>=1) F_j G_j F_t
        = S*B + S*(A-1)
        = S*(A+B-1).                               (3)

In the first region j=i+t and G_(i+t)<=G_i G_t. In the second i=j+t,
t>=1, and F_(j+t)<=F_j F_t. Extending finite support sums adds only
nonnegative terms. The subtraction 1 is exactly F_0=1.

Hockey-stick summation gives

    A=binom(a+C-1,C-1)/binom(a+C-2,C-2)
     =(a+C-1)/(C-1)=1/alpha,
    B=(b+R-1)/(R-1)=1/beta.

A,B>=1 and S>=1. Dividing (3) by the positive product ABS and using (2)
therefore yields

    P(X_ij=0)<=1/S<=(A+B-1)/(AB)
                    =alpha+beta-alpha*beta.

This proves the simultaneous row/column bound, including the product correction.

## 4. Consequence for actual padded residuals

For an R-by-C completion rectangle with residual row margin a>=C*L and
column margin b>=R*L, where L>=0,

    alpha <= (C-1)/(C*L+C-1) <= 1/(L+1),
    beta  <= 1/(L+1).

The latter inequalities use C*L >= (C-1)*L and R*L >= (R-1)*L.
Thus P(X_ij=0)<=2/(L+1). A signed adjustment with at most two negative unit
cells rejects only if one of those cells is zero, so the ordinary union bound
proves rejection <=4/(L+1). In particular **L>=7 gives half acceptance**.
The sharper product expression improves constants but is unnecessary for
this safe sufficient condition.

For singleton rectangles R=1 or C=1, the completion table is determined by
its margins and the existing between-map feasibility theorem handles actual
physical adjacent targets without rejection. Empty rectangles remain their
separate branch. For arbitrary physical capacities, the existing cap premise
is still needed to identify the reference fiber with an unrestricted ordinary
fiber before applying this result.

`Research.ConstantPaddingAcceptance.reference_edge_acceptance_seven` derives
the full residual floors, equal totals and directional adjustment bounds from
the actual physical adjacent move. It retains the source `hB` and `hcap`
hypotheses and supplied reference indices. Singleton dimensions use the
existing zero-donor theorem; empty completion rectangles are excluded by the
reference indices and belong to the existing alternate branch.

The acceptance theorem alone does not construct the completion draw. The
[frozen complete sampler](legacy-completion-backend.md) supplies an accurate
arbitrary-margin backend at outer `L=7`, using its own internal padding.
Its new physical adapter and complete cost composition remain open.

## Smaller blocks and the padding-growth guard

The separate [block-floor theorem](../research/shape-refinement/) proves half
acceptance whenever `min(R,C)L >=3(R-1)(C-1)`. Thus the executable scale helper
can choose

`L=min(7,max(1,ceil(3(R-1)(C-1)/min(R,C))))`.

For 2×2 completions this is `L=2`. After choosing L, the helper uses
`U=max(2,2L,ceil(47RCL·min((m-1)(n-1),m+n-2)/32)-1)`, using the
[reciprocal growth proof](reciprocal-padding-growth.md), and verifies that exactly the
requested rows and columns are large at that cutoff. The original full-table
donor count is essential in this count-growth guard. For example, the 4×4
margins `(2,1,1,1)` at `U=2` leave a 1×1 completion block with zero internal
donors, yet adding one at that large cell changes the ordinary table count
from 33 to 34. Replacing the full-table donor count by zero would be false.

The bounded [3×3 example](../reports/residual-padding.json) has margins
`(46,46,1)`, `U=46,L=2`, 49 positive physical states and 300 directed edges.
Its smallest exact reference acceptance is `48/49`, and padding changes the
original count from 231 to 251. The executed path checks feasibility and work
budgets; its deliberately vacuous mixing allowance proves no accuracy claim.

## Reproduction

```sh
PYTHONPATH=src python3 experiments/reciprocal_zero_bound.py --output .local/reports/reciprocal-zero-bound.json
PYTHONPATH=src python3 experiments/residual_padding.py --output .local/reports/residual-padding.json
python3 research/repair-accept/verify.py --scope constant-padding --output .local/constant-padding-fresh
```

The [exact report](../reports/reciprocal-zero-bound.json) checks 24 fibers,
34,082 tables, 672 weighted levels and 1,312 actual directed edges, including
zero-margin and singleton boundary cases. These finite checks supplement the
arbitrary-parameter Lean proof. The formal runner requires the pinned compiler
and already-built baseline imports; use a new output directory for each run.
