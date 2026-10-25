# Aggregate completed-table incidence and the bounded-aspect d6.5 allowance

11 October 2026. Independently reviewed mathematics by separate AI agents,
with exact finite checks. Grouping correction moments after repairing their
**full completed tables** gives the rational inverse-gap allowance
15488 A^(3/2)d^(13/2) when s²≤Ad, where s=m+n−2. This is a spectral-gap
derivation, not a machine-runtime exponent. The complete new physical Lean
assembly remains open; no human review or novelty claim is made.

## Setup and the actual cap premise

Take ordinary unrestricted nonnegative integer margins of equal total,
m,n≥2, uniform small capacity/cutoff U≥2, and padding L. Let

    R = number of rows with margin ≥U,   C = number of columns with margin ≥U,
    a = m−R, b = n−C,
    S = {(i,j): r_i<U or c_j<U},        p = |S| = ab+aC+Rb.

Weights are actual uniform dense-completion counts. Cell restrictions,
interaction weights and the inverse-factorial worker law are outside this
argument. Use the same boxed correction kernel, hard limit, current support
and owned leaf energies as the [retained-root spectral proof](retained-root-spectrum.md).

The source residual tables have padded full margins **and** the original
selected-cell partial inequalities
Σ_selected in row i A_ij≤r_i, Σ_selected in column j A_ij≤c_j.
The required hcap quantifies over **every** such residual table and every
cell: A_ij≤B_ij. A cap checked only on already-positive profiles does not
replace this ordinary child-card premise.

The actual canonical capacities discharge it: selected cells have B_ij=U
and their residual-table entries are at most min(r_i,c_j)≤U−1. Large cells
have B_ij=M+dL+U+2, with M the original total and d≥mn; every entry
is at most the padded total M+RCL≤M+dL. Thus no residual completion is
excluded. The cap is derived from the construction, rather than supplied
as the desired correction bound.

## Repair each completed defect before aggregating

Fix a row-major context at selected cell s, its earlier selected prefix,
and an adjacent level l. The exact boxed correction is a sum over one
exceptional later cell t>s. Its nonzero moment is
μ_t=X_t(U+1−X_t), with 1≤X_t≤U.

Expand each hard weight into its individual completions. A completed defect
has full views Q=X+e_s−e_t, with the same dense completion outside S.
Put v=(row(t),col(s)). Its actual full repair is

    A = X−e_t+e_v = Q−e_s+e_v.

The source joint-repair theorem gives a residual table A satisfying both
padded margins and the original partial constraints. Row-major order fixes
every earlier selected entry. Its current child is l−1 when the donor row
differs from the current row, and l when the rows agree.

For fixed labels, recover the entire source:

    X = A+e_t−e_v,       Q = A+e_s−e_v.

This is injective on completed defects. When v is large, the repaired dense
entry is A_v=Z_v+1, so the inverse recovers the original completion as
Z_v=A_v−1. Projected completion weights can change; they are not assumed
equal. Receiver positivity alone need not make every inverse feasible:
ordinary slack and cap conditions still apply. We only enlarge the image
when taking nonnegative upper bounds.

Now group by each repaired **full** table A, keeping every distinct donor
label. Each fixed (A,t) has at most one completed preimage. This retains
all completion multiplicities and explains why large crossings cause no
missing weight factor. The source child-card identity counts precisely these
full residual tables.

The recovered donor is A_t when col(t)=col(s), and A_t+1 otherwise.
Since every selected A_t≤U−1,

    μ_t ≤ U A_t + A_t                       in the same column,
    μ_t = (A_t+1)(U−A_t) ≤ U(A_t+1)        otherwise.

## Left and right child moment bounds

For any repaired residual table,

    Σ_(t∈S) A_t ≤ Σ_small rows r_i + Σ_small columns c_j ≤ (a+b)(U−1).

Partition S into all small-row cells and large-row/small-column cells;
SS entries are counted once in the first part. The original partial
constraints are essential here.

Different-row donors land in the left child. The extra same-column mass
is a subset of this selected mass, and there are at most p donor +1
terms. With k=a+b, their moment sum for each full A is at most

    U k(U−1) + pU + k(U−1) ≤ kU²+pU =: K_left.

Same-row donors land in the right child and have moment at most U(A_t+1).
For a small current row, its selected total is at most U−1 and at most
n−1 other cells occur, giving U²+(n−2)U. For a large current row,
only the b small columns are selected; their other totals give
(b−1)U². A common bound is

    K_right = max(1,b−1)U²+(n−2)U.

It covers b=0, when a selected current cell can only lie in a small row.
After summing over the two full-table children, with masses z_(l−1),z_l,

    c_l ≤ K_left z_(l−1)+K_right z_l ≤ K_row max(z_(l−1),z_l),
    K_row = [k+max(1,b−1)]U²+(p+n−2)U.

Transposing the whole table and swapping x,q preserves full repair,
completion sets, weighted graph energy and directed accepted counts. The
second whole-graph orientation therefore has
K_col=[k+max(1,a−1)]U²+(p+m−2)U. This chooses between complete proofs;
it does not reorder cells within a context or identify their local kernels.

## Reference-branch coefficient at the preselected scales

Put d=10+(m+1)(n+1), s=m+n−2, and preselect U=11ds,L=7 before
classifying any margin. The [reciprocal growth proof](reciprocal-padding-growth.md)
gives padded/original count ratio at most two. The [actual reference-move
theorem](constant-padding.md) gives half acceptance at this padding.

Choose the whole orientation with small-column count t=min(a,b). If
k≥2, max(1,t−1)≤k/2. The [spectral path theorem](retained-root-spectrum.md)
and actual support diameter at most U−1 give

    CT ≤ (3k+1)U² + [2(p+max(m,n)−2)−1]U ≤ (3k+2)U².

The last step uses p+max(m,n)−2<d and U≥2d. If k=1, the same
calculation gives CT≤6U²; k=0 has no selected defect branch.

For a nonempty reference rectangle, R,C≥1, hence k≤s. Thus
CT≤(3s+2)U², including s=2: its worst a=b=1,p=3 case gives
7U²+5U≤8U². The previous CT≤pU² is still valid, so use the smaller
coefficient when appropriate.

The existing repair comparison gives C_full≤2p²CT. Reference accepted
conductance dominates min-weight energy by one half; the harmonic trace
with rational step β=1/(2Q) consequently has allowance 4Q C_full.
Using the actual canonical reference allowance Q=4p−3≤4p yields

    K_rational ≤ 3872 d⁵s²(3s+2),
    K_dyadic   ≤ 7744 d⁵s²(3s+2).

For s²≤Ad, use 3s+2≤4s to obtain 15488 A^(3/2)d^(13/2) rational
and 30976 A^(3/2)d^(13/2) dyadic. The [earlier arbitrary-aspect
allowances](retained-root-spectrum.md), 431d⁸ and 862d⁸, remain valid;
take the better bound. Constants are algebraic consequences, not fits.

## Empty completion rectangle: separate unit normalization

When R=0 or C=0, do not use k≤s. Completions are unique, weights
and accepted edge conductances are one, and the degree bound is
Q_unit=2(m+n)−3=2s+1. For the mathematical unit harmonic trace with
β=1/(2Q_unit), its allowance is 2Q_unit C_full, giving

    K_rational ≤ 484(2s+1)d⁵s² ≤ 1210 A^(3/2)d^(13/2),
    K_dyadic   ≤ 2420 A^(3/2)d^(13/2).

This degree normalization differs from the compiled actual RationalTrace
kernel's Q=4p−3. It is also not a new claim about the old compiled
unitChain step size. The uniform combined bounded-aspect constants above
describe the reference trace and this separately normalized unit trace.
The unit certificate and its normalization must be kept together.

All statements concern the nonempty positive defect branch. Zero margins
are permitted by the count and variance arguments; the current joint-output
Python terminal retains positive-margin scope. The [frozen earlier complete
sampler](legacy-completion-backend.md) supplies the mathematical uniform completion
backend at outer L=7, but its new adapter, encoded composition and full new
physical Lean assembly remain separate. No faster complete sampler runtime follows.

## Exact checks

Run:

    PYTHONPATH=src python3 experiments/aggregate_incidence.py --output .local/reports/aggregate-incidence.json

The [saved report](../reports/aggregate-incidence.json) checks 45 contexts,
1,856 completed auxiliary assignments and 1,064 large crossings, including
source/target weights 17→18. It verifies full reconstruction, prefix and
child values, fixed-(A,t) injectivity, exact grouped moments, and actual
branch degree/acceptance bounds. The script refuses -O; these finite checks
supplement the all-parameter proof and do not measure mixing, replace formal
assembly, or establish a physical-gap lower bound.
