# Joint repair-and-accept terminal for the general weighted defect trace

The joint correction below now has a bounded implementation in [general_defect_terminal.py](../src/contingency115/general_defect_terminal.py), with exact weighted-fiber and finite-word tests. It retains the sampled completion, checks padding before its inverse-fiber coin, and includes completion and rounding errors. The [shape-aware scales](shape-aware-defect.md) supply an additional guarded success certificate. This component does not itself establish endpoint mixing or a complete general outer sampler.

24 October 2026. The [composed Lean correction](../research/physical-trace-general-terminal-law/)
now proves the actual repair's exact support/slack label count, the full c0
lower bound, constant successful point mass, uniform proportions and positive
success. At `U=11d(m+n-2),L=7`, the checked bound is
`s>=c0/[2p(p-1)]`, using the actual smaller-scale padding theorem. All six
modules compile and pass full assumption audits, with separate AI source
review. The compact factorization `D0+abuv`, its linear-time implementation,
and the scalar `1/(8p)` corollary remain separate from that compiled ideal
law. The [subsequent finite-word composition](corrected-reference-sampler.md)
now checks the literal counter, bounded coin, scheduled endpoint error, fresh
retries and original-table zero restoration for the reference branch.

11 October 2026. Mathematical derivation reviewed by a separate AI agent,
with exact finite checks. This supplies a stationary uniform-table output
rule for the [general weighted defect trace](general-defect-trace.md), with
success at least **1/(8p)** at the ideal scales. That stationary-law and success
scalar claim remains reviewed mathematics; the later compiled label-sum law
above establishes the distinct smaller-scale bound. Neither installs a
complete general trace sampler.

## Scope

Unrestricted ordinary equal-total margins, m,n>=2, every row and column margin
POSITIVE, U>=2, L>=1, the actual source small/large mask and source capacities.
There is at least one small row or small column (p>0). Then p>=2 under m,n>=2.
Let a=#small rows and b=#small columns, and p=an+bm-ab. Dense completions may
have nonconstant counts. This statement is not about arbitrary external weights.

The defect trace stationary law is w(z)/Z_D, and a fresh exact uniform
completion above z makes the joint (defect,completion) law UNIFORM. Inverse
repair counts must be done on these joint pairs, not on profile marginals.

## Completion-retaining repair

For defect labels q-x=e_s-e_t, let v=(row(t),col(s)). If v is a small cell,
repair to balanced small profile A=x-e_t+e_v and retain the dense completion T'
unchanged. If v is a large cell, repair to A=x-e_t and change the dense
completion to T=T'+e_v. These are the source's completion-retaining physical
repair maps (not the different reference-star translation used for transitions).
The repaired pair is feasible; its unpadded small-row/small-column inequalities
are retained. Reject unless every repaired dense entry is >=L; successful
pairs correspond bijectively to ordinary original tables by unpadding.

## Exact successful joint inverse-fiber count

Fix one successful balanced joint pair (A,T). The small profile A has each
entry <U, because every small cell lies in a fixed small row or small column.
Define ordinary residual slacks on large rows and columns:

    rho_i=r_i-sum_small_row(A), gamma_j=c_j-sum_small_col(A).
    u=#{large i:rho_i>0}, vcount=#{large j:gamma_j>0}.

Let h_i be the number of small cells in row i and k_j the number in column j.
Set

    D0(A)=sum_{small z:A_z>0}(h_row(z) k_col(z)-1),
    ell_D(A)=D0(A)+a*b*u*vcount.

For a crossing z that is small, inverse repairs are

    x=A+e_t-e_z, q=A+e_s-e_z, dense completion T unchanged.

They are feasible iff A_z>0. There are h_row(z)k_col(z)-1 ordered label pairs
with this crossing, and both views are bounded by U. Their x row sums and q
column sums agree with A, so all completion margins and ordinary inequalities
are unchanged.

For a crossing z that is large, inverse repairs are

    x=A+e_t, q=A+e_s, dense completion T-e_z.

Here t must lie in the large row of z and a small column (b choices), while s
lies in a small row and the large column of z (a choices). Feasibility is
EXACTLY rho_row(z)>0 and gamma_col(z)>0. The corresponding added small entries
are <=U. The large entry T_z is >=L>=1 by successful-pair scope, so subtraction
is nonnegative. Padded residual rows and columns decrease by one consistently,
and all source caps remain satisfied. Thus there are ab choices at each of the
u*vcount active large crossings. If a slack is zero this inverse is forbidden,
even though the padded completion entry can be positive; this distinction is
essential and is exercised by the zero-slack fixture.

Defect labels are unique. They determine the crossing and the completion
inverse (T or T-e_z), so distinct ordered labels cannot duplicate a joint
preimage. These two crossing classes partition all designated inverse repairs.
This proves the displayed exact count. In particular ell_D depends only on A
for SUCCESSFUL pairs; before the >=L test, one must also check T_z>0 on large
crossings and the formula above need not hold.

## Computable lower bound and output law

Define

    c0=max[a*(n*a-1), b*(m*b-1)].

Small rows have positive margins, so each of the a small rows contains a
positive small entry. Each such cell has h_i=n and k_j>=a, giving
D0>=a(na-1). The symmetric small-column argument gives D0>=b(mb-1).
Thus ell_D>=D0>=c0>0. Also ell_D<=p(p-1), because the unique ordered defect labels
provide at most that many inverse preimages.

The terminal rule is:

1. Draw a fresh uniform completion conditional on defect z.
2. Apply the completion-retaining designated repair.
3. Reject unless all repaired large entries are >=L.
4. Compute ell_D(A) above and accept with probability c0/ell_D(A).
5. Unpad the repaired completion and return the original table.

Every successful balanced pair has uniform joint-defect mass ell_D(A)/Z_D.
Its corrected unconditional successful mass is exactly c0/Z_D. Successful
balanced pairs correspond bijectively to original ordinary tables. Therefore
accepted stationary output is uniform, with success s=N*c0/Z_D.

The existing source joint repair estimate gives `Z_D<=p^2 Z_B`, and
`Z_B<=P`, the full ordinary padded-table count. At ideal scales
**U=5d^3 and L=3d**, the already compiled ordinary padding bound is `P<=2N`;
see [PhysicalStationaryLaw.ideal_padded_count](../formal/Math115/PhysicalStationaryLaw.lean)
and the [stationary-success argument](physical-stationary-success.md). Hence

    s>=c0/(2p^2).

For m,n>=2, c0>=max(an,bm)/2 >=(an+bm)/4 >=p/4, so
s>=1/(8p). This supplies a linear-in-p
inverse-success allowance rather than a quadratic one. The lower bound is
conservative and the unit branch has the stronger existing dimension formula.

The correction requires geometry/support/slack counts, not completion counts
or a partition-function normalizer. A fresh terminal completion draw is still
required. Computing repaired profile/support/slacks costs O(p+m+n), and
checking/unpadding its returned dense matrix costs O(number large cells).

## Finite words and remaining obligations

Using floor(2^k c0/ell_D)/2^k introduces less than 2^-k terminal variation per
attempt. If an independently restarted defect endpoint is within delta of its
weighted stationary law and the fresh conditional completion call has uniform
TV error <=eta, the joint draw differs by <=delta+eta. With fixed feasible
fallback and R attempts, a sufficient output-TV bound is

    (1-s_lower)^R + R*(delta+eta+2^-k),
    s_lower=c0/(2p^2) at ideal scales.

The approximate trace transition budget, capped star exits, geometry draws,
and completion calls must first supply delta. The current repository already
has a compiled dilation/rounding completion family and bounded encoded sampler
at U=5d^3; the NEW trace and NEW joint terminal still need their own composition
and encoded-law identification. This note does not modify the existing compiler
proof and does not supply a complete machine-time exponent.

## Exact evidence and scope checks

The [general defect experiment](../experiments/general_defect_trace.py) repairs
every enumerated defect/completion pair and compares observed successful
preimages with `ell_D`. It also compares the entire corrected output support
with an independent exact table sampler, checks all successful point masses,
and retains nonconstant completion weights and zero ordinary residual slack.
The [public report](../reports/general-defect-trace.json) records those finite
checks; it does not claim a proof by exhaustion.

The independent AI review constructed inverse joint pairs directly from
ordinary tables, checking the argument in the other direction. It also found
and checked two essential scope boundaries:

* Retaining zero margins invalidates this `c0`: with `r=c=(2,0,0), U=2, L=1`,
  `p=8`, `c0=10`, but the sole ordinary table has only four joint preimages.
  The proposed acceptance would be `5/2`. This terminal requires positive
  margins. Removing zero rows and columns is a separate preprocessing step.
* `L=3d` by itself does not imply the success lower bound. With
  `r=c=(2,2,1), U=2, L=78`, stationary success is `11/3474`, below `1/(8p)`.
  Accepted output is still uniform; the diagnostic lacks the ideal cutoff
  or an independent `P<=2N` proof.

If there are no small cells (`p=0`), there are no defect labels and this
terminal is undefined. The existing completion branch handles that case.
Singleton dimensions likewise have a unique table and need no defect walk.
The new general trace, this terminal, finite approximation schedules, and
encoded program remain separate integration obligations. None changes the
existing compiled general sampler or its historical receipts.
