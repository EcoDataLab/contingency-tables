# An explicit thin-family comparison with more than one first-row token

11 October 2026. Restricted mathematical derivation; its independent AI source
review is recorded separately.
This extends the [single-token family comparison](thin-parallel-comparison.md)
while retaining ordinary completion counts and the same physical defect trace.
It is not a Lean theorem, a general-margin result, or a sampler/runtime bound.

## Family, raw bound and clock

Take b>=2,U>=3,L>=7 and 1<=h<=floor(U/2). Put H=U-1,C=b and

    T1=42b(bH+1)+U, Rbase=T1+bL,
    J=T1+bL+h+1, T2=bH+bJ-h-T1,
    rows=(h,T1,T2), columns=(H repeated b,J repeated b), p=4b.

The displayed h-dependent J and T2 replace the single-token margins.
Use the same canonical large capacity M+dL+U+2, actual ordinary completion
weights and literal reference accepted conductances. For all positive defects
D and every real observable g, the comparison is

    Var_w,D(g)<=751bU^2(E_star+E_DD)(g).

The canonical rational proposal beta=1/[2Q],Q=4p-3 gives

    K_rational<=1502QbU^2<=1502p^2U^2.

At d=8b+14,U=11d(2b+1), p<d/2 and2b+1=(d-10)/4<d/4 give
K_rational<2839.71875d^6<=2840d^6. The next-power-of-two slot clock has
at most twice this coefficient,5680d^6. Use any legacy clock's own beta.
The result contains no external unextracted constant. The single-token
result retains its sharper raw coefficient100; this extension changes scope.

## Exact law and physical count premises

A balanced first row v is any weak composition of h into2b places. For small
column j, the large-row split y_j ranges independently over0,...,H-v_j.
Its slice cardinality is

    N(v)=product_small_j(U-v_j) in [U^b/2,U^b],

because product(1-v_j/U)>=1-sum_small_j(v_j/U)>=1/2. The uniform balanced
selected law has composition marginal proportional to N(v), rather than a
uniform composition marginal. Both large-row selected totals are <=bH<T1,T2,
and large-column selected totals are <=h<J: all original dense-line slacks
are positive.

The [single-token count argument](thin-parallel-comparison.md) applies with
these adjusted margins: every large-column residual is >=J-h+2L=Rbase+2L+1,
and in a designated LL inverse defect is >=Rbase+2L. The first dense-row total
lies in[Rbase-bH-1,Rbase]. Thus all first-row weak compositions fit and the
second dense row is forced; the same finite-product estimate gives

    delta W<=w_A<=W, delta=41/42, W=binom(Rbase+b-1,b-1).

Canonical capacity contains all ordinary source completions. LL inverse
counting and actual half acceptance remain distinct. The completed repair
injection and active LL lower bound give

    b^2w_A/2<=nu(A)<=p(p-1)w_A<16b^2W.

For repair-fiber means F_A, harmonic star means H_A and raw fiber noise N,

    Var_w,D(g)=N+Var_nu(F),
    N+sum_A nu(A)(F_A-H_A)^2<=2E_star.

## A direct finite composition gap

This gap identity is classical. [Kim and Sau, *Spectral gap of the symmetric
inclusion process*](https://arxiv.org/pdf/2303.16607v2), equations (1.1)–(1.2)
and Corollary 1.2, give these rates, uniform stationary law and gap equality
when alpha=1 and all complete-graph edge rates are 1; Section 1.3.5 discusses
the explicit complete-graph spectrum. The coupling below proves this special
case directly. Its application to the physical bridge comparison is the
contribution here.

On all weak compositions v of h into n>=2 places, define rates
q(v,v-e_i+e_j)=v_i(v_j+1),i!=j. Reverse rates are equal, so the uniform
composition law is reversible. This inclusion process has gap exactly n.
Here is a proof fixing its rate convention.

Give h tokens distinct labels and n possible colors. Each label resets to
each color at rate1; each ordered receiver/donor pair of distinct labels
copies the donor's color at rate1. Occupation counts have exactly the stated
rates: resets contribute v_i and copying contributes v_i v_j.
Couple two label systems with the same clocks. If D_a is the mismatch
indicator of label a, a reset erases its mismatch. A copying event(a,b)
changes the total Hamming mismatch D by D_b-D_a. Summing ordered pairs gives
zero, whereas resets give generator drift -nD. Hence E[D_t]=e^(-nt)D_0.

Neighboring compositions admit lifts differing at just one label. Occupation
unit-transfer graph distance is half the L1 distance and is <=D. Therefore
for every function f with unit-edge Lipschitz seminorm Lip(f),
|P_t f(v)-P_t f(w)|<=Lip(f)e^(-nt) on every unit edge. A real nonconstant
eigenfunction with eigenvalue lambda attains Lip(f)>0 at some unit edge.
Since P_t f=e^(-lambda t)f,lambda>=n. Symmetry and connectedness give the
finite spectral inequality. The nonzero linear function v_i-h/n has
Lf=-nf, so equality of the gap follows, although only the lower bound is used.

With unordered unit-transfer energy E_complete and
K_h=floor((h+1)^2/4), the rate bound v_i(v_j+1)<=K_h gives

    Var_unit,comp(f)<=E_inc(f)/n<=K_h E_complete(f)/n.

Uniform mass cancels exactly; E_inc counts each rate-weighted edge once.
No external zero-range theorem or numerical spectral experiment is needed.

## Slice coupling and center inequality

Keep auxiliary G moves that transfer one unit between the two large rows
within a small column. Auxiliary J moves take a first-row token from small
column j to large column c, restoring that column into either large row r:
B=A-e_0j+e_0c+e_rj.

For v_j>0 the affected grid grows from n_grid=U-v_j to n_grid+1. From uniform
y in0,...,n_grid-1, increment y with probability(y+1)/(n_grid+1) and otherwise
keep it. The target is exactly uniform: each endpoint probability is1/(n_grid+1),
and interior z receives(n_grid-z+z)/[n_grid(n_grid+1)]. Thus for uniform slice
means m, Jensen and U^b<=2N(v) yield U^b E_bip(m)<=2E_J,unit(F), where E_bip
uses first-row token transfers across the small/large column partition.

Route each same-part token transfer i->j through every opposite-part place k,
with weight1/b, using v->v-e_i+e_k->v-e_i+e_j. For each fixed directed cross
edge, the first-step role has at most b-1 destination choices and the second-step
role at most b-1 origin choices; each initial composition is uniquely recovered.
The two-term square cost2/b gives total charge<=4(b-1)/b. Add original cross
transfers and divide directed energies by2 to get E_complete<=5E_bip.

Evaluate the N-weighted composition variance at the uniform-composition mean,
apply the n=2b inclusion theorem and add conditional grid tensorization:

    Var_unit,B(F)<=U^2/8 E_G,unit(F)+5K_h/b E_J,unit(F),
    Var_nu(F)<=2b^2U^2/delta E_G,w(F)+80bK_h/delta E_J,w(F),

where w_e=min(w_A,w_B)>=delta W. This uses the actual selected law and raw
repair load, rather than cancellation of normalized center tilts.

## Literal transport and explicit coefficient

The [single-token parallel G construction](thin-parallel-comparison.md) still
gives b^2 distinct actual DD bridges per G edge. Its receiver(0,j) has source
Q entry v_j+1<=h+1<=U; dense residuals remain those of the designated centers.
Endpoint lists are globally disjoint, so the same charge holds:

    E_G,w(F)<=6/b^2 E_DD,G(g)+3/b N.

Each J edge has the literal shared defect
x=A-e_0j+e_0c,q=A-e_0j+e_rj,with designated repair A,weight w_A and accepted
incidence c_Ad=w_A. Its actual B,d incidence obeys c_Bd>=w_e/2. Distinct J
edges give distinct defects. At B there are at most2b min(b,h) incoming J
moves; hence their total w_e/nu(B) is <=4min(b,h)/b<=4. Expand each contrast
through g_d and H_B. Designated noise, actual B,d star energy and the harmonic
center error give

    E_J,w(F)<=3N+6E_star+12sum_B nu(B)(F_B-H_B)^2<=36E_star.

Source and target centers can overlap as classes for h>1, so their star costs
are added here. Insert both transport inequalities and N<=2E_star:

    Var_w,D(g)<=12U^2/delta E_DD,G
      +[2+12bU^2/delta+2880bK_h/delta]E_star.

Since h+1<=U,K_h<=U^2/4 and2<=bU^2, the star coefficient is at most
[1+732/delta]bU^2=(30785/41)bU^2<751bU^2. The DD coefficient is smaller.
Retain all additional DD energy. Normalized physical variance and energy are
Var_w,D/Z_D and beta(E_star+E_DD)/Z_D: only their common defect mass cancels.

## Evidence boundary

The [focused checker](../experiments/thin_row_extension.py) and
[saved report](../reports/thin-row-extension.json) use b=2,U=4,h=2,L=7.
They check 121 balanced profiles, 3,926 defects, 5,054 DB incidences, 172 grid edges,
688 DD bridges and 328 shared J defects, with endpoint charge 1 and incoming
J degree 8. Its 10 compositions have exact slice sizes 8..16; exact coupling
marginals and routed path charge 2 are checked. Four observables check raw
variance and actual transport inequalities. These finite checks supplement
the all-parameter derivation; they are not an all-observable matrix certificate,
a Lean proof, dense-completion enumeration, a full DD matrix, or a runtime
benchmark. Arbitrary thin margins and other masks remain outside this theorem.

    PYTHONDONTWRITEBYTECODE=1 python3 experiments/thin_row_extension.py \
      --output reports/thin-row-extension.json

The [independent AI source review](thin-row-extension-review.md) records the
mathematical and adaptation review. No outside human review is claimed.
