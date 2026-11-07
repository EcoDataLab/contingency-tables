# Growing-row higher-token extension: slice density, exact load, and limits

11 October 2026. The [one-token family](growing-row-comparison.md) extends
to a growing small-row total h. Independent AI mathematical reviews passed
for this extension and its [general junction comparison](junction-star-comparison.md).
This is reviewed mathematics for specified ordinary margins, not a compiled
Lean theorem or arbitrary-margin inverse-gap result.

At bounded aspect it gives an explicit `64856A d^5` allowance. Applying
Morris's classical theorem to both conditional columns and small-row places
gives `C_Z(48400A²+121000A)d⁴+1000C_Zd³`, with `C_Z` universal and
unextracted. The preceding one-token result keeps its sharper constants.

## Scope and the key density estimate

Let R,b,U,L,h,J be integers with R,b>=2, U>=2, L>=7 and

    1<=h<=U/[2(R-1)], H=U-1,
    T=42(R-1)b(bH+1)+U, S=T+bL, J>(R-1)S+h,
    Tlast=bH+bJ-h-(R-1)T.

Rows are (h,T,...,T,Tlast), columns (H^b,J^b). There is one small row,
R large rows, b small and b large columns, p=b(R+2). Original large-line
slack is strictly positive for every balanced profile. Large-row selected
mass is at most bH, and each large column's selected mass is at most h.
The same cap-vacuous dense-row counting argument gives

    delta W<=w_A<=W, delta=41/42,
    W=binom(S+b-1,b-1)^(R-1).

All relevant active LL inverse counts obey the same bound: the minimum dense
column total is J+RL-h-1, still above the sum of first R-1 row totals.
Use canonical capacity M+dL+U+2, where M is the original total and
d=10+(R+2)(2b+1); it excludes no full completion. In particular nu_A<=p^2 W; this is a RAW
mass bound, not a normalized tilt or lost factor of total defect mass.

Let v be the small-row vector, a weak composition of h among 2b places.
The displayed range implies U>=R and h<=H, so every v is feasible. Given v, each small-column LS vector is an
independent uniform composition of H-v_j among R rows. Put
M_R(t)=binom(t+R-1,R-1), B(v)=product_(j small)M_R(H-v_j), B0=M_R(H)^b.
The useful ratio is a product over R-1 factors, NOT over v_j particles:

    B(v)/B0=product_(j small)product_(q=1..R-1)[1-v_j/(H+q)]
              >=1-(R-1)sum_(j small)v_j/U>=1/2.                (1)

The first inequality is the finite product bound with nonnegative factors.
This is why a constant product-slice density survives growing h in the
stated range. Using a weaker denominator after expanding over v_j instead
would lose this estimate unnecessarily.

## Exact Polya coupling and unit place comparison

For a small-to-large place move v->v-e_j+e_c, restore its missing column
particle to row r with probability

    (eta_r+1)/(H-v_j+R).

Uniform Comp(H-v_j,R) maps EXACTLY to uniform Comp(H-v_j+1,R): each target's
incoming mass is its total particle count divided by that denominator and
the source composition cardinality. Other columns remain independent.
This is a coupling of the actual conditional unit slice laws.

For complete-graph inclusion on 2b places, the [one-token proof's tagged Moran argument](growing-row-comparison.md#classical-complete-graph-composition-gap-with-exact-clock)
gives gap 2b with rates v_i(1+v_j). Its rates are at most
K_h=(h+1)^2/4. Thus uniform place-composition variance is at most
K_h/(2b) times COMPLETE unit-transfer energy.

To compare this with small/large bipartite unit transfers, route a same-side
unit transfer i->j via each of the b opposite-side places, averaging paths
of length two. A fixed cross-edge has a unique coordinatewise-minimum
configuration. It can be used by at most b-1 same-side pairs from either
side. Cauchy-Schwarz therefore gives

    E_complete,unit<= [1+4(b-1)/b] E_bipartite,unit<=5E_bipartite,unit.

There is no particle multiplicity or h-dependent congestion in this UNIT
edge comparison. It must not be mistaken for an unweighted comparison of
inclusion's particle-dependent rates. Combining it with (1) and the Polya
coupling gives, for any balanced center F,

    Var_unit,B(F)<= [U^2/(4R)] E_G,unit(F)+(5K_h/b)E_J,unit(F).  (2)

Here G transfers one LS unit between any large rows in one small column;
J is A->A-SS+LS+SL. The same actual source weights give
Var_nu(F)<=p^2/delta times the corresponding weighted right side of (2).

## J endpoint load does not grow with h

Counting occupied large places alone suggests a spurious h factor. The
true incoming load at B is at most N4(B)*w_B, with N4 the number of positive
LS/SL pairs. The general junction proof's five-family charge N4<=N0, and the exact selected
crossing repair mass N0*w_B<=nu_B, instead give

    sum_(incoming J to B)min(w_A,w_B)<=nu_B.                   (3)

Each J edge has its unique shared defect of weight w_A, with designated
repair A and actual B-d conductance at least min(w_A,w_B)/2. For conditional
repair means F and harmonic means H, use the JOINT bound
N+sum nu(F-H)^2<=2E_star. The [general junction comparison](junction-star-comparison.md) proves

    E_J,mu(F)<=3N+6E_star+3sum nu(F-H)^2<=12E_star.             (4)

This does not assume uniform LL activity, and has no extra h or R congestion
factor. Full all-label nu is essential; a restricted subset of repair labels would
not justify (3). No normalized center-law mass is canceled.

## An explicit numerical bound

The [row DD bridge](growing-row-comparison.md#actual-g-copies-j-shared-defects-and-bounded-charges) has Lrow>=Rb^2 and noise coefficient<=3/b. Its
contribution to the coefficient of N is at most 3pU^2/(2delta); its raw DD
coefficient is at most 6U^2/delta. Since h>=1,

    K_h<=h^2<=U^2/[4(R-1)^2],
    (R+2)/(R-1)^2<=4.

Equations (2)-(4) and the exact Var_D=N+Var_nu(F) decomposition therefore give

    Var_D(g)<=(6/delta)U^2 E_DD
                 +[2+(63/delta)pU^2]E_star
             <=67pU^2(E_DD+E_star).                           (5)

This keeps the same raw order throughout the entire displayed h range. The
h^2 rate maximum has been paid explicitly, then absorbed by that range; it
has not vanished by normalizing the repair law. The unchanged rational clock
gives at most 536p^2U^2, or 64856d^4s^2 at U=11ds, and 64856A d^5 under
s^2<=Ad. These are reviewed mathematical bounds, without Lean verification.

## What the sourced Morris refinement changes

If Morris is used ONLY for the LS conditional columns, a remaining inclusion
place coefficient of order h^2 leaves a J contribution of order R^3b^2h^2
in the normalized trace. Its one-token d^4 conclusion does not then automatically
persist over the full h range.

The same [Morris Theorem 3](https://arxiv.org/pdf/math/0405161) also applies to
the uniform place compositions, now with 2b colors and h particles. After
its explicit clock conversion the unit allowance is
C_Z(1+h/(2b))^2/(2b-1). The elementary bipartite comparison above multiplies
this by five, and (1) by at most two. Thus place factor 5K_h/b is replaced by
10C_Z(1+h/(2b))^2/(2b-1), with C_Z chosen at least one. It is the same
unextracted universal source constant, not a numerical theorem proved here.

Keeping actual G copies, (4), and the sharp G noise algebra yields the safe
same-clock expression

    K_rational<=1600C_Z b^2U^2
                    +8000C_Z R^3b^2(1+h/(2b))^2.              (6)

The h dependence is still visible. Using h<=U/[2(R-1)], (6) is at most

    C_Z[(1600b^2+4000R)U^2+16000R^3b^2].                     (7)

At the actual cutoff U=11ds, d=10+(R+2)(2b+1), s=R+2b-1, use b^2<=Ad/4,
R<=d/4 and R^3b^2<=d^3/16. The resulting restricted aspect allowance is

    C_Z[48400A^2+121000A]d^4+1000C_Zd^3.

Thus a sourced classical O(d4) order can survive the same growing h range,
provided the place theorem is ALSO used with its true unit clock. The
explicit numerical bound (5), the classical constant, and the
restricted-family hypotheses remain distinct. No general exponent is claimed.

## Precisely what prevents transplanting this to arbitrary margins

1. **Original large-row budgets couple the columns.** The T margins make
   every row sum of b LS entries feasible. With a large row only U and two
   small columns H, the putative product support includes row mass 2H>U.
   Actual support is truncated, target rows can be inactive, and neither
   full-composition product tensorization nor all G edges are available.
2. **The dense weights need not have constant tilt.** J above the sum of
   first R-1 dense row totals makes the forced last row nonnegative for
   every independent choice. Without it, column constraints exclude many
   choices, couple dense rows, and can make w_A/W highly profile-dependent.
   Comparing normalized repair and incidence laws does not supply the
   required weighted center inequality.
3. **One small row gives one unrestricted place composition.** Multiple
   small rows share each small-column budget. Their place arrays are
   constrained transportation tables rather than Comp(h,2b); the Polya
   scalar slice identity does not supply their global place Poincare bound.
4. **The product density is a real range restriction.** Beyond h=O(U/R),
   B(v)/B0 can be very small (all h tokens in one small column gives a
   binomial ratio). A constant-density reduction to uniform place law can
   fail. This is a limitation of this argument, not a proved physical-gap
   obstruction.
5. **Complete ordinary label domains and capacities matter.** Restrictive
   cell caps, activities or structural zeros can remove inverse labels or
   change their weights. The proof is for uniform completion counts with
   canonical source capacities, not arbitrary added constraints.

All-large original activity is used in the restricted product/LL count
construction; the new J congestion comparison itself no longer needs that
activity lower bound. For general ordinary margins the missing obligation
is a real weighted center comparison on the constrained support, with
original-slack-dependent moves and dense weights. Merely replacing the
small-row parameter h in these formulas does not establish it.

## Focused finite check

The [exact checker](../experiments/growing_row_extension.py) uses repository
bounded compositions at R=3,b=2,U=8,h=2, without changing those parameters.
Its [deterministic report](../reports/growing-row-extension.json) records ten
place compositions, minimum B(v)/B0=7/12, exact Polya source and target
marginals for all 16 relevant place edges, and complete-to-bipartite unit
routing factor 3. It counts configuration edges once, even when donor
occupancy is two.

```sh
python3 experiments/growing_row_extension.py --output .local/reports/growing-row-extension.json
```

This check covers the new slice and place mechanism. It performs no dense
completion or defect enumeration, and is not an all-observable physical-gap
certificate, Lean build or runtime benchmark. The parameter-wide conclusion
rests on the displayed proof and the [separate AI reviews](growing-row-extension-review.md).
