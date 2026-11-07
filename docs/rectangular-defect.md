# Variable-capacity transport on arbitrary all-small rectangles

Mathematical derivation, 11 October 2026, reviewed by a separate AI agent. For positive ordinary margins below the cutoff on both sides, tighter coordinate capacities extend the defect-chain inverse-gap exponent `31/2` to **every aspect ratio**. The [boxed quadratic hard-limit lemma](../research/rectangular-defect/) is compiled separately; the full physical Lean specialization remains open.

## Bound and scope

Let `m,n>=2`, let all integer row and column margins be positive with equal total, and suppose **both sides' margins are strictly below U**. There are no cell caps, structural zeros or weights. Set `p=mn`, order cells row-major, and define

`t_s=min(r_row(s),c_col(s))`, `B_s=t_s+1`,

`T_B=max_s { B_s(B_s+1)/2 * [2+½Σ_{t>s}(B_t+1)^2] }`,

`C_B=T_B+(p sqrt(T_B)+1)^2`.

The transport argument below gives the **same physical graph** full variance bound `V_full<=C_B E_full`. Its previously reviewed accelerated defect trace then has

`K_rational <=(4m+4n−6) C_B`,

and the dyadic variant has at most twice this allowance. At `d=10+(m+1)(n+1), U=5d^3`, the uniform rectangular consequence is

`K_rational <=20000 d^(31/2)`, `K_dyadic <=40000 d^(31/2)`.

The bounds apply to arbitrary aspect ratios. Existing selected/reference chains outside the positive both-small branch are unaffected. This changes neither the reviewed defect-trace transition nor its terminal support correction. No complete sampler runtime exponent follows.

## 1. Capacity change preserves every actual state and edge

Write physical views `(x,q)`. Row sums of `x` are `r`, column sums of `q` are `c`, and `q-x` is either zero or `e_s-e_t`. Therefore

`x_ij<=r_i` and `x_ij<=q_ij+1<=c_j+1`,

`q_ij<=c_j` and `q_ij<=x_ij+1<=r_i+1`.

These imply `x_ij,q_ij<=min(r_i,c_j)+1=B_ij`. Positivity and strict smallness give `2<=B_ij<=U`. The new complementary view is `y'_ij=B_ij-q_ij`. It is nonnegative for every actual state. Conversely a state feasible with these tighter capacities also satisfies the old capacity `U`, so the sets in `(x,q)` are exactly equal. Translation `y'=y-(U-B)` preserves each unit difference vector. Designated repairs depend only on `(x,q,s,t)`. Thus all exchange and repair edges, their unit weights and energies are unchanged.

Every ordinary table has `A_ij<=t_ij<B_ij`. The tighter capacities consequently exclude no ordinary table and no repaired table.

## 2. Actual contexts and conditional variance

For a current cell `s`, fix each earlier table entry `a_t` and its complementary coordinate `B_t-a_t`. Leave the current pair and later pairs free. The suffix list in abstract transport is **literally** `Ms=(B_t:t>s)`, and the current balance is `B_s`. This is an explicit bijection between local coordinates and physical coordinates outside the fixed prefix.

Balanced assignments on a suffix slot are `(a_t,B_t-a_t)`, `0<=a_t<=B_t`. Current child `j` is `(j,B_s-j)`. The contextual hard weight is one exactly when the assembled `x` rows and `q` columns have their prescribed margins; otherwise it is zero. Its child mass is exactly the number of ordinary tables with that prefix and current entry `j`; its child mean is the corresponding mean of the given physical observable.

The needed signature premises and the child's global no-valley property are available for **arbitrary capacities and arbitrary suffix lists**, already in the pinned source:

* `Sampling/FirstPaperContextTransport.lean`, `contextSoft_slices` and `contextSoft_tendsto`, has no equal-small-capacity hypothesis.
* `Sampling/FirstPaperContextChildren.lean`, `context_child_minimum`, accepts arbitrary `Ms` and current balance.

Apply the existing weighted-path variance theorem at current width `B_s`. The contribution of each fixed prefix is bounded by `B_s(B_s+1)/2` times its sum of adjacent contrasts. Finite conditional-variance telescoping over the product alphabets `Fin(B_t+1)` gives the ordinary-table variance exactly. This needs no new probabilistic approximation: expand the finite conditional means and use the usual variance decomposition at each cell.

If using the existing common-alphabet formal exposure lemma, one can instead embed every alphabet in `Fin(U+1)` with zero weight whenever a cell choice exceeds `B_t`. Its conditional variance reduces to the shorter positive child alphabet, and invalid prefixes contribute zero. The only additional identities are finite zero-extension sums.

## 3. Weighted auxiliary mass identity and repair

For adjacent current entries `l-1,l`, `1<=l<=B_s`, the root display is `(l,B_s+1-l)`. Removing its two root coordinates leaves the current pair

`(l-1,B_s-l)`, with occupancy `B_s-1`.

The boxed quadratic auxiliary kernel is exactly the sum over suffix assignments with **one** exceptional later slot `t`, whose pair occupancy is `B_t+1`; every other suffix slot has occupancy `B_u`. Its summand carries the scalar `(B_t+1)^2/4`. Box truncation ensures both coordinates of that exceptional slot are at most `B_t`, so its first coordinate lies in `1,...,B_t`.

This weighted identity follows directly by induction from `WidthWeightedTransport.quadraticAuxiliaryKernel`:

* The first term exposes the outer slot with occupancy `B_t+1`, sums all other slots at their balances, and multiplies by `(B_t+1)^2/4`.
* The recursive term first sums that outer slot at occupancy `B_t` and chooses the unique exceptional slot later in the list.

These two cases partition the single-excess assignments, so no profile is counted twice and no multiplicity is discarded.

Each positive hard-weight auxiliary assignment is an actual physical defect: current pair occupancy `B_s-1` means `q_s-x_s=+1`, the exceptional suffix occupancy `B_t+1` means `q_t-x_t=-1`, and all other occupancies imply `q_u=x_u`. Positivity of its hard weight gives the actual row/column margins. The assignment-to-profile map is injective since all displayed coordinates are retained. For a fixed exceptional slot `t`, repair it to

`A=x-e_t+e_(row(t),col(s))`.

Subtracting at the donor is valid because `x_t=q_t+1>=1`. Row-major `t>s` implies either `row(t)>row(s)` or equal rows with a later column. In the first case the receiver follows `s` and `A_s=l-1`; in the second the receiver is `s` and `A_s=l`. No earlier entry changes. The resulting ordinary table automatically satisfies its tighter capacities. For fixed labels `s,t`, the inverse formula reconstructs `x,q` uniquely from `A`.

Thus each exceptional type injects into one adjacent child, and its mass is at most the maximum of those two child masses. Importantly, the source theorem `Sampling/SmallContextCount.lean:149`, `conditional_defect_mass_le`, already accepts **arbitrary B** and gives this same child value. Equal capacities are required only by the source assembly wrapper, not by the repair theorem itself.

Writing `a,b` for the adjacent child masses, this proves

`c_quadratic <=¼ [Σ_{t>s}(B_t+1)^2] max(a,b)`.

## 4. Hard zeros and localized leaf transport

Apply the abstract variable-width root transport with the literal prefix, current balance and suffix list just described. Keep box/degree truncation on its quadratic auxiliary kernel. The physical soft marginal tends pointwise to the hard indicator. All marginals, the quadratic kernel and leaf energy are finite sums; the two endpoint masses are the only quantities divided by, and are positive whenever the adjacent contrast is nonzero.

The compiled [`VariableWidthLimit.lean`](../research/rectangular-defect/formal/VariableWidthLimit.lean) proves this boxed hard-limit statement with the actual quadratic auxiliary kernel retained. It imposes no common maximum suffix width. The theorem is an additive specialization of the existing `WidthWeightedTransport.integer_root_leaf_transport_widths` and the source finite-sum limit lemmas.

Using the preceding auxiliary bound and the existing root coefficient inequality gives the local contrast bound

`min(a,b)(mean_left−mean_right)^2 <= [2+½Σ_{t>s}(B_t+1)^2] E_owner`.

Zero-mass children contribute zero, by the same nonnegative minimum argument already used in `PhysicalLeafEnergy.lean`.

## 5. Physical leaf edges and ownership

Each literal leaf display has the fixed prefix, pair occupancy `B_s+1` at the current slot, and pair occupancy `B_t` elsewhere. Its vertices are obtained by removing one active unit outside the prefix. Removing it from the current pair gives a balanced profile; removing it from another pair gives exactly one surplus/deficit pair. All resulting coordinates are bounded by their own `B_t`, since the current display coordinates are `l` and `B_s+1-l`, both at most `B_s`. Two leaf vertices differ by a single unit exchange, so each literal leaf edge is in the tighter-capacity physical exchange graph and hence, by Section 1, in the original graph.

There is no new owner multiplicity. Given the two distinct edge endpoints, recover the whole display by taking their pointwise maximum. Compare each recovered pair occupancy with its own `B_t`: exactly the special slot is one overfull. Its first coordinate recovers `l`; earlier coordinates recover the prefix. These statements already appear with **variable** capacities in `GlobalDisplayOwnership.edge_owner_unique` and `edge_prefix_unique`.

Consequently a physical unordered edge belongs to at most one owner `(s,l,prefix)`. The sum of all owner energies is at most full physical exchange energy, with the same one-half oriented-edge convention. Multiplying local contrasts by their current-cell path coefficient and using this disjointness proves

`V_balanced<=T_B E_exchange<=T_B E_full`.

## 6. Full variance, defect trace and rectangular envelope

The original deterministic repair has injectivity for fixed ordered labels and unit-weight domination, independently of capacities. Its energy is a subset of the full graph energy. The existing abstract square-root repair inequality therefore gives

`V_full <= [T_B+(sqrt(p^2 T_B)+1)^2] E_full = C_B E_full`.

Let `a=min(m,n)`, `b=max(m,n)`, `M` be the common total. Both-small margins give `M<=aU`. Choosing the smaller side for the sum yields

`Σ_ij t_ij<=aM<=a^2U`,

`Σ_ij(B_ij+1)^2=Σ(t_ij+2)^2<=9Σt_ij^2<=9UΣt_ij<=9a^2U^2`.

The last positive margin condition is essential to `t+2<=3t`. Since `B_s<=U` and `U>=2,a>=2`,

`T_B <= (3/4)U^2[2+(9/2)a^2U^2] <=(7/2)a^2U^4`.

After expanding `C_B=(p^2+1)T_B+2p sqrt(T_B)+1` and dividing by `p^2a^2U^4`, its three terms are at most `119/32`, `1/8`, `1/1024`, because `p>=4,a>=2,U>=2`. Their sum is less than four, so `C_B<=4p^2a^2U^4`.

The reviewed trace theorem then yields

`K<=4(a+b) C_B<=16(a+b)p^2a^2U^4<=32p^3aU^4<=32p^(7/2)U^4`.

Here `a+b<=2p/a` and `a<=sqrt(p)`; no comparable-dimension assumption is used. Substitute `U=5d^3,p<=d` to obtain `20000d^(31/2)` rational, twice that dyadic.

## Verification status

Sections 1, 2, 3 and 5 are explicit finite combinatorial arguments with the cited generic source premises. The boxed variable-width hard-limit statement compiled locally with only `propext`, `Classical.choice`, and `Quot.sound` in its axiom list; the entire new physical specialization and numerical envelope have not been assembled into a Lean theorem.

The accompanying `check_variable_contexts.py` checks four unequal-capacity rectangles and their transposes. Exact assertions verify equality of reencoded unit neighbors with the actual graph, weighted auxiliary repair injection into the right child, every literal leaf edge's membership in the physical graph, and unique owner recovery across contexts. The four fixtures contain 452 physical states, 274 checked prefix/level contexts, and 289 owned physical leaf edges. These are bridge checks, not a proof by finite exhaustion.

Independent review reports no mathematical obstruction, and a separate broader enumeration checked 371 margin pairs, 2,212 balanced states, 63,564 defects, 23,084 nonzero auxiliary types and 7,323 weighted contexts without a failure. Its formal-interface caution is retained in Section 2: existing `RowMajorEnumeration.wordWeight` uses the uniform-U raw choice and cannot be reused unchanged. A new B-dependent assembly and zero extension are required. The proof is for the same positive both-small defect trace, not for the general selected/reference branch.
