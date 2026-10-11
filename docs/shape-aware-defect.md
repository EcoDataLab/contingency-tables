# Shape-aware defect proposals and completion scales

11 October 2026. Mathematical derivations reviewed by a separate AI agent,
with exact finite checks and a bounded reference implementation. The new
physical graph and scale assembly have not been compiled in Lean. These are
inverse-gap bounds; complete machine runtime and practical mixing remain open.

The general rational trace allowance improves from `20000d^16` to
**`10000d^16`**, and its dyadic allowance from `40000d^16` to **`20000d^16`**.
The sharper instance bounds are `16p^4V^4` and `32p^4V^4`. More substantial
dimension gains hold for a specified class: a fixed-size nonempty completion
block admits **O(d^8)** for arbitrary aspect ratio, or **O(d^(15/2))** for
bounded aspect ratio, at the smaller self-consistent scales below.

## Count the moves the defect can actually make

Use ordinary equal-total nonnegative integer margins, `m,n>=2`, cutoff `U>=2`,
positive padding, and source capacities that exclude no completion. Let `R,C`
be the large-row and large-column counts, and write

`a=m-R`, `b=n-C`, `A=aC`, `B=Rb`, `p=ab+A+B`.

Assume the positive defect space is nonempty. Then `p>=2`. Small cells have
types SS, LS and SL, with respective counts `ab,B,A`. The effective width is
`V=max(2,1+max_small min(r_i,c_j))`; its [unchanged-graph argument](effective-defect-width.md)
and compiled scalar inequality supply variance coefficient `C_var<=p³V⁴`.

For defect labels `q-x=e_s-e_t`, every doubled-coordinate exchange must
receive at `s` or donate at `t`. Pure x moves preserve every fixed small-row
margin. They have at most `Hrow(s)+Hrow(t)-2` candidates, where Hrow is `n`
on SS/SL and `B` on LS. The subtraction removes self exchanges. Pure q moves
similarly have at most `Hcol(s)+Hcol(t)-2`, with Hcol `m` on SS/LS and `A`
on SL. Caps, donor positivity and ordinary slacks can only remove moves.

A mixed increase is possible only from an LS x coordinate and an SL q
coordinate. Its cancellation candidates number at most
`A*1_(s LS)+B*1_(t SL)-1_(s LS,t SL)`. The last term owns the overlapping
candidate once. Mixed decreases exchange s and t in this formula. Same-cell
mixed moves violate a fixed small-line margin. Add at most one designated
repair edge. The resulting full degree bounds, including DD and DB edges, are:

| Label types | Degree bound |
|---|---:|
| SS, SS | `2(m+n)-3` |
| SS, LS | `n+2m+A+B-3` |
| SS, SL | `2n+m+A+B-3` |
| LS, LS | `2(A+B+m)-3` |
| SL, SL | `2(A+B+n)-3` |
| LS, SL | `2(A+B)+m+n-4` |

Take Q as the maximum over available pairs; a same-type pair needs two cells.
One may also take the minimum with `8p-7`, or with `2(m+n)-3` when the completion rectangle is empty
(`R*C=0`). Constant completion weights do not suffice for that last bound. Q depends on the fixed layout, never on the current state's degree.

In every nonempty mask, **Q<=4p-3**. If SS exists, `p>=m,n` and `A+B<=p`
bound each displayed expression by `4p-3`. If SS is absent, the mask consists
only of LS or only of SL. Its bound is respectively `2(p+m)-3` with `p>=m`,
or `2(p+n)-3` with `p>=n`.

This order and leading constant are nearly attained. For `N>=3`, take an
N-by-3 table, `U=N+2`, `L=3(N-1)`, every row margin U, and column margins
`(N+1,floor(T/2),ceil(T/2))`, where `T=NU-(N+1)`. Precisely the last two
columns are large. On the N small cells choose `q=(2,1,...,1)` and
`x=(1,2,1,...,1)`. Both views have positive donors and ample upper slack.
Each pure-view family has `2N-3` distinct feasible neighbors; the designated
repair is already one of them. Thus the actual degree is `4N-6`, with `p=N`.
For N=3 the source and a neighboring completion count are 208 and 207, so
this is also a genuinely weighted example. The leading `4p` allowance is
nearly sharp.

## The implemented proposal preserves the weighted law

[GeneralDefectChain](../src/contingency115/general_defect_chain.py) scans O(p)
canonical sparse move descriptors. After an initial margin/slack scan, each
candidate's feasibility is checked with constant-size updates. Only the
chosen target profile is constructed. Valid descriptors occupy distinct slots
in a global Q-slot bank, padded with holds. A fixed dyadic denominator
`D=2^ceil(log2(2Q))` gives every actual directed neighbor probability `1/D`.
Using the current degree as the denominator would change the desired law.

The accepted source translation and balanced-star elimination are unchanged
from the [weighted trace proof](general-defect-trace.md). For
`L>=3(R-1)(C-1)` when the completion rectangle is nonempty, each directed
completion test accepts with probability at least one half. Therefore

`K_rational <=4Q C_var <=16p^4V^4`,

`K_dyadic <=2D C_var <=32p^4V^4`.

At `U=5d³`, `p<=d`, `V<=U`, these give the stated `10000d^16` and
`20000d^16` allowances. The uniform exponent remains 16.

The backend caps balanced-star exits after q attempts and holds the original
defect on exhaustion. With completion TV allowance eta, k-bit geometry ranks,
`beta=1/D` and `delta_geom=min(1,5p²/(4*2^k))`, its row error is at most

`Q beta eta + 2 beta [q eta + q delta_geom + 2^-q]`.

The factor `2 beta` uses the proved maximum of two balanced neighbors per
defect. It charges the probability of entering a star. Error from the initial
completion is charged separately. All possible calls, words and declared
oracle work have finite caps; callback accuracy and cooperative work remain
explicit contracts. Local scans and dense-matrix validation are additional
work, and callback CPU time is not certified by its work counter.

The [general repair terminal](../src/contingency115/general_defect_terminal.py)
now implements the [joint-fiber correction](general-defect-output.md), retaining
the completion, checking padding before counting inverse repairs, and using a
finite correction word. Its per-attempt perturbation is at most
`eta_terminal+2^-k_terminal`. Neither component alone supplies endpoint mixing
or a completed outer sampler.

## Smaller scales when the completion block is small

Let `g=RC` and `e_full=(m-1)(n-1)`. The existing
[free padding recurrence](../formal/Math115/PaddingGrowth.lean) and
[count conversion](../formal/Math115/PaddingGrowthAlgebra.lean) give padded
count `P<=2N` whenever marked cells have original incident margins at least U
and `47gL e_full<=32(U+1)`. The
[accepted-edge theorem](../formal/Math115/ReferenceEdgeAcceptance.lean)
requires `L>=3e_large`, with `e_large=(R-1)(C-1)`.

Hence sufficient scales are

`L=max(1,3e_large)`,

`U=max(2,2L,ceil(47RCLe_full/32)-1)`.

The `2L` floor is conservative; the free recurrence does not itself require
it. The ceiling-minus-one ensures exactly the needed inequality for `U+1`.
These scales define a **self-consistent input class**: the actual margins must
have exactly R large rows and C large columns at this new U. Classifying at an
old cutoff and assuming the classification survives is invalid. The new
[scale helpers](../src/contingency115/general_scales.py) check this condition.

For fixed R,C, padding is constant, `U=O(d)`, and the type bounds give
`Q=O(m+n)`. Thus `4Qp³U⁴=O(d^8)` for arbitrary aspect ratio; bounded aspect
ratio gives `Q=O(sqrt(d))` and **O(d^(15/2))**. These are changed-scale
chains, rather than unchanged-graph comparisons with the old ideal cutoff.
For positive margins the joint terminal still has stationary success at least
`c0/(2p²)`, where `c0=max(a(na-1),b(mb-1))`.

## A concrete 2x2 completion block

For `R=C=2`, take `L=3` and `U=max(6,ceil(141e_full/8)-1)`. When `m,n>=3`,

`Q=5(m+n)+|m-n|-19`, `p=mn-4`, `U<=18d`.

An infinite family proves the class is nonempty, including nonsquare tables.
Give all small margins value U-1, one large margin on each side value U, and
the other large row/column margins respectively
`U+max(n-m,0)(U-1)` and `U+max(m-n,0)(U-1)`. Totals agree and precisely two
lines on each side are large. This family has V=U; the new order does not
depend on small margins staying bounded as dimensions grow.

[SmallCompletionOracle](../src/contingency115/small_completion.py) realizes
the remaining completion calls. A 2x2 table is determined by its first entry
in a computable integer interval. Mapping a k-bit word to
`floor(interval_size*word/2^k)` avoids enumeration and unbounded retries. Its
exact per-request TV error is available, with request allowance
`interval_size/(4*2^k)` and uniform declared allowance
`min(1,(max_margin+1)/(4*2^k))`. The implementation also checks finite capacities and
handles unique one-row/one-column completions without random bits.

The `(70,70,1)` square fixture has cutoff 70, padding 3, 351 ordinary tables
and 381 padded tables: ratio `127/117`. Completion weights are 75, 76 and 77;
minimum directed acceptance is `74/75`. Its proposal denominator falls from
128 to 32. This is a real weighted block, not a disguised unit-weight branch.

## Reusing the existing completion program for larger blocks

For general promised nonempty R,C, set instead

`d_local=max(14,R,C,(R-1)(C-1)+1)`, `L=3d_local`,

and use the same guarded cutoff formula. The standalone compiled
[CompletionSamplerSemantics.draw_semantics](../formal/Math115/CompletionSamplerSemantics.lean)
requires `d_local>=14`, `R,C<=d_local`, free dimension at most `d_local-1`,
and residual row/column floors `C*3d_local` and `R*3d_local`. The definitions
and nonnegative ordinary slacks discharge those scalar conditions.

This reuses the generic program's local parameter, not the existing physical
wrapper's outer d. A new physical reindexing/call adapter and encoded trace
composition remain to be supplied. For any fixed block dimensions, padding
stays constant and the O(d^8)/O(d^(15/2)) gap orders persist. For square outer
dimension N and a k-by-k block that stays a proper fraction of it, the envelope
is `O(N^15 k^17)`: if `k=Theta(N^alpha)`, this is
`O(d^(7.5+8.5alpha))`. It interpolates subclass bounds without reducing the
uniform worst-case power 16.

## Evidence and remaining barriers

The degree, scale and local-program arguments received separate AI review.
The [exact report](../reports/shape-defect.json) checks seven actual finite
graphs, compact proposal ownership, the new padding ratio, and a bounded
execution with the real small-completion and terminal implementations.
The execution checks feasibility and accounting; its endpoint accuracy is
unmeasured. Reproduce with:

```sh
python3 experiments/shape_defect.py --output .local/reports/shape-defect.json
```

No universal improvement of the variance powers is established. Uniform
nearest-neighbor paths have variance/energy ratio `(V+1)(V+2)/12`, so their
V² dependence is real. A weighted mixed-mask family attains a quadratic
designated-repair load, blocking a simple replacement of p² by p in that
step. Improving the remaining width and dimension powers needs a stronger
transport argument or a different kernel. The default compiled sampler and
its historical verification receipts remain unchanged.
