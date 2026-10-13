# A zero-range comparison for a unique-completion subclass

For a restricted ordinary-margin family, the accepted defect trace has inverse gap

\[
\tau_D\le Q\left[1+2C\min(p,H)(1+H/p)^2\right]
       \le 4p+16CH(H+p),\qquad Q=4p-3.
\]

Here \(C\) is a universal constant from Ben Morris’s complete-graph zero-range theorem; no numerical value is extracted. At the cutoff \(U=11dp\) described below, this is \(O(d^4)\). The result is a mathematical derivation reviewed by two AI agents, with no human review claimed. The external theorem and this subclass comparison are not Lean-formalized.

This family already admits exact independent weak-composition sampling: choose the \(p-1\) separator positions uniformly among \(H+p-1\) positions, then fill the unique dense completion. The comparison is useful for understanding how actual graph geometry can remove losses in the generic repair argument; it is not a practical sampling recommendation or a new bound for general weighted completion blocks.

## The actual ordinary-margin family

Take \(p\ge2\) rows and two columns, with equal natural-margin totals. Every row margin \(r_i\) is at least \(U\ge2\). One column has margin \(H\), where \(1\le H<U\); the other column is large. Use padding \(L=7\) and the usual capacities dominating residual totals. The small mask consists exactly of the first column.

Write the two small views of a physical state as \(x,q\). The fixed small-column margin gives \(\sum_iq_i=H\). Balanced or single-defect occupancy gives \(\sum_ix_i=H\) too. Thus both views are weak compositions of \(H\) into \(p\) entries. Conversely, every pair with \(x=q\) or \(q-x=e_s-e_t\), \(s\ne t\), is feasible: each coordinate is at most \(H<U\), and \(r_i-x_i\ge U-H\ge1\).

The dense residual rectangle is \(p\)-by-1. Its unique completion has entries \(r_i-x_i+L\). The source translation sends this completion to the unique target completion, whose entries are positive. Therefore every retained physical weight and every valid edge’s accepted conductance is exactly one.

A defect \((x=A,q=B)\), with \(B=A+e_s-e_t\), has exactly two balanced neighbors: a transfer in \(q\) reaches \(A\), and a transfer in \(x\) reaches \(B\). Its designated repair also reaches \(A\), so adds no new edge. Mixed moves change the fixed \(q\) column sum and are infeasible. There are no balanced-to-balanced edges. Defect-to-defect edges remain part of the full graph.

For a balanced composition \(A\), each positive donor and each of the \(p-1\) other sites gives two distinct defect neighbors. Hence

\[
S_A=2(p-1)\operatorname{supp}(A),\qquad a_x=2,
\]

where \(S_A\) is the total accepted conductance around \(A\), \(a_x\) is that from a defect to balanced centers, and \(\operatorname{supp}(A)\) counts positive entries.

## The zero-range graph and its rate

Let

\[
J_{AB}=\sum_x\frac{c_{Ax}c_{Bx}}{a_x},\qquad A\ne B,
\]

with \(c\) the actual accepted conductances. Each unit-transfer pair \(A,B\) has precisely two defects, \((A,B)\) and \((B,A)\), each contributing \(1/2\). Thus \(J_{AB}=1\) on unit-transfer pairs and zero otherwise.

This is the configuration graph of the constant-rate zero-range process on the complete graph with \(p\) sites and \(H\) particles. Morris’s convention is that each occupied site expels a particle at rate one, choosing uniformly among the \(p-1\) other sites. His Theorem 3 bounds its continuous-time relaxation by \(C(1+H/p)^2\). [Ben Morris, *Annals of Probability* 34(5), 1645–1664 (2006), Theorem 3 and the rate convention in Sections 1–2](https://arxiv.org/pdf/math/0405161).

Let \(N\) be the number of balanced compositions, and define the unordered energy

\[
E_J(F)=\sum_{\{A,B\}}J_{AB}(F_A-F_B)^2.
\]

The normalized zero-range Dirichlet energy is \(E_J/[N(p-1)]\), while uniform normalized variance is \(\operatorname{Var}_{\rm unit}/N\). Cancelling \(N\) in the spectral inequality gives

\[
\operatorname{Var}_{\rm unit}(F)
 \le\frac{C(1+H/p)^2}{p-1}E_J(F).
\]

Evaluate the unnormalized \(S\)-variance at the uniform mean and use \(\operatorname{supp}(A)\le\min(p,H)\). Then

\[
\operatorname{Var}_S(F)
 \le2(p-1)\min(p,H)\operatorname{Var}_{\rm unit}(F)
 \le K E_J(F),\qquad
K=2C\min(p,H)(1+H/p)^2.
\]

## Accepted-star energy and the actual defect trace

For a defect observable \(g\), assign each balanced center its harmonic value

\[
h_A=\frac{\sum_{x\sim A}c_{Ax}g_x}{S_A}.
\]

The exact incidence-variance identity is

\[
\operatorname{Var}_a(g)=E_{\rm star}(g)+\operatorname{Var}_S(h).
\]

Here \(a_x=2\) and defect weights are one, so the left side is \(2\operatorname{Var}_{{\rm unit},D}(g)\). Minimizing \(\sum_{A\sim x}c_{Ax}(h_A-v)^2\) separately at every defect shows \(E_J(h)\le E_{\rm star}(g)\). Consequently

\[
\operatorname{Var}_{{\rm unit},D}(g)
 \le\frac{1+K}{2}E_{\rm star}(g)
 \le\frac{1+K}{2}E_{\rm trace}(g).
\]

The trace energy includes every actual defect-to-defect edge, in addition to the eliminated balanced stars. Its off-diagonal conductance is

\[
t_{xy}=\mathbf1_{\{x,y\}\text{ is a defect edge}}
       +\sum_{A\sim x,y}\frac1{S_A},\qquad x\ne y.
\]

At a defect with labels \(s,t\), a valid pure \(x\) transfer must receive at \(s\) or donate at \(t\), giving at most \(2p-3\) targets. The pure \(q\) transfers give at most \(2p-3\) more. Mixed moves are infeasible and the repair is already counted, so full defect degree is at most \(4p-6\). Thus \(Q=4p-3\) is a valid allowance and \(\sum_{y\ne x}t_{xy}\le Q\).

Set \(\beta=1/(2Q)\), use \(P_D(x,y)=\beta t_{xy}\), and put the remaining mass on the diagonal. This is the actual half-lazy symmetric trace, with uniform stationary law on defects. It is connected because unit transfers connect all compositions, each transfer has shared defects, and every defect is attached to its two centers. Its normalized variance and energy are respectively \(\operatorname{Var}_{{\rm unit},D}/|D|\) and \(\beta E_{\rm trace}/|D|\). Cancelling \(|D|\) gives

\[
\tau_D\le\frac{1+K}{2\beta}=Q(1+K).
\]

There is no completion-acceptance penalty or ratio of full-state to defect-state normalizers. A dyadic slot rate between \(1/(4Q)\) and \(1/(2Q)\) gives at most twice this bound.

## Arithmetic, cutoff and transpose

Since \(Q\le4p\) and \(\min(p,H)(H+p)\le2Hp\),

\[
Q\left[1+2C\min(p,H)(1+H/p)^2\right]
 \le4p+16CH(H+p).
\]

For arbitrary \(U\), this is the stated bound: \(H<U\) alone does not imply \(O(U^2)\) if \(p\) is much larger than \(U\). At the current shape-dependent cutoff for this \(m\)-by-2 family,

\[
m=p,\qquad d=10+(m+1)(2+1)=3p+13,\qquad U=11dp.
\]

Then \(p\le U\), giving \(O(U^2)\); also \(U\le11d^2\), giving \(O(d^4)\). One conservative conversion is \(\tau_D\le(4+2112C)d^4\). The constant still depends on the universal, unextracted \(C\); this is not an explicit encoded sampling schedule or runtime bound.

The whole transpose has two rows, one small row of total \(H\), and \(p\) large columns, with a unique 1-by-\(p\) completion. Transposing the cells and swapping \(x,q\) preserves all physical states, defect-to-defect and balanced-to-defect edges, unit accepted conductances and the trace kernel. The designated repair can choose the other balanced endpoint, but both endpoints are already exchange neighbors. The same bound therefore applies to the full transposed family.

The case \(H=0\) has no defects and belongs to a separate direct-completion branch. Multiple small columns, small rows in the original orientation, or a completion rectangle with at least two rows and two columns are outside this result.
