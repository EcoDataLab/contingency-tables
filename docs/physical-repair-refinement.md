# Refined repair coefficient on the actual physical chain

The new `Math115.PhysicalRepairRefinement` module retains the existing
`repairWord`, `defectLabels`, source residual-capacity hypothesis, positive-support
identity, and encoding variance identity. It defines a new coefficient rather
than changing the earlier `fullConstant` or its certificates.

Write `p` for the actual number of small cells, `U` for the cutoff, and

```
C_T = U(U+1)/2 * (2 + (p-1)_Nat (U+1)^2/2)
C   = C_T + (sqrt(p^2 C_T) + 1)^2.
```

The refined coefficient satisfies `C <= fullConstant p U`, including `p=0`.
The actual positive-weight physical state variance is at most `C` times the
unchanged full graph energy. The reference completion chain therefore has exact
Poincare coefficient `2 C / beta`; the empty-completion unit branch has
`C / beta`; the existing selected chain is bounded by `2 C / beta`.
Here `beta` is the same source dyadic proposal `smallProposal d`.

For the actual allowance `d = 10 + (card I + 1)(card J + 1) >= 11`, `U >= 2`,
and `p <= d`, the new polynomial envelope is

```
C <= d^3 U^4.
reference / selected coefficient <= 128 d^5 U^4
unit coefficient                 <=  64 d^5 U^4.
```

To check the envelope, `U(U+1)/2 <= 3 U^2/4` and
`(U+1)^2 <= 9 U^2/4` give `C_T <= 27 d U^4/32`.
Young's inequality with parameter `1/d` bounds the refined coefficient by
`[1+(1+1/d)p^2] C_T + 1+d`. Its multiplier is at most `9 d^2/8`,
and its remainder is at most `d^3 U^4/128`. Thus the two contributions are at
most `(243/256 + 2/256) d^3 U^4`, leaving positive slack.
The proof divides only by the positive `d`, so it covers zero defect label
count and zero transversal variance.

The refined repair coefficient together with the tighter polynomial envelope
gives an eightfold improvement of the earlier conservative coefficients `1024`
and `512`. The exact repair refinement alone has an asymptotic factor near two
when the defect multiplier dominates. It changes no exponent for a fixed scale choice,
and supplies no new dense-oracle or finite-bit runtime theorem.

`Math115.ReducedRepairRefinement` specializes the same certificates to the
unchanged dense-compatible cutoff `U=47*d^5` and padding `L=32*d^3`.
Its existing reference, selected, and equal-total feasible chains have
Poincare allowance `(128*47^4)*d^25`; its existing unit branch has
`(64*47^4)*d^25`. These are chain bounds, without adding a finite-bit runtime claim.

`Math115.IdealRepairRefinement` instead specializes the same certificates to
the separate ideal-only cutoff `U=5*d^3` and padding `L=3*d`.
Its existing reference, selected, and equal-total feasible chains have
Poincare allowance `80000*d^17`; its existing unit branch has `40000*d^17`.
The underlying scales remain incompatible with the retained sufficient dense
finite-bit interface. The exponent reduction comes from this separate scale
choice; the repair refinement lowers its coefficient.
