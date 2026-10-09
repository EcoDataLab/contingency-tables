# Physical stationary success at free scales

All three proof modules compiled with the pinned Lean 4.34.1 on
9 October 2026. Their 53 selected declarations passed isolated transitive
axiom audits, followed by the integrated checkpoint's 285-declaration audit.
The [module receipt](../formal/results/stationary-output/verification.json),
[independent source review](../formal/results/stationary-output-review.json),
and [formal ledger](formal-verification.md) retain the exact evidence and scope.

- [`PhysicalStationaryMass.lean`](../formal/Math115/PhysicalStationaryMass.lean)
  bounds the actual physical normalizer.
- [`PhysicalStationarySuccess.lean`](../formal/Math115/PhysicalStationarySuccess.lean)
  proves the successful-pair equivalence.
- [`PhysicalStationaryLaw.lean`](../formal/Math115/PhysicalStationaryLaw.lean)
  connects the actual chain's stationary law to completion and rejection laws.

Let `small = firstPaperSmall r c U`, let `B` be the unchanged source paper
capacity at `U,L`, and let `p` count small cells. Write `N` for the number of
ordinary tables with margins `r,c`, `P` for the number with the source padded
margins, and `Z` for the normalizer of actual positive-weight physical states
(which can be zero without equal total margins). The mass
module proves

$$
Z\le(1+p^2)P.
$$

It retains all completion multiplicities. The physical profiles decompose
into balanced words and positive defects. The source repair map charges at
most one defect per ordered pair of small-cell labels to each balanced
word, giving the `p²` factor. Balanced word/completion pairs inject into
ordinary padded tables. These count statements permit empty fibres and
need no total-margin equation or lower bound on `U,L`.

The successful-pair module uses the literal success test: the small profile
must be balanced, and every large entry of the retained first view must be
at least `L`. Its equivalence identifies successful physical
state/completion pairs with ordinary tables. The inverse pads each original
table on precisely the large cells; the forward map unpads those same
cells. The padding lower bound protects natural-number subtraction.

The law module defines a rational state law from actual completion-fibre
cardinalities and proves its real cast equals the stationary law of the
selected physical chain, in either reference or unit branch. A state draw
from that law followed by an exact uniform completion gives the uniform
law on all physical state/completion pairs, including pairs above defects.
`stationary_trial_mass_real` gives each original table accepted trial mass
`1/Z`, and `stationary_success_probability` proves that the
stationary trial succeeds with probability exactly `s=N/Z`.

For equal ordinary total margins, the earlier constructive nonemptiness
bridge makes `N,Z` positive, including empty row or column types. If `A>0`
and `P≤A N`, then

$$
s\ge\frac{1}{A(1+p^2)}.
$$

At the ideal-only scales `U=5d³`, `L=3d`, the checked ordinary padding count
bound supplies `A=2`. Thus the proved physical stationary success bound
is `1/[2(1+p²)]` (`ideal_stationary_success_probability_lower`), also at least `1/[2(1+d²)]` because `p≤d`.

For `n` independent exact stationary state/completion trials and a fixed
feasible fallback, the bounded retry law is exactly

$$
(1-(1-s)^n)\operatorname{Uniform}+(1-s)^n\delta_{\mathrm{fallback}}.
$$

Its total-variation distance from the uniform ordinary-table law is at most
`exp(-n/[A(1+p²)])`. Equal accepted point masses also establish uniformity
of the output conditional on a successful stationary trial. The fallback
mixture is relevant for bounded retries even when every successful trial
has the correct law.

The [stationary-rejection obstruction](stationary-success-obstruction.md)
shows that this quadratic dependence on `p` is necessary in worst-case order
for the unchanged rule, already at the smaller ideal scales. It is a
separate reviewed counting argument with exact finite examples.

These are stationary-law and independent-trial results. They do not assert
mixing from an arbitrary initial state at arbitrary `U,L`, implement the
finite-bit completion oracle, account for an approximate terminal draw,
construct the complete correction program, or establish its machine cost.
The subsequent [finite-walk proof](physical-finite-walk.md) combines these
stationary inputs with the ideal `d¹⁷` chain bound, giving an output-error
guarantee for independent restarted finite walks and exact completions.
Additional cell constraints or structural zeros require separate feasibility
and sampling guarantees.

The [module receipt](../formal/results/stationary-output/verification.json)
retains direct compilation commands, source hashes, diagnostics, and isolated
audits. The [integrated log](../formal/results/fifth-checkpoint.log) records a
fresh aggregate compilation and both complete selected-declaration audits.
These checks use existing dependency outputs; they are not a fresh full
dependency rebuild or strict Comparator replay. The pinned upstream source
is unchanged.
