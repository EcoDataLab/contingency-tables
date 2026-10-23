# Completion at constant padding using the frozen complete sampler

Updated 23 October 2026. The compiled complete d¹⁷ sampler supplies accurate
completions for the new outer `L=7` construction. Its contract accepts arbitrary
equal-total natural margins; its own internal padding is independent of the
outer padding. A new [compiled physical adapter](../research/legacy-physical-completion/)
now closes the actual residual-input and completion-law interface for the
both-large branch at arbitrary `U,L`. Complete encoded composition remains open.

## Existing executable contract

[`LatticeSampler.draw_spec`](../formal/Math115/LatticeSampler.lean) identifies
the executable `LatticeSampler.draw` output, for every reserved word, with a
feasible ordinary table. For a uniform word of exactly the computed length
`q=totalBits((rows,columns),k)`, its law has total variation at most `2^(-k)`
from uniform. The only margin premise is equality of natural totals. Zero
margins, singleton dimensions and empty dimensions are covered.

The draw returns the typed nested-list matrix code, avoiding the public flat
output parser. The new sampler can call this frozen program as a subroutine:

```
new outer sampler → frozen complete d17 sampler → frozen dense completion
```

This is acyclic. The old sampler never calls the new outer algorithm. Its
module identity must remain fixed when the new implementation is assembled.
It is an executable formal program, not yet a Python completion callback.

## Actual residual inputs and redundant caps

Let the original total be `M`, and let `R,C` be the selected large-line counts.
Every actual balanced or defect physical state at padding seven satisfies

```
M_request ≤ M + 7RC,
d_request = 10+(R+1)(C+1) ≤ d_outer.
```

The residual total and cap statements are separately compiled in the
[research packet](../research/retained-root/). The existing physical completion
theorems provide nonnegative, equal-total residual margins. A cap at least
`M+7RC` is redundant because every entry is at most the whole table total.
The source cap `M+dL+U+2` meets this condition. Restrictive cell bounds would
change the target law and are outside this bridge.

`Math115.LegacyPhysicalCompletion` now instantiates the arbitrary-`U,L`
listed-fiber equivalence, reindexes the selected lines to finite coordinates,
and transports the old draw law through that bijection. Its row and column
code lemmas identify the actual physical residual inputs; `completionDraw_code`
identifies the old executable output for every exact-length word.
`completionLaw_accuracy` proves TV at most `2^(-h)` on the physical fiber,
and `oracleFamily_accuracy` gives the same bound for every reference-line pair.
Neither accuracy nor cap redundancy is an assumption. The proof requires an
actual positive physical state and both computed large-line lists nonempty.
Singleton blocks are covered. The old `ListedLatticeCompletion` remains fixed
to its older scales. A valid empty block has a unique completion, but its new
executable branch is not included in this adapter.

## Remaining interface to the canonical defect trace

The new trace and the adapter share the physical residuals, capacity and
completion-translation `acceptedCount` algebra. The missing next interface is
the law of an actual bounded transition on defects. For distinct defects
`d,e`, the canonical theorem uses

```
P(d,e) = [W(d,e) + sum_b S(b,d) S(b,e)/s_b] / [2(4p-3) w(d)],
s_b = sum_f S(b,f).
```

Zero-star terms contribute zero. Here `W` counts accepted defect-to-defect
conductance, `S` counts accepted balanced-to-defect conductance, and `w` is the
completion-count weight.
The old `selectedTransitionLaw` walks on the full state space with a different
dyadic proposal clock. It is not this trace. A transition proof must identify
the weighted exit `S(b,e)/s_b`, charge capped exit failures and approximate
completion errors, and use the correct rational clock or certified dyadic
rounding. Uniform neighbor exits would give the wrong law.

The [computed-reference packet](../research/computed-reference-trace/) now
closes the reference-choice obligation by constructing the trace and proving
the aggregate bound for every fixed large reference pair. Its computed
specialization uses the same first large lines as the completion adapter.
It retains the exact clock and weighted exits; no equality between different
reference kernels is assumed. The [list acceptance packet](../research/listed-acceptance/)
also closes the pointwise decision correspondence at arbitrary `U,L`. Its
`translationValid_draw` identifies the actual list Boolean on the old
sampler's matrix output, and `draw_completionDecision` identifies the
accept/reject branch for every exact-length word and optional physical
proposal. The no-proposal hold and singleton selected blocks are included.
Neither adjacency, a padding lower bound nor accuracy is assumed for this
identity. Both computed large-line lists remain nonempty.

The remaining local obligation is the bounded transition law: implement the
proposal clock and weighted exit distribution, then account for capped exit
failure and approximate completions. Pointwise acceptance alone supplies
neither that distribution nor its error budget.

A [compiled weighted-retry helper](../research/weighted-exit/) now supplies
the local first-success algebra. If the ideal trial at a fixed balanced
state has mass `ρS(b,e)/w(b)` and the actual trial differs by at most `δ`,
`J` fresh fixed-width trials have error at most `(1−ρs_b/w(b))^J+Jδ` from
`S(b,e)/s_b`. Its actual `flatRetry` uses exactly `J*k` bits.

The [physical one-trial packet](../research/physical-star-trial/) now derives
those mass and accuracy facts for the actual computed proposal, frozen
source completion draw and literal list test. Its uniform word has length
`clog2(32d²)+q_b(h)`, and trial error is at most `2^-h`. Rational accepted
counts and the source completion count cast to this trace's `S(b,e)` and
`w(b)`. The first-success specialization, positive-star and useful success
bounds remain to compile; zero stars need a separate branch. The old proposal
rate cancels within the ideal successful exit law but does not identify the
incoming trace clock.

After that transition interface, the program still needs fresh adaptive words,
initialization and mixing, the defect-law repair/padding/output correction,
retry schedules, zero-margin and degenerate branches, and encoded costs.
The existing general output correction assumes positive original margins;
the trace theorem permits zeros. These obligations must close before the gap
bound can be carried into a complete sampler theorem.

## A uniform reservation for adaptive calls

Suppose a new outer program has a proved cap `H≥1` on all completion calls,
including failed attempts and terminal requests. With common precision `k`, set

```
C0 = 12672000000 · 37^62
M_star = M + 7RC
N_star = d_outer + clog2(M_star+2) + k + 3
W_star = C0 · N_star^85.
```

The existing `reservedBits_combined` theorem bounds every request's exact
word length by `W_star`. Reserve `H` disjoint blocks of that width, and pass
the requested prefix of the next fresh block to each draw. Requests may depend
on earlier outputs; conditional on that past, the next block remains uniform.
The pinned prefix-word law therefore retains the `2^(-k)` error guarantee.
Independent outputs are neither asserted nor required.

The whole backend reservation is at most `H W_star`, including unused bits.
Choosing `k=h_out+clog2(H)+2` bounds the cumulative completion error by
`H·2^(-k)≤2^(-h_out-2)`. Initial-law, mixing, terminal correction and retry
exhaustion errors still need their own allocations. No new compiled outer
call-cap or adaptive composition theorem is claimed here.

## Complete cost and present evidence

The old fixed physical machine has an existing bound

```
Time_old ≤ C_old · S_request^D_old,
D_old = D from the explicit complete-degree certificate.
```

The [complete degree packet](../research/runtime-degree/checkpoints/complete-explicit-degree-v1/)
now fixes D as a literal natural expression with 4,137 decimal digits. Its
coefficient C_old remains existential. The same constants work for every residual request. Thus its
subcalls cost at most `H C_old S_star^D_old`, where
`S_star=m+n+clog2(M_star+1)+k+1`. Constructing and interpreting the new outer
program, reindexing, copying outputs, and materializing or skipping the larger
common blocks require additional charges. The old machine bound already
covers its own requested word bank, not those extra outer operations.

This gives a potentially costly but valid route to polynomial completion
composition. It does not establish a smaller complete runtime exponent or
implement the new outer sampler; the seven old-machine draw certificates are now closed. The [common-size comparison](composed-complexity.md)
continues to compare the already compiled machines separately.

The [adapter packet](../research/legacy-physical-completion/) has a fresh
ordinary Lean compilation and four full headline dependency-closure audits,
with only standard axioms. A separate AI reviewer checked its frozen source
and saved evidence. The semantic witness is tied pointwise to the executable
old draw; it does not itself implement the physical decoder or revised outer
program. Adaptive reservation and complete composition above remain proposals.
