# Completion at constant padding using the frozen complete sampler

11 October 2026. The already compiled complete d¹⁷ sampler supplies accurate
completions for the new outer `L=7` construction. Its contract accepts arbitrary
equal-total natural margins; its own internal padding is independent of the
outer padding. This closes mathematical backend availability. The new physical
adapter and complete encoded composition remain to be implemented and checked.

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

The remaining adapter must instantiate the arbitrary-`U,L` listed-fiber
equivalence, reindex the selected lines to `Fin R` and `Fin C`, and transport
the old draw law through that bijection. Existing `equivLaw_uniform` and
`variation_equiv` preserve uniformity and total variation. The old
`ListedLatticeCompletion` abbreviations fix older outer scales and cannot
be reused unchanged. A valid empty block has a unique completion and needs
no random bits.

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

Separate AI source reviews checked this bridge against the old sources, which
match the successful complete-sampler checkpoint. The new residual cap module
has fresh compilation evidence. The proposed full wrapper has not been
compiled; it is deliberately excluded from the public Lean proof claims.
