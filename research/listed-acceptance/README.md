# Executable list acceptance at arbitrary physical scales

23 October 2026. The existing list acceptance test on the frozen sampler's
actual output now agrees with the physical completion decision at arbitrary
natural cutoff `U` and padding `L`. This closes one pointwise interface
between the completion adapter and the newer trace. It does not yet supply
the trace's bounded transition law.

The [compiled module](formal/ResearchListedAcceptance/Decision.lean) is
`ResearchListedAcceptance.Decision`, with namespace `Math115.ListedAcceptance`.
For a physical state `x`, the old `LatticeSampler.draw` receives the actual
residual row and column lists. On every word of its exact requested length,
the existing `translationValid` Boolean accepts precisely when the signed
translation of that physical completion toward the candidate state is
nonnegative. The reference pair is the first large row and column in computed
list order, matching the [computed-reference trace](../computed-reference-trace/).

| English claim | Lean statement | Hypotheses |
|---|---|---|
| Computed list order preserves the signed nonnegativity predicate. | `translated_nonnegative` | Natural finite margins and arbitrary `U,L`; both computed large-line lists nonempty; actual physical states `x,y` and a completion of `x`. |
| Listed and reference accept/reject decisions agree, including hold. | `listed_completionDecision` | The same source and completion; any optional physical proposal. No adjacency premise. |
| The actual old draw output equals the listed table code. | `draw_listed_code` | Actual source state, both lists nonempty, any natural precision `h`, any word of the exact state-dependent computed length. |
| The executable list Boolean equals the physical nonnegativity test. | `translationValid_draw` | The preceding word/source hypotheses and any physical candidate state. The theorem contains the literal `translationValid` and `LatticeSampler.draw` calls. |
| The actual Boolean branch equals the physical reference decision. | `draw_completionDecision` | Any optional physical proposal and every exact-length completion word, including the no-proposal hold branch. |

There is no `U≥2`, `L≥7`, adjacency, accuracy or positive-original-margin
premise for these correspondence statements. They therefore specialize to
the newer `L=7` construction. Singleton selected rows or columns are included;
empty selected lists are outside this adapter. Source and candidate values
must belong to the actual physical state space at the source capacity.

The physical interpretation still uses the preceding adapter's typed
`Classical.choose` witness and its proved output identity. No new executable
decoder is introduced. The Boolean test is existing executable list
arithmetic; the returned branch here is a physical state. Proposal decoding,
the rational trace clock, conductance-weighted balanced exits, bounded-retry
errors, fresh adaptive words, output correction and the new outer realizer
and costs remain separate. No numerical gap or runtime exponent changes.

## Verification and replay

The [receipt](attempt-02/verification.json) records a clean ordinary Lean
4.34.1 compilation in 90.19 seconds and environment audit in 214.16 seconds.
All 40 module declarations, including nine theorems, were enumerated. Four
full headline closures contain 10,529, 43,787, 43,792 and 43,794 declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The executable
closures contain the actual `LatticeSampler.draw_spec`, adapter output
identity and list-test semantics. All 11,866 imported-object hashes match
accepted receipts, except the newly compiled module's own recorded object.

The initial namespace error is preserved in `attempt-01/`. Its downstream
error-recovery warnings are not part of the accepted environment. The only
source change before the successful compile opens the namespace defining
the intended physical `Fibre`; statements and proofs are otherwise unchanged.
The [diff](attempt-02/proof-only.diff) and scope comparison are retained.
Source and compressed audit bytes are unchanged on publication. The public
receipt uses repository-relative paths; failed diagnostic paths use `<repo>`
and `<packet>`, with trailing whitespace removed.

This additive ordinary compilation trusts the pinned compiler and reused
imports. It is not a default-target rebuild, independent review or strict
Comparator acceptance. Objects and caches are not distributed.

Prepare the pinned compiler, the checked
`ResearchComparison.LegacyPhysicalCompletion` object, upstream
`Transport.ListedReferenceDecision` and `Transport.TranslationDecisionSemantics`,
and the existing `ResearchAudit.EnvironmentAudit`, with their dependencies:

```sh
LEAN_PATH=<prepared-object-roots> bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

`LEAN_BIN` can override the compiler path. The script compiles this module,
runs the environment auditor and checks axioms throughout the headline
closures. It was syntax-checked; the saved run used identical source and
the same compiler options. It does not rebuild or download dependencies.
The repository's `scripts/claims_ledger.py --check-readme` replays the saved
source, exact-type, complete-closure and object-inventory checks.
