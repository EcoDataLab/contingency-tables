# Independent correctness review, 6 November 2026

This bounded review started from commit
`7a7aa8ac8a7f80a870dbf1db1958feb2ce49b230`. Separate AI workers inspected
contracts and source, constructed new counterexamples and exact finite oracles,
then used the existing tests as additional regression checks. A separate AI
reviewer challenged proposed repairs. This is not a human review, a universal
correctness proof, or a complete strict Comparator replay.

## Defects reproduced and repaired

| Defect | Concrete consequence | Correction and remaining boundary |
|---|---|---|
| Weighted integer-source validation | Negative, Boolean and fractional `randrange` results silently selected feasible tables. | Exact and cactus weighted samplers share integer/range validation. Every valid integer retains the same selection. This concerns malformed RNGs, not a demonstrated wrong law for valid RNGs. |
| Shared preparation budgets | A factor using the remaining allowance caused a later factor needing zero work to be rejected. Relabeling factors changed acceptance. | Zero remaining allowances are permitted when the actual preflight plan needs zero. Positive work still fails before coefficient evaluation; zero-mass proofs are supported. |
| Hypergeometric quantile equality | Rows `(2,14)` and columns `(3,13)` have exact `F(1)=39/40`; the rounded CDF returned upper quantile 2 instead of 1. | Totals at most 1024 use integer combinatorial CDF comparisons. Larger inputs retain explicitly documented binary64 limitations; PMF reporting remains numerical. |
| R observation serialization | Valid integer 100000 was emitted as `1e+05`, which Python's integer parser rejected. | R emits supported integer observations in decimal notation. Native single-output cases cover large first cells and metrics. |
| Serial-result framing | Tail truncation could turn an interior substring or terminal-control payload into an apparently anchored success marker. An unfinished result token could also be accepted too soon. | The [tail repair](../strict-sampler-checkpoints/runtime-tail-v1/) preserves framing, waits for completed lines and refuses ambiguous truncated control sequences. It has no native supervisor replay yet. |
| Serial-phase ordering | Taking only the last phase hid backward transitions within a batch or across a trimmed boundary. | The same repair distinguishes retained events from new events and checks each new transition against the prior phase. |
| Comparator output allocation | The observer reread the entire already-saved stdout log into one Python string. | The [output repair](../strict-sampler-checkpoints/runtime-output-v1/) scans bounded chunks for the exact acceptance phrases; raw logs and hashes remain preserved. The returned Comparator stdout is explicitly a marker summary. |
| Named-audit stderr | A zero-exit fake compiler with valid axiom stdout and unexpected stderr passed the named-output check. | Both output streams now reach the existing parser. This fixes the output-validation boundary; it is not evidence that a saved theorem is false. |
| Audit cancellation cleanup | Timeout or cancellation could leave an owned compiler descendant running. | POSIX runs use an owned process session and terminate that group on timeout or escaping exceptions. CLI SIGTERM enters cleanup and exits 143. Imported callers own their signal handlers; Windows cleanup remains limited to the direct child. |

The parser repair was revised after independent counterexamples defeated the
first candidate, including an OSC payload containing both success markers and a
phase reversal hidden after an older marker left the tail. The final tests
retain these cases. The raw log and acceptance requirements were not replaced
with a weaker checking mode.

## Independent finite checks

The scripts below derive expected values directly from cell boxes, margin
equations, factorial weights, finite random words, probability identities or
separately convolved distributions. They are standalone review artifacts, not
additional default-suite discovery. Some seeded cases have empty fibers; case
counts do not imply that every case is a distinct nonempty distribution.

| Script | Checked scope |
|---|---|
| [Completion oracles](check_completions_independent.py) | 2,200 bounded problems; rank bijections and exact weighted laws under both orientations; 2,340 small-completion word/precision cases; 27 tiny lattice plans and their accepted preimages. |
| [Block articulation oracles](check_block_articulations.py) | 150 support/bound cases, 300 weighted cases, fixed positive chords and articulation vertices; eight complete sampling decision trees with 1,823 nodes. |
| [Markov oracles](markov_independent_audit.py) | Physical-state and neighbor graphs from integer equations, completion rejection and detailed balance, terminal preimages, periodic/disconnected diagnostics, and all 15,625 symmetric 3-by-3 integer PSD cases with entries from -2 through 2. |
| [Weighted law and optimization oracles](weighted_oracle.py) | Complete tiny urn laws, cactus weights and signed linear extrema against direct Cartesian enumeration. |
| [Support and transport oracles](extra_oracles.py) | Zero/rational activities and lower bounds, transport ownership on both edges and non-edges, direct cut/variance identities. |
| [Arithmetic oracles](arithmetic_oracles.py) | 2,500 rational logarithm cases; 225 literal finite-word offset laws; 3,000 least domination precisions; Bernoulli convolution, direct padded-table counts and rational growth bounds. |
| [Report oracles](experiment_oracles.py) | Independently supplied timing/count observations, 936 closed-interval score identities, and an offline replay of the pinned commuting panel. |

The commuting replay changes no saved interval, coverage indicator or summary.
Its smallest total is 6356, above the new exact-quantile domain. Historical
reports and verification receipts retain their original bytes.

From the repository root, after installing the documented test environment:

```sh
make test
PYTHONPATH=src .venv/bin/python research/correctness-review-2026-11-06/check_completions_independent.py
PYTHONPATH=src .venv/bin/python research/correctness-review-2026-11-06/check_block_articulations.py
PYTHONPATH=src .venv/bin/python research/correctness-review-2026-11-06/markov_independent_audit.py
PYTHONPATH=src .venv/bin/python research/correctness-review-2026-11-06/weighted_oracle.py
PYTHONPATH=src .venv/bin/python research/correctness-review-2026-11-06/extra_oracles.py
PYTHONPATH=src .venv/bin/python research/correctness-review-2026-11-06/arithmetic_oracles.py
PYTHONPATH=src .venv/bin/python research/correctness-review-2026-11-06/experiment_oracles.py
```

The [validation record](validation.json) binds these scripts and the local
verification result. Passing these bounded oracles does not establish arbitrary
input performance, native numerical accuracy, correctness of every application
model, or absence of further bugs.

## Formal verification remains separate

No mathematical theorem or inverse-gap exponent changed. The expanded ordinary
main build was interrupted at a module boundary: 325 baseline modules have full
bookkeeping, and module 326 compiled successfully before scheduler interruption.
The baseline audit and 118-source integration stage did not run. Completed
artifacts and the incomplete receipt were preserved; this is no aggregate pass.

The strict source bundle includes the metadata lifetime, serial framing and
bounded-output repairs. It remains a source-only candidate for the historical
679-module target. Fresh native preparation, the intended longer execution
profile, complete compilation, export, default-kernel replay and Comparator
acceptance remain outstanding. The newer ordinary sampler and its remaining
encoded-cost interface retain their separately documented scope.
