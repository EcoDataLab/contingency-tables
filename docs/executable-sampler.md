# Executable all-input table sampler

`rawHybridSamplerCode xs ys t word` is a complete ordinary Lean program on natural margin lists and a supplied Boolean word. It computes the branch, initialization, schedule, actual corrected trials, retries, fallback and original zero positions. The caller supplies no semantic state, table, completion, defect labels or acceptance count.

For equal-total margin lists, the contract identifies a computed width and a table-valued interpretation of this same program on every word of that width. Every output is feasible, and uniform independent fair bits give total variation at most `2^-t` from uniform ordinary tables on the original ordered lists. This includes zero margins, zero totals, empty lists and `t=0`.

The combined [public contract source](../research/physical-trace-general-executable-sampler/formal/ResearchPhysicalTraceJoin/GeneralExecutableSampler.lean) passed ordinary compilation and the full assumption audit in [attempt-02](../research/physical-trace-general-executable-sampler/attempt-02/verification.json). Its proof connects the fixed ordinary program to the existing checked hybrid sampling law.

## Inputs and output contract

The operational interface is

```lean
rawHybridSamplerCode (xs ys : List ℕ) (t : ℕ) (word : List Bool) : MatrixCode
rawHybridWordWidth   (xs ys : List ℕ) (t : ℕ) : ℕ
```

The program checks `xs.sum = ys.sum` internally. Equal totals are the sampling theorem's only condition on the margins; they need not be positive. Unequal totals return the empty matrix code and have no sampling guarantee.

The theorem concerns a **full word of exactly the computed width**. It certifies a table-valued function `sample` whose encoded output equals `rawHybridSamplerCode` on every such word, together with the uniform-word error bound. The raw function is total on arbitrary Boolean lists, but its correctness and accuracy contract uses the stated full-width words. It does not generate randomness or provide a streaming random-bit driver. At `t=0`, feasibility still holds pointwise and the stated error bound is `1`.

Stable positive filtering retains repeated values and their positions. All scales, catalogs and branch tests are recomputed on those lists. Literal matrix restoration then inserts the original zero rows and columns in their original order.

| Computed reduced branch | Program used | Reserved width |
|---|---|---|
| Deterministic | Greedy feasible reduced table, then zero restoration | `0` |
| Reference | Initialized stronger trace, retained completion, repair, padding test and bounded correction | `rawPositiveWordWidth xs ys t` |
| Unit or no-small | Existing complete `LatticeSampler.draw`, then zero restoration | The frozen backend's computed `totalBits` |

The legacy backend rebuilds its own scales. Its internal branch need not match the newer classifier. The new trace is used on every input tagged reference by the recomputed positive-list classifier.

## The actual reference program

A greedy reduced table supplies the feasible fallback. The checked finite search constructs the starting defect's encoded profile. Raw ordered neighbor selection, accepted steps, balanced exits and the joined walk then operate on the stored profile lists. Their pointwise equations preserve the same word splits as the typed sampling proof.

The terminal call computes its residual margins from the reached state and runs the frozen completion program. Full source-row reconstruction preserves the sampled dense entries, including entries below the padding. Ordered defect labels are extracted from both stored profile views through the existing label test. The program repairs the retained matrix, tests the repaired large entries, unpads successful output, counts actual inverse labels and applies the separate bounded-bit correction coin. Padding failures and coin rejection remain `none` on exactly the same word as in the typed trial.

Each retry starts from the same initialized defect and receives its own consecutive complete trial block. The first successful result is selected; a successful value equal to the fallback still counts as success. Exhaustion returns the original greedy fallback. The reference retry code takes the first `R*q` bits before chunking, so surplus bits cannot create additional attempts.

The current retry primitive **maps the trial over the complete block list before selecting the first successful result**. Its first-success output equation does not establish early return, fewer inspected bits or an expected-cost bound for this implementation. The supplied full bank reserves all attempts.

## Current schedule and separate alternatives

The executable program currently uses the established linear outer schedule and old uniform completion reservation. With reduced dimensions `m,n`, small-cell count `p`, small-row/column counts `a,b`, and `d=10+(m+1)*(n+1)`, its reference settings are

```text
U  = 11*d*(m+n-2),  L = 7
c0 = max(a*(n*a-1), b*(m*b-1))
s  = c0 / (2*p*(p-1))
A  = min(2*p*(p-1), 4*p)
R  = A*(t+1)
H  = t+2+clog2(R)
q  = rawTerminalScheduleWordWidth(reduced margins,U,7,H) + H
reference bank = R*q
```

Both corrected-trial precisions are `H`. Here `s` is the proved success allowance, a lower bound on actual ideal trial success. The current uniform completion bound uses the power-85 allowance from `GeneralScheduleCode`; it is reserved repeatedly inside exits and across the walk. [The complete reservation comparison](reservation-comparison.md) records why these banks can be enormous even after improving the chain gap and outer retry count. No practical speedup follows from the code correspondence alone.

The following checked alternatives are separate from this program's selected settings:

| Alternative | Checked result | Current integration boundary |
|---|---|---|
| [ShapeSchedule](../research/physical-trace-general-shape-schedule/) | Retains `c0`; the block is exactly `ceil(2*p*(p-1)/c0)` on reference inputs, with a proved dyadic budget | Standalone alternative schedule; the program above still uses `A` |
| [Tighter completion budget](../research/physical-trace-general-completion-tight-budget/) and [TightWidth](../research/physical-trace-general-tight-width/) | Completion/step/terminal reservations no larger than the old widths, with exact preservation of the actual joined and terminal laws | The program above still uses the old uniform banks |
| [Augmented numerator](../research/physical-trace-general-augmented-lower/) | `max(c0,p-1)` is a valid inverse-count lower bound; the separate numerator law gives ideal success at least `1/(2p)` at actual reference scales | The current coin, success allowance and scheduler still use `c0` |

The exact ceiling is the least integer satisfying its product-cover certificate. That is not an optimal-retry or runtime claim. The selected program continues to use the linear retry schedule, old uniform banks and original numerator.

## English and Lean contract

All names are in `Math115.PhysicalTraceJoin`.

| English claim | Lean statement | Main hypotheses and status |
|---|---|---|
| Complete ordinary program has computed width, feasible output on every full word, and TV at most `2^-t` | `executableSampler_contract` | `xs.sum = ys.sum`, natural `t`; passed |
| Computed branch width equals the proved hybrid width | `rawHybridWordWidth_eq` | Equal original totals; natural `t`; passed |
| Every full-word raw output equals the encoded typed table output, across all branches | `rawHybridSamplerCode_eq` | Equal original totals; a word of the selected width; passed |
| Reference initialization, fallback, schedule and restoration agree pointwise | `rawPositiveReferenceWordCode_eq` | Equal totals, computed reduced reference tag, full reference word; passed |
| Literal retries preserve first-success output and all-failed fallback | `rawCorrectedRetryCode_eq` | Equal reduced totals, both large lists, actual start/fallback, positive trial width and complete retry word; passed |
| The actual raw corrected trial preserves repair and rejection on the same word | `rawCorrectedTrial_eq` | Equal reduced totals, both large lists, actual defect start and full trial word; passed |
| Legacy and deterministic raw outputs agree with their proved backends | `rawPositiveLegacyWordCode_eq`, `rawPositiveDeterministicWordCode_eq` | Equal original totals; matching reserved word, including zero-bit deterministic output; passed |

Component theorem inputs such as an actual start or residual matrix are discharged inside the complete program. The endpoint has no supplied start, fallback, branch, success probability, counting premise or outer-budget choice. The contract’s `Table`-valued interpretation certifies feasibility on every full word.

## Verification and remaining work

The whole-program composition and public contract passed ordinary Lean 4.34.1 compilation and full module/headline audits. The contract's complete headline closure contains 45,911 declarations and uses only `propext`, `Classical.choice` and `Quot.sound`. Source-bound packets retain successful sources, failed candidates, diagnostics, compiler/object hashes and accepted-import receipts. The pinned compiler and reused objects remain trusted.

| Packet | Exact passed receipt |
|---|---|
| [Ordinary program composition](../research/physical-trace-general-program-code/) | [attempt-03](../research/physical-trace-general-program-code/attempt-03/verification.json) |
| [Combined executable contract](../research/physical-trace-general-executable-sampler/) | [attempt-02](../research/physical-trace-general-executable-sampler/attempt-02/verification.json) |
| [Optional tight-width adapter](../research/physical-trace-general-tight-width/) | [attempt-03](../research/physical-trace-general-tight-width/attempt-03/verification.json) |

The new operational definitions are ordinary compiled Lean functions. Their semantic correspondence proofs can use noncomputable mathematical witnesses and standard classical axioms. This closes the ordinary list-program composition obligation. A composed encoded `Realizer`, charged machine-time theorem and new runtime exponent remain open. This checkpoint also does not extend historical hosted Linux builds or strict Comparator receipts. The existing complete encoded `d^17` sampler and its runtime certificate are unchanged.

The [separate AI source/receipt review](../research/physical-trace-general-executable-sampler/AI-SOURCE-REVIEW.md) records the exact checked sources and semantic boundaries.

The earlier [typed hybrid specification](hybrid-finite-word-sampler.md) describes the probability construction. [Component correspondences](sampler-code-correspondence.md) and the [source dependency replay](../research/repair-accept/INTEGRATION-REPLAY.md) record the interfaces reused here.
