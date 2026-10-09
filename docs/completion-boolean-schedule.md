# Both-branch Boolean law and computed schedule

This component checkpoint verifies **134 declarations** across three modules:
`PhysicalReferenceBoolean` has 16 strict named audits,
`LatticeScheduleProgram` has 105, and `PhysicalBooleanSampler` has 13. Together
they supply the ideal-scale mathematical finite-word experiment in both
branches, its scheduled output accuracy, and the ordinary list program that
computes its schedule and reserved widths. The numeric schedule computation
has a polynomial TreeTyped cost proof; the complete encoded walker and public
random-machine runtime remain separate.
The [receipt](../formal/results/completion-boolean-schedule/verification.json)
records the exact sources, objects, logs, input snapshots and scope.

These names are disjoint from the 869-declaration aggregate, the 46 encoded
completion-program declarations, and the 193 physical-bridge declarations.
They remain a separate component checkpoint. The fresh focused Linux result
at `895b45c` still audits 863 names; it does not certify these 134 additions.

## An exact reference-branch word experiment

Let `r : Fin m → ℕ` and `c : Fin n → ℕ` have equal totals. The reference
experiment also requires both computed large-index lists to be nonempty at
`U=5d³`, where `d=10+(m+1)(n+1)` and `L=3d`. The reference module proves this branch under explicit nonempty-list
hypotheses. The third module below supplies the automatic missing-reference
branch as well.

For completion precision `t`, write `F(t)` for the common, state-independent
completion reservation. The reference experiment splits the uniform Boolean
bank into disjoint segments:

- Each transition receives `s+F(hStep)` bits, where `s=clog₂(32d²)`: a proposal
  prefix and a separate completion word, including when the proposal holds.
- Each attempt receives `T(s+F(hStep))+F(hTerminal)` bits. The terminal suffix
  is fresh after the adaptively obtained final state; its precision is separate.
- The outer bank contains `R` independent attempt words. Every attempt starts
  from the same initial state. Total rejection returns the fixed feasible
  fallback; unused suffix words are not recycled.

`bitStep_law`, `flatWalk_law`, `jointDraw_law`, and `outerDraw_law` identify
these word functions with the actual proposal, completion, walk, joint and
retry laws. `initializedDraw` fixes the original fallback to the greedy
feasible table and constructs its initial physical state from that table.
`initializedDraw_law` identifies this initialized experiment with
`ListedLatticeCompletion.outerLaw`; no caller-supplied completion witness or
accuracy premise is needed.

`initializedDraw_variation` supplies the finite-law bound

```text
exp(-R/S) + R B exp(-T/K)
  + R (T γ 2^(-hStep) + 2^(-hTerminal)),
```

with `K=80000d¹⁷`, the actual physical `S` and `B`, and `γ≤1/2`.
`initializedDraw_explicit_accuracy` discharges the numeric schedule conditions
and gives total variation at most `2^-h` for every natural `h`, under the equal
margin and nonempty large-index hypotheses above.

This is a typed, noncomputable law layer: coordinate equivalences and feasible
table construction occur in the proof-level experiment. It supplies exact
finite-word semantics, but does not by itself implement a literal random
machine, an encoded Boolean transition, or a complete sampler runtime bound.

## Both branches and pointwise feasible output

`PhysicalBooleanSampler.bothLarge` tests the lengths of the actual computed
large-index lists. `draw` chooses the reference experiment when both lists
are nonempty and the unit experiment otherwise. Its return type is `Table r c`
for **every** fixed reserved word: feasibility holds pointwise, including on
total outer rejection. Branch selection, original fallback and initial state
depend only on the original margins.

In the unit branch, `unitBitStep` reads the proposal prefix and moves on a
successful neighbor proposal; an unused proposal code holds the state. The
completion suffix is reserved and ignored, rather than reused.
`flatUnitWalk_law` identifies this actual Boolean walk with the selected unit
transition law. `unitJointDraw` reconstructs the unique terminal completion,
and `unitJointDraw_law` identifies it with the exact joint law. Completion
error is zero in this branch. `unitOuterDraw_law` preserves independent
restarts, the ordinary success test and the same feasible fallback.

`draw_variation` gives the displayed finite-law error bound in either branch.
`draw_explicit_accuracy` applies the stated schedule and proves total variation
at most `2^-h` for every equal-total natural margin pair and every natural
`h`, **including zero margins and empty index types**. No caller-provided
large-index, completion or accuracy witness remains in this combined theorem.

The experiment is still a noncomputable typed function from a fixed Boolean
word to a feasible table. These proofs close the mathematical finite-word law
for both branches; they do not identify the output of the pending literal
encoded walker or construct its public physical random machine. That final
pointwise program seam and the complete machine-cost bound require their own
successful receipts.

## Computing the actual schedule

`LatticeScheduleProgram` is a total ordinary list program. Given margin lists
and `h`, it computes the ideal catalogue size `p`, dimension `d`, row mass `M`,
walk length, restart count, separate precisions, and all word reservations.
Write `clog₂ x = Nat.clog 2 x`, the natural ceiling binary logarithm. Its
schedule is exactly

```text
A = M + 3d² + 5d³ + 3
R = 2(1+p²)(h+3)
T = 80000d¹⁷ (h+3 + clog₂ R + 2d clog₂ A)
hTerminal = h+3 + clog₂ R
hStep = hTerminal + clog₂ T.
```

The crucial `2d` log-mass factor is retained. The completion reservation uses
the actual `d¹²` inflation inside the binary-length bound:

```text
C = d¹² (M + 3d² + 2d)
bFine = clog₂(C+2)
q(t) = t+2 + clog₂(4(t+2))
F(t) = 4(t+2) · 25(d+bFine+q(t)+1)^62
W = R (T(s+F(hStep)) + F(hTerminal)).
```

`polynomial_schedule` and `polynomial_totalBits` prove polynomial charged
TreeTyped work for computing these **numbers** from their encoded inputs.
Fixed powers such as 12, 17 and 62 are fixed program syntax. The schedule
program does not allocate lists of `T` steps, `R` attempts or `W` bits.
Computing a numeric reservation efficiently is separate from executing the
reserved experiment or acquiring those fair bits.

The `*_ofFn` identities identify the program's catalogue, scales, precisions
and widths with the typed physical definitions. In particular,
`totalBits_ofFn` equals `PhysicalReferenceBoolean.outerBits`, and
`totalBits_ofFn_budget` equals `CompletionRandomBudget.physicalTotalReservedBits`.
The [existing arithmetic checkpoint](completion-schedules.md) therefore
applies its degree-85 reserved-bit allowance to these exact widths. That power
counts reserved bits, including unused words; it is not a machine-time degree.

The list schedule is total even on empty or unequal-total inputs. Its numeric
computation theorem does not assert feasible table output for such inputs;
the typed sampler's equal-total hypothesis remains explicit, and the reference
subtheorems retain their nonempty-list hypotheses.

## Evidence and remaining integration

All three selected source modules were freshly compiled with native Windows Lean
4.34.1, direct `-j2 -DautoImplicit=false`. Their imported project objects and
the trusted official package/toolchain cache were reused. The authenticated
internal closures contain 551, 566 and 566 modules, including the selected
module in each count. Complete before/expected/after audit maps contain 1,197,
1,227 and 1,227 input entries; reconstruction checked the frozen graph, transitive
source/object bindings and every direct parent object hash.

The reference compile log retains **two style warnings** about `letI` in a
proposition. The schedule compile log is empty. The both-branch sampler log
retains **seven warnings**: six `letI` style warnings and one deprecated
`dif_neg` rewrite. All 16+105+13 audit reports match
the exact drivers in order, contain no extra compiler output, and use only
`propext`, `Classical.choice`, and `Quot.sound`, or subsets. Source and raw log
hashes remain tied to the original evidence archives. Projected compile logs
replace only machine-specific source pathnames; warning text is retained.

The source hashes are
`3f465cb573045370252e6eaad81c7d8a7b5b297aa7fd48e948868ef8aa8e534e`,
`6f4269c7366956bda9b4a1ccb2f81d89b31834ba1c12585fcd788a1fd248a359`,
and
`a676bb44fd5a60a0f45e082061c4947279ffc7da253527d2504a3620bfffe935`.
Pins remain OpenAI source
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The surrounding native batches were **overall failed**. In the latest batch,
one source compile failed and twelve downstream modules were blocked; its
selected `PhysicalBooleanSampler` module nevertheless compiled and passed all
thirteen strict audits. The separate audit watcher recorded thirteen blocked
module audits and no failed audits. Failed and blocked records remain context
and do not become positive evidence by selecting these three successful
modules. This checkpoint does not certify the literal encoded Boolean step
and walker, final public random machine, or the original bounded-sampling
statement. Those downstream integration proofs require their
own exact successful receipts. It also supplies no fresh Linux reproduction,
strict Comparator replay, practical benchmark, or complete machine-time degree.
