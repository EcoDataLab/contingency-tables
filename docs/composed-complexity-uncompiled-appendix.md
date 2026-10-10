# Uncompiled research appendix: composed-cost source excerpts
This appendix records **uncompiled proposed Lean source**, not verified sampler results. It supports the conditional comparison in [Composed complexity](composed-complexity.md). No successful compilation, axiom audit, or independent reproduction of the assembled proposal is certified here. The snippets are excerpts, omit dependencies and intervening declarations, and are not standalone Lean modules.

The four draft filenames below identify the exact reviewed sources. Their full-file SHA-256 hashes come from the original 20-file source snapshot in the [structured report](../reports/composed-complexity.json). Hashes establish which text was inspected; they do not establish correctness or compilation. The full pending sampler modules are outside this public evidence package.

Existing checked size bridges are linked separately: [CompletionPublicSize](../formal/Math115/CompletionPublicSize.lean), [CompletionEncodingSize](../formal/Math115/CompletionEncodingSize.lean), and their [verification scope](completion-input-size.md). Their size bounds do not certify an instantiation with the proposed complete sampler.

The point of the excerpts is narrow: the proposed runtime degree is `170 * P.natDegree`, the complete polynomial witness remains existential, supplied-word work is a different cost model, and the final proposed sampling statement imports that symbolic bound. None supplies a literal numeric complete degree.
## Proposed public interface and physical bound

**Status: uncompiled proposal.** Source identifier: `formal/Math115/PublicLatticeSampler.lean`.

Full source SHA-256: `b7cc9fea4b109f1136fe081eb21239c6978ebcc46fe43e05fc2b001c71783245`.

Exact source lines 1–9:

```lean
/-
SPDX-License-Identifier: Apache-2.0
Source-only public literal interface for the NEW computed ideal-scale sampler.
Parsing, printing and the fixed finite-word machine compiler are reused from
pinned generic APIs. The executed schedule and complete output law are the new
LatticeSampler program. No old-scale schedule or runtime theorem is invoked.
Compilation of unresolved sampler dependencies and independent review remain
required. Fair-bit generation is part of the existing finite-word compiler.
-/
```

Exact source lines 23–50:

```lean
/-- A new word-count function; only the binary parser is reused. -/
def wordCount (as : List Symbol) : ℕ := LatticeScheduleProgram.totalBits (parsedSampling as)
def wordCountRealizer : Realizer wordCount :=
  composition parsedSamplingRealizer LatticeScheduleProgram.totalBitsRealizer
lemma polynomial_wordCount : PolynomialTime wordCountRealizer :=
  polynomial_composition polynomial_parsedSampling LatticeScheduleProgram.polynomial_totalBits

/-- Literal public output of the new computed schedule/initializer/two-branch draw. -/
def publicDraw (z : List Symbol × List Bool) : List Symbol :=
  GreedyFeasibleTable.printMatrix (LatticeSampler.draw (parsedSampling z.1, z.2))
def publicDrawRealizer : Realizer publicDraw :=
  composition (composition (pair (composition first parsedSamplingRealizer) second)
    LatticeSampler.drawRealizer) GreedyFeasibleTable.printMatrixRealizer
lemma polynomial_publicDraw : PolynomialTime publicDrawRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_parsedSampling) polynomial_second)
    LatticeSampler.polynomial_draw) GreedyFeasibleTable.polynomial_printMatrix

lemma publicDraw_alphabet (as : List Symbol) (bits : List Bool) :
    ∀ a ∈ publicDraw (as, bits), a ≠ 6 ∧ a ≠ 7 := printMatrix_alphabet _

noncomputable def machine : RandomMachine := FiniteWordExecution.machine wordCountRealizer publicDrawRealizer
noncomputable def machineTime (as : List Symbol) : ℕ :=
  FiniteWordExecution.machineTime wordCountRealizer publicDrawRealizer as

lemma machineTime_polynomial :
    ∃ P : Polynomial ℕ, ∀ as, machineTime as ≤ P.eval (FiniteWordExecution.wordMeasure wordCount as) :=
  FiniteWordExecution.machineTime_polynomial polynomial_wordCount polynomial_publicDraw
```

Exact source lines 138–148:

```lean
/-- Equal totals are retained for the literal input encoding bound. The
coefficient/exponent here control wordMeasure, not the final machine-time degree. -/
lemma public_wordMeasure_bound (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ) (hh : 1 ≤ h) :
    FiniteWordExecution.wordMeasure wordCount (Algorithms.encodeSamplingInput r c h) ≤
      CompletionPublicSize.wordMeasureCoefficient * (Algorithms.samplingSize n r h)^170 := by
  unfold FiniteWordExecution.wordMeasure
  rw [weight_word, wordCount_spec, LatticeScheduleProgram.totalBits_ofFn_budget]
  simpa only [CompletionRandomBudget.physicalTotalReservedBits] using
    CompletionPublicSize.literal_input_and_bank_public_bound r c htotal
      (CompletionOuterSchedule.physicalSmallCount r c) h
      (CompletionRandomBudget.physicalSmallCount_le_dimension r c) hh
```

Exact source lines 152–173:

```lean
/-- One polynomial time bound in the original public samplingSize. Its degree
is determined by the generic physical compiler's polynomial witness; the bank
power and the inverse-gap power are not full runtime exponents. -/
theorem machineTime_public_bound :
    ∃ Ctime Dtime : ℕ, 0 < Ctime ∧ ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i, r i = ∑ j, c j) → ∀ h : ℕ, 1 ≤ h →
        machineTime (Algorithms.encodeSamplingInput r c h) ≤
          Ctime * (Algorithms.samplingSize n r h)^Dtime := by
  obtain ⟨P, hP⟩ := machineTime_polynomial
  let A := CompletionPublicSize.wordMeasureCoefficient
  refine ⟨P.eval A + 1, 170 * P.natDegree, by omega, ?_⟩
  intro m n r c htotal h hh
  have hs : 1 ≤ Algorithms.samplingSize n r h := by
    have hx := CompletionPublicSize.samplingSize_at_least_two (n := n) r h hh
    omega
  calc
    _ ≤ P.eval (FiniteWordExecution.wordMeasure wordCount (Algorithms.encodeSamplingInput r c h)) := hP _
    _ ≤ P.eval (A * (Algorithms.samplingSize n r h)^170) :=
      polynomial_eval_monotone P (public_wordMeasure_bound r c htotal h hh)
    _ ≤ P.eval A * (Algorithms.samplingSize n r h)^(170 * P.natDegree) :=
      ProfilePrograms.polynomial_scaled_power P A (Algorithms.samplingSize n r h) 170 hs
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)
```

## Proposed supplied-word cost bridge

**Status: uncompiled proposal.** Source identifier: `formal/Math115/LatticeSamplerCost.lean`.

Full source SHA-256: `11a1e019a9f7b7d6c753b1e70891b3d033ed42a7cd962aa8dfd0826bd676dc5e`.

Exact source lines 1–7:

```lean
/-
SPDX-License-Identifier: Apache-2.0
Source-only instantiation of the compiled encoding-size bridge for the final
reserved-word sampler. The supplied word is included in deterministic cost;
this file neither acquires random bits nor instantiates a public RandomMachine.
The LatticeSampler dependency is not compilation-verified by this author.
-/
```

Exact source lines 40–50:

```lean
/-- One polynomial bounds deterministic tree cost plus output size on every
reserved word, in encoded margins plus numeric h. No equal-total hypothesis
is required for this cost theorem; feasibility and TV remain separate. -/
theorem reserved_draw_work :
    ∃ P : Polynomial ℕ, ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (h : ℕ)
      (bits : Fin (LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h)) → Bool),
      let z := (((List.ofFn r, List.ofFn c), h), List.ofFn bits)
      LatticeSampler.drawRealizer.cost z + weight (LatticeSampler.draw z) ≤
        P.eval (CompletionEncodingSize.measure (List.ofFn r, List.ofFn c) h) := by
  obtain ⟨P, hP⟩ := CompletionEncodingSize.reserved_program_work
    (F := LatticeSampler.drawRealizer) LatticeSampler.polynomial_draw
```

Exact source lines 60–74:

```lean
/-- Literal public margin encoding length plus numeric precision is another
valid polynomial measure. This is still a TreeTyped supplied-word cost bound,
not the physical-machine conversion or an explicit running-time exponent. -/
theorem reserved_draw_work_literal :
    ∃ P : Polynomial ℕ, ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (h : ℕ)
      (bits : Fin (LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h)) → Bool),
      let z := (((List.ofFn r, List.ofFn c), h), List.ofFn bits)
      LatticeSampler.drawRealizer.cost z + weight (LatticeSampler.draw z) ≤
        P.eval ((Algorithms.encodeMargins r c).length + h + 3) := by
  obtain ⟨P, hP⟩ := reserved_draw_work
  refine ⟨P.comp (4 * Polynomial.X), ?_⟩
  intro m n r c h bits
  apply (hP m n r c h bits).trans
  simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X] using
    polynomial_eval_monotone P (CompletionEncodingSize.measure_le_literal_length_numeric r c h)
```

## Proposed bounded-sampling instantiation

**Status: uncompiled proposal.** Source identifier: `formal/Math115/LatticeBoundedSampling.lean`.

Full source SHA-256: `a67e022d7a472abd3c25508e1bd3253f213eb40d141b6ee2e954deeab533500a`.

Exact source lines 1–6:

```lean
/-
SPDX-License-Identifier: Apache-2.0
Source-only proposed instantiation of the original bounded-sampling statement
for the NEW computed ideal-scale public machine. No exact sampler or counting
extension is supplied. Independent review and compilation remain necessary.
-/
```

Exact source lines 16–25:

```lean
/-- A fixed public RandomMachine, every-tape bounded halting/feasibility, and
normalized TV at the same fixed execution time. No explicit complete runtime
degree is claimed: it is the physical compiler witness's degree. -/
theorem boundedSampling : Algorithms.BoundedSamplingStatement := by
  obtain ⟨Ctime, Dtime, hC, hbound⟩ := PublicLatticeSampler.machineTime_public_bound
  refine ⟨PublicLatticeSampler.machine, Ctime, Dtime, hC, ?_⟩
  intro m n r c htotal h hh
  dsimp only
  have ht := hbound m n r c htotal h hh
  refine ⟨PublicLatticeSampler.machine_outputs r c htotal h _ ht, ?_⟩
```

## Proposed ordinary list draw and both branches

**Status: uncompiled proposal.** Source identifier: `formal/Math115/LatticeSampler.lean`.

Full source SHA-256: `486cf091c5cf7c46e2acc10db7e253e581623d6e364d595a72fe67b5033db78f`.

Exact source lines 1–7:

```lean
/-
SPDX-License-Identifier: Apache-2.0
One encoded ideal-scale sampler: compute the schedule and initial configuration,
select the actual reference or empty-block branch, then consume a reserved
Boolean word. Supplied-word polynomial cost and reserved-bit bounds are stated
separately; no explicit full machine-time exponent is asserted here.
-/
```

Exact source lines 60–83:

```lean
/-- A total ordinary list function, with all choices computed from its input. -/
def draw (z : Input) : MatrixCode :=
  if LatticeSamplerPreparation.bothLargeTest z.1.1 then
    LatticeOuterProgram.retry (prepare z.1, z.2)
  else LatticeUnitOuter.retry (prepare z.1, z.2)

def drawRealizer : Realizer draw :=
  (choose (composition (composition first first) LatticeSamplerPreparation.bothLargeTestRealizer)
    (composition (pair (composition first prepareRealizer) second) LatticeOuterProgram.retryRealizer)
    (composition (pair (composition first prepareRealizer) second) LatticeUnitOuter.retryRealizer)).congr
      (by intro z; rfl)

/-- Polynomial tree-machine time includes the supplied Boolean bank as input.
The next theorem bounds that bank separately; d^17 is the gap allowance. -/
theorem polynomial_draw : PolynomialTime drawRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      LatticeSamplerPreparation.polynomial_bothLargeTest)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_prepare) polynomial_second)
      LatticeOuterProgram.polynomial_retry)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_prepare) polynomial_second)
      LatticeUnitOuter.polynomial_retry))
```

## How to read the proposed bound

In the public-interface excerpt, `machineTime_polynomial` has an existential `Polynomial ℕ` witness. The proposed `machineTime_public_bound` selects `P.eval A + 1` and `170 * P.natDegree`; it does not select a numeric degree. The source's `public_wordMeasure_bound` is itself an uncompiled use of an existing scalar input-and-bank theorem plus the proposed computed-word identity.

In the supplied-word excerpt, `reserved_draw_work` proposes applying an existing generic theorem to `LatticeSampler.drawRealizer` and the proposed `polynomial_draw` witness. `reserved_draw_work_literal` uses an affine size change. These proposed instantiations do not acquire fresh bits or instantiate the complete physical machine.

In the final-statement excerpt, `boundedSampling` begins by obtaining the same symbolic degree and then claiming the original fixed-time statement. The truncated proof fragment is included to expose that dependency, not as a complete proof. The last excerpt shows that the proposed `draw` selects between reference and empty-block branches; its asserted polynomial witness depends on both retry realizers.

The accompanying comparison therefore retains the verified scalar reservation and a conditional compiler-degree calculation while marking the complete local sampler as unresolved. Public inspection of these excerpts cannot replace checking its omitted dependencies or the complete theorem bodies.
