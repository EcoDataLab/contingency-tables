/-
SPDX-License-Identifier: Apache-2.0
Source-only public literal interface for the NEW computed ideal-scale sampler.
Parsing, printing and the fixed finite-word machine compiler are reused from
pinned generic APIs. The executed schedule and complete output law are the new
LatticeSampler program. No old-scale schedule or runtime theorem is invoked.
Compilation of unresolved sampler dependencies and independent review remain
required. Fair-bit generation is part of the existing finite-word compiler.
-/
import Math115.LatticeSampler
import Math115.CompletionPublicSize
import OAI.Combinatorics.ContingencyTables.Sampling.ProfilePublicSemantics
import OAI.Combinatorics.ContingencyTables.Sampling.ProfilePublicMachine
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileRuntimeBound
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordTableLaw

namespace Math115.PublicLatticeSampler
open OAI OAI.ContingencyTables OAI.MatchingFPRAS
open OAI.MatchingFPRAS.TreeTyped OAI.MatchingFPRAS.LiteralCodec
open ProfilePrograms DensePrograms
open scoped BigOperators

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

open FirstSuccess ResidualMixture
open scoped Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma wordCount_spec (h : ℕ) :
    wordCount (Algorithms.encodeSamplingInput r c h) =
      LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h) := by
  unfold wordCount
  rw [SmallGraphProfiles.parsedSampling_spec]

/-- The actual finite-word program law comes solely from draw_spec, including
both branches, ordinary fallback mass and all inner rejections. -/
theorem public_spec (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ) :
    let q := LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h)
    letI := OAI.ContingencyTables.table_nonempty r c htotal
    ∃ f : (Fin q → Bool) → Table r c,
      (∀ bits, publicDraw (Algorithms.encodeSamplingInput r c h, List.ofFn bits) =
        Algorithms.encodeMatrix (f bits).val) ∧
      (variation (mapLaw (uniformLaw (α := Fin q → Bool)) f)
        (uniformLaw (α := Table r c)) : ℝ) ≤ (CompletionRetryBudget.dyadic h : ℝ) := by
  dsimp only
  letI := OAI.ContingencyTables.table_nonempty r c htotal
  obtain ⟨f, hcode, hv⟩ := LatticeSampler.draw_spec r c htotal h
  refine ⟨f, ?_, hv⟩
  intro bits
  unfold publicDraw
  rw [SmallGraphProfiles.parsedSampling_spec, hcode bits]
  exact GreedyFeasibleTable.printMatrix_ofFn (f bits).val

/-- Proof-level witness for the actual table-valued output. It is never called
by the executed public program or its realizer. -/
def tableDraw (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ) :
    (Fin (LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h)) → Bool) → Table r c :=
  Classical.choose (public_spec r c htotal h)

lemma tableDraw_code (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (bits : Fin (LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h)) → Bool) :
    publicDraw (Algorithms.encodeSamplingInput r c h, List.ofFn bits) =
      Algorithms.encodeMatrix (tableDraw r c htotal h bits).val :=
  (Classical.choose_spec (public_spec r c htotal h)).1 bits

lemma tableDraw_variation (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ) :
    letI := OAI.ContingencyTables.table_nonempty r c htotal
    (variation (mapLaw (uniformLaw (α := Fin
      (LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h)) → Bool))
      (tableDraw r c htotal h)) (uniformLaw (α := Table r c)) : ℝ) ≤
        (CompletionRetryBudget.dyadic h : ℝ) :=
  (Classical.choose_spec (public_spec r c htotal h)).2

/-- All time-indexed random tapes halt and yield a feasible original table at
any one time bound dominating this fixed new machine's execution allowance. -/
theorem machine_outputs (htotal : ∑ i, r i = ∑ j, c j) (h t : ℕ)
    (ht : machineTime (Algorithms.encodeSamplingInput r c h) ≤ t) :
    ∀ bits : PhysicalStream.Bits t, ∃ X : Table r c,
      Algorithms.OutputsTable machine (Algorithms.encodeSamplingInput r c h) bits X.val := by
  let as := Algorithms.encodeSamplingInput r c h
  let P : Turing.Tape Symbol → Prop := fun tape => ∃ X : Table r c,
    tape.right₀ = Turing.ListBlank.mk (Algorithms.encodeMatrix X.val)
  have hf : ∀ bits : PhysicalStream.Bits (wordCount as),
      P (Turing.Tape.mk₁ (publicDraw (as, List.ofFn bits))) := by
    dsimp only [as]
    rw [wordCount_spec]
    intro bits
    refine ⟨tableDraw r c htotal h bits, ?_⟩
    rw [tableDraw_code r c htotal h]
    simp only [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_right₀]
  have hP := FiniteWordExecution.machine_all wordCountRealizer publicDrawRealizer as
    (samplingInput_nonzero r c h) (publicDraw_alphabet as) P hf t ht
  have hhalt := (FiniteWordExecution.machine_law wordCountRealizer publicDrawRealizer as
    (samplingInput_nonzero r c h) (publicDraw_alphabet as) t ht).1
  intro bits
  obtain ⟨X, hX⟩ := hP bits
  exact ⟨X, hhalt bits, hX⟩

lemma machine_mass (htotal : ∑ i, r i = ∑ j, c j) (h t : ℕ)
    (ht : machineTime (Algorithms.encodeSamplingInput r c h) ≤ t) (X : Table r c) :
    Algorithms.tableMass machine (Algorithms.encodeSamplingInput r c h) t X.val =
      ((mapLaw (uniformLaw (α := Fin
        (LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h)) → Bool))
        (tableDraw r c htotal h)).mass X : ℝ) :=
  FiniteWordExecution.machine_tableMass wordCountRealizer publicDrawRealizer
    (Algorithms.encodeSamplingInput r c h) (samplingInput_nonzero r c h)
    (publicDraw_alphabet _) (wordCount_spec r c h) (tableDraw r c htotal h)
    (tableDraw_code r c htotal h) t ht X

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

end

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

end Math115.PublicLatticeSampler
