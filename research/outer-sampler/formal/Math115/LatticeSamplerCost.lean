/-
SPDX-License-Identifier: Apache-2.0
Source-only instantiation of the compiled encoding-size bridge for the final
reserved-word sampler. The supplied word is included in deterministic cost;
this file neither acquires random bits nor instantiates a public RandomMachine.
The LatticeSampler dependency is not compilation-verified by this author.
-/
import Math115.CompletionEncodingSize
import Math115.LatticeSampler

namespace Math115.LatticeSamplerCost
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open scoped BigOperators

noncomputable section

lemma reserved_word_length_le_total {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (h : ℕ)
    (bits : Fin (LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h)) → Bool) :
    (List.ofFn bits).length ≤ CompletionRandomBudget.totalReservedBits
      (CompletionEncodingSize.dimension (List.ofFn r, List.ofFn c))
      (CompletionOuterSchedule.physicalSmallCount r c)
      (CompletionEncodingSize.massTotal (List.ofFn r, List.ofFn c)) h := by
  rw [List.length_ofFn, CompletionEncodingSize.dimension_ofFn, CompletionEncodingSize.massTotal_ofFn]
  exact le_of_eq (by simpa only [CompletionRandomBudget.physicalTotalReservedBits] using
    LatticeScheduleProgram.totalBits_ofFn_budget r c h)

lemma reserved_bank_input_weight {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (h : ℕ)
    (bits : Fin (LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h)) → Bool) :
    weight (((List.ofFn r, List.ofFn c), h), List.ofFn bits) ≤
      CompletionEncodingSize.inputEnvelope.eval
        (CompletionEncodingSize.measure (List.ofFn r, List.ofFn c) h) := by
  have hp : CompletionOuterSchedule.physicalSmallCount r c ≤
      CompletionEncodingSize.dimension (List.ofFn r, List.ofFn c) := by
    rw [CompletionEncodingSize.dimension_ofFn]
    exact CompletionRandomBudget.physicalSmallCount_le_dimension r c
  exact CompletionEncodingSize.input_weight_bound (List.ofFn r, List.ofFn c)
    (CompletionOuterSchedule.physicalSmallCount r c) h hp (List.ofFn bits)
    (reserved_word_length_le_total r c h bits)

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
  refine ⟨P, ?_⟩
  intro m n r c h bits
  have hp : CompletionOuterSchedule.physicalSmallCount r c ≤
      CompletionEncodingSize.dimension (List.ofFn r, List.ofFn c) := by
    rw [CompletionEncodingSize.dimension_ofFn]
    exact CompletionRandomBudget.physicalSmallCount_le_dimension r c
  exact hP (List.ofFn r, List.ofFn c) (CompletionOuterSchedule.physicalSmallCount r c) h hp
    (List.ofFn bits) (reserved_word_length_le_total r c h bits)

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

end
end Math115.LatticeSamplerCost
