/-
SPDX-License-Identifier: Apache-2.0
Pointwise acceptance correspondence at arbitrary physical cutoff and padding.
The existing list Boolean test is applied to the frozen sampler's actual
output. This does not implement the defect trace's weighted exit or clock.
-/
import ResearchComparison.LegacyPhysicalCompletion
import OAI.Combinatorics.ContingencyTables.Transport.ListedReferenceDecision
import OAI.Combinatorics.ContingencyTables.Transport.TranslationDecisionSemantics

set_option maxHeartbeats 800000

namespace Math115.ListedAcceptance

open OAI OAI.ContingencyTables
open ProfilePrograms DensePrograms SmallGraphProfiles CompletionTranslation
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open Math115.ReducedSmallChain Math115.LegacyPhysicalCompletion Math115.PhysicalStationarySuccess
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)
local notation "B" => capacity r c U L
local notation "i₀" => largeOptionEquiv r U hr none
local notation "j₀" => largeOptionEquiv c U hc none
local notation "R" => listedRows r c U L B hr
local notation "P" => listedColumns r c U L B hc
local notation "R₀" => referenceRows r c U L B i₀
local notation "P₀" => referenceColumns r c U L B j₀
local notation "nr" => tailCount r U
local notation "nc" => tailCount c U

def listedCompletion (x : States r c U L) (A : Fibre r c U L x) : Table (R x) (P x) :=
  listedFibreEquiv r c U L B hr hc x
    (physical_paper_capacity _ r c _ L U dimension_le_allowance x) A

def referenceCompletion (x : States r c U L) (A : Fibre r c U L x) :
    Table (R₀ x) (P₀ x) :=
  referenceFibreEquiv r c U L B i₀ j₀ x
    (physical_paper_capacity _ r c _ L U dimension_le_allowance x) A

attribute [local irreducible] referenceFibreEquiv listedFibreEquiv

lemma listed_between (x y : States r c U L) (i) (j) :
    between (R x) (R y) (P x) (P y) i j =
      between (R₀ x) (R₀ y) (P₀ x) (P₀ y)
        (listedReferenceIndex r U hr i) (listedReferenceIndex c U hc j) := by
  have he := between_reindex (listedReferenceIndex r U hr) (listedReferenceIndex c U hc)
    (listedReferenceIndex_none r U hr) (listedReferenceIndex_none c U hc)
    (R₀ x) (R₀ y) (P₀ x) (P₀ y) i j
  simpa only [listedReference_row, listedReference_column] using he

/-- The signed translation test is unchanged by the computed coordinate order.
This is pointwise in a physical completion, without any probability premise. -/
theorem translated_nonnegative (x y : States r c U L) (A : Fibre r c U L x) :
    (∀ i j, 0 ≤ ((listedCompletion r c U L hr hc x A).val i j : ℤ) +
      between (R x) (R y) (P x) (P y) i j) ↔
    ∀ i j, 0 ≤ ((referenceCompletion r c U L hr hc x A).val i j : ℤ) +
      between (R₀ x) (R₀ y) (P₀ x) (P₀ y) i j := by
  have he (i) (j) : (listedCompletion r c U L hr hc x A).val i j =
      (referenceCompletion r c U L hr hc x A).val
        (listedReferenceIndex r U hr i) (listedReferenceIndex c U hc j) :=
    listedFibreEquiv_entry r c U L B hr hc x
      (physical_paper_capacity _ r c _ L U dimension_le_allowance x) A i j
  constructor
  · intro h i j
    obtain ⟨i, rfl⟩ := (listedReferenceIndex r U hr).surjective i
    obtain ⟨j, rfl⟩ := (listedReferenceIndex c U hc).surjective j
    have hij := h i j
    rw [he i j, listed_between r c U L hr hc x y i j] at hij
    exact hij
  · intro h i j
    rw [he i j, listed_between r c U L hr hc x y i j]
    exact h _ _

/-- Listed and computed-reference decisions agree for every physical completion,
including a missing proposal. No adjacency or padding lower bound is needed. -/
theorem listed_completionDecision (x : States r c U L)
    (proposal : Option (States r c U L)) (A : Fibre r c U L x) :
    completionDecision R P x proposal (listedCompletion r c U L hr hc x A) =
      completionDecision R₀ P₀ x proposal (referenceCompletion r c U L hr hc x A) := by
  cases proposal with
  | none => rfl
  | some y =>
    unfold completionDecision
    dsimp only
    have he := translated_nonnegative r c U L hr hc x y A
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact False.elim (h₂ (he.mp h₁))
    · exact False.elim (h₁ (he.mpr h₂))
    · rfl

def listedDraw (x : States r c U L) (h : ℕ)
    (word : Fin (bits r c U L hr hc x h) → Bool) : Table (R x) (P x) :=
  listedCompletion r c U L hr hc x (completionDraw r c U L hr hc x h word)

lemma listedDraw_output (x : States r c U L) (h : ℕ)
    (word : Fin (bits r c U L hr hc x h) → Bool) :
    tableOutput (m := nr) (n := nc) (listedDraw r c U L hr hc x h word) =
      matrixCode (programTable r c U L hr hc x h word).val := by
  have he :
      tableReindex (finSuccEquiv nr) (finSuccEquiv nc) (R x) (P x)
        (listedDraw r c U L hr hc x h word) =
      programTable r c U L hr hc x h word := by
    unfold listedDraw listedCompletion
    exact (finiteFibreEquiv r c U L hr hc x).apply_symm_apply
      (programTable r c U L hr hc x h word)
  exact congrArg
    (fun X : Table (coarseRows r c U L hr x) (coarseColumns r c U L hc x) =>
      matrixCode X.val) he

/-- The actual frozen draw output is exactly the listed table's code. -/
theorem draw_listed_code (x : States r c U L) (h : ℕ)
    (word : Fin (bits r c U L hr hc x h) → Bool) :
    LatticeSampler.draw
      (((List.ofFn (coarseRows r c U L hr x), List.ofFn (coarseColumns r c U L hc x)), h),
        List.ofFn word) = tableOutput (listedDraw r c U L hr hc x h word) :=
  (programTable_code r c U L hr hc x h word).trans
    (listedDraw_output r c U L hr hc x h word).symm

lemma margin_codes (x : States r c U L) :
    (List.ofFn (coarseRows r c U L hr x), List.ofFn (coarseColumns r c U L hc x)) =
      (marginCode (R x), marginCode (P x)) :=
  Prod.ext (marginCode_ofFn _).symm (marginCode_ofFn _).symm

/-- Executable list arithmetic on the actual sampler output decides exactly the
computed-reference translated-nonnegativity predicate, on every word. -/
theorem translationValid_draw (x y : States r c U L) (h : ℕ)
    (word : Fin (bits r c U L hr hc x h) → Bool) :
    translationValid
      (((List.ofFn (coarseRows r c U L hr x), List.ofFn (coarseColumns r c U L hc x)),
        (List.ofFn (coarseRows r c U L hr y), List.ofFn (coarseColumns r c U L hc y))),
        LatticeSampler.draw
          (((List.ofFn (coarseRows r c U L hr x), List.ofFn (coarseColumns r c U L hc x)), h),
            List.ofFn word)) = true ↔
      ∀ i j, 0 ≤ ((referenceCompletion r c U L hr hc x
        (completionDraw r c U L hr hc x h word)).val i j : ℤ) +
          between (R₀ x) (R₀ y) (P₀ x) (P₀ y) i j := by
  rw [draw_listed_code r c U L hr hc x h word,
    margin_codes r c U L hr hc x, margin_codes r c U L hr hc y]
  exact (translationValid_code (R x) (R y) (P x) (P y)
    (listedDraw r c U L hr hc x h word)).trans
    (translated_nonnegative r c U L hr hc x y (completionDraw r c U L hr hc x h word))

/-- The actual Boolean branch agrees with the physical reference decision for
every completion word and optional proposal. This is one acceptance interface,
not a proposal distribution, a weighted exit sampler or an outer realizer. -/
theorem draw_completionDecision (x : States r c U L)
    (proposal : Option (States r c U L)) (h : ℕ)
    (word : Fin (bits r c U L hr hc x h) → Bool) :
    (match proposal with
      | none => x
      | some y =>
        if translationValid
          (((List.ofFn (coarseRows r c U L hr x), List.ofFn (coarseColumns r c U L hc x)),
            (List.ofFn (coarseRows r c U L hr y), List.ofFn (coarseColumns r c U L hc y))),
            LatticeSampler.draw
              (((List.ofFn (coarseRows r c U L hr x), List.ofFn (coarseColumns r c U L hc x)), h),
                List.ofFn word)) then y else x) =
      completionDecision R₀ P₀ x proposal (referenceCompletion r c U L hr hc x
        (completionDraw r c U L hr hc x h word)) := by
  cases proposal with
  | none => rfl
  | some y =>
    have he := translationValid_draw r c U L hr hc x y h word
    dsimp only
    unfold completionDecision
    dsimp only
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact False.elim (h₂ (he.mp h₁))
    · exact False.elim (h₁ (he.mpr h₂))
    · rfl

end
end Math115.ListedAcceptance
