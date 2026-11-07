/-
SPDX-License-Identifier: Apache-2.0
Optional exact zero-bit replacement for a physical completion whose actual
coarse request has at most one row or column. The default backend is unchanged.
No no-small specialization or execution-time bound is asserted.
-/
import ResearchPhysicalTraceJoin.GeneralCompletionCode
import Math115.AdaptiveDenseCompletion

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open SmallContextFibres PaddedCompletions FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace Math115.PhysicalComputedProposal
open Math115.LegacyPhysicalCompletion Math115.PhysicalCompletionWidth Math115.PhysicalCompletionOracle
open scoped BigOperators

/-- An ordinary representative depending only on the coarse margin lists.
It consumes no Boolean word and makes no semantic table choice. -/
def rawSingletonCompletionCode (rs cs : List ℕ) : MatrixCode :=
  GreedyFeasibleTable.listMatrix rs cs

open scoped Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U,List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U,List.ofFn c)).length)

theorem coarseSingletonTable_subsingleton (z : States r c U L)
    (hs : (largeIndices (U,List.ofFn r)).length ≤ 1 ∨
      (largeIndices (U,List.ofFn c)).length ≤ 1) :
    Subsingleton (Table (coarseRows r c U L hr z) (coarseColumns r c U L hc z)) := by
  rcases hs with hs | hs
  · apply Math115.AdaptiveDenseCompletion.table_subsingleton_of_row_card_le_one
    simp only [Fintype.card_fin]
    unfold tailCount
    omega
  · apply Math115.AdaptiveDenseCompletion.table_subsingleton_of_column_card_le_one
    simp only [Fintype.card_fin]
    unfold tailCount
    omega

/-- Typed transport of the same raw greedy representative. Accuracy is only
claimed below under the actual singleton-request guard. -/
def singletonCompletionDraw (z : States r c U L) (_word : Fin 0 → Bool) : Math115.PhysicalStationarySuccess.Fibre r c U L z :=
  (finiteFibreEquiv r c U L hr hc z).symm
    (GreedyFeasibleTable.table (coarseRows r c U L hr z) (coarseColumns r c U L hc z)
      (coarse_totals r c U L hr hc z))

/-- Every complete inherited word gives this same actual fibre, not just
an approximation to its law. No claim is made for short raw Boolean lists. -/
theorem completionDraw_eq_singleton (z : States r c U L)
    (hs : (largeIndices (U,List.ofFn r)).length ≤ 1 ∨
      (largeIndices (U,List.ofFn c)).length ≤ 1) (h : ℕ)
    (word : Fin (bits r c U L hr hc z h) → Bool) (emptyWord : Fin 0 → Bool) :
    completionDraw r c U L hr hc z h word = singletonCompletionDraw r c U L hr hc z emptyWord := by
  letI := coarseSingletonTable_subsingleton r c U L hr hc z hs
  apply (finiteFibreEquiv r c U L hr hc z).injective
  exact Subsingleton.elim _ _

/-- The optional zero-bit experiment has exactly the existing frozen law. -/
theorem singletonCompletionDraw_same_law (z : States r c U L)
    (hs : (largeIndices (U,List.ofFn r)).length ≤ 1 ∨
      (largeIndices (U,List.ofFn c)).length ≤ 1) (h : ℕ) :
    mapLaw (uniformLaw (α := Fin 0 → Bool)) (singletonCompletionDraw r c U L hr hc z) =
      completionLaw r c U L hr hc z h := by
  let emptyWord : Fin 0 → Bool := fun i => Fin.elim0 i
  have he : completionDraw r c U L hr hc z h =
      fun _ => singletonCompletionDraw r c U L hr hc z emptyWord := by
    funext word
    exact completionDraw_eq_singleton r c U L hr hc z hs h word emptyWord
  unfold completionLaw
  rw [he, mapLaw_constant]
  exact mapLaw_constant _ _

lemma rawSingletonCompletionCode_table {a b : ℕ} (R : Fin a → ℕ) (P : Fin b → ℕ)
    (htotal : (∑ i, R i) = ∑ j, P j) :
    rawSingletonCompletionCode (List.ofFn R) (List.ofFn P) =
      matrixCode (GreedyFeasibleTable.table R P htotal).val :=
  Math115.LatticeSamplerPreparation.initialFallback_code R P htotal

/-- On an actual singleton coarse request, the complete frozen draw can be
replaced pointwise by the zero-bit list representative. The word-length guard
is retained even though the replacement itself takes no word. -/
theorem rawCompletionResidual_singleton (z : States r c U L)
    (hs : (largeIndices (U,List.ofFn r)).length ≤ 1 ∨
      (largeIndices (U,List.ofFn c)).length ≤ 1) (h N : ℕ)
    (hN : bits r c U L hr hc z h ≤ N) (word : Fin N → Bool) :
    rawCompletionResidual (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L z)
      h (List.ofFn word) = rawSingletonCompletionCode
        (rawCoarseRows (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L z))
        (rawCoarseColumns (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L z)) := by
  letI := coarseSingletonTable_subsingleton r c U L hr hc z hs
  rw [rawCompletionResidual_eq r c U L hr hc z h N hN word,
    rawCoarseRows_eq r c U L hr z, rawCoarseColumns_eq r c U L hc z,
    rawSingletonCompletionCode_table _ _ (coarse_totals r c U L hr hc z)]
  exact congrArg (fun X : Table (coarseRows r c U L hr z) (coarseColumns r c U L hc z) =>
    matrixCode X.val) (Subsingleton.elim _ _)

/-- The raw representative also encodes the typed zero-bit fibre in exactly
the existing coarse row/column order. -/
theorem rawSingletonCompletionCode_draw (z : States r c U L) (emptyWord : Fin 0 → Bool) :
    rawSingletonCompletionCode
      (rawCoarseRows (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L z))
      (rawCoarseColumns (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L z)) =
      matrixCode ((finiteFibreEquiv r c U L hr hc z)
        (singletonCompletionDraw r c U L hr hc z emptyWord)).val := by
  rw [rawCoarseRows_eq r c U L hr z, rawCoarseColumns_eq r c U L hc z]
  simpa only [singletonCompletionDraw, Equiv.apply_symm_apply] using
    rawSingletonCompletionCode_table (coarseRows r c U L hr z) (coarseColumns r c U L hc z)
      (coarse_totals r c U L hr hc z)

end
end Math115.PhysicalTraceJoin
