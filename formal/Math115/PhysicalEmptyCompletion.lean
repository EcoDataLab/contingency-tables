/-
SPDX-License-Identifier: Apache-2.0
Explicit empty-large-block completion from the retained profile views.
The data is a RowColumnPair/Fibre, not an ordinary Table before balance.
Existence is used only for erased proofs, never to choose output entries.
The adjacent-neighbor unit transition and outer loop remain separate.
-/
import Math115.PhysicalComputedProposal
import OAI.Combinatorics.ContingencyTables.Sampling.AllSmallFibres
import OAI.Combinatorics.ContingencyTables.Sampling.OuterMatrixSemantics
import OAI.Combinatorics.ContingencyTables.Sampling.SmallComplementProgram
import OAI.Combinatorics.ContingencyTables.Transport.FiniteDeterministicJoint

namespace Math115.PhysicalEmptyCompletion

open OAI OAI.ContingencyTables
open SmallGraphProfiles CompletionCounts PaddedCompletions
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open SmallContextCoordinates SmallContextFibres ProfilePrograms DensePrograms
open ReducedSmallChain PhysicalStationarySuccess PhysicalStationaryLaw
open FirstSuccess ResidualMixture MatchingFPRAS.TreeTyped
open scoped BigOperators

/-- Ordinary total data for reconstructing both retained views.
Dimensions come from margin-list lengths, not a binary counter loop. -/
abbrev ReconstructionInput :=
  ((List ℕ × List ℕ) × (List (ℕ × ℕ) × (List ℕ × List ℕ))) × ℕ

/-- A generic matrix-output input with only a retained sparse view. -/
def retainedData (x : List (ℕ × ℕ) × List ℕ) : OuterTableData :=
  (((x.1, (x.2, [])), ([], [])), ((0, 0), []))

def retainedDataRealizer : Realizer retainedData :=
  pair (pair (pair first (pair second (constant []))) (constant ([], [])))
    (constant ((0, 0), []))

theorem polynomial_retainedData : PolynomialTime retainedDataRealizer := by
  unfold retainedDataRealizer
  exact polynomial_pair
    (polynomial_pair (polynomial_pair polynomial_first
      (polynomial_pair polynomial_second (polynomial_constant []))) (polynomial_constant ([], [])))
    (polynomial_constant ((0, 0), []))

def rowInput (x : ReconstructionInput) : OuterMatrixInput :=
  (x.1.1, retainedData (x.1.2.1, x.1.2.2.1))

def rowInputRealizer : Realizer rowInput :=
  pair first.fst (composition (pair first.snd.fst first.snd.snd.fst) retainedDataRealizer)

theorem polynomial_rowInput : PolynomialTime rowInputRealizer := by
  unfold rowInputRealizer Realizer.fst Realizer.snd
  exact polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      (polynomial_composition
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second)
        polynomial_first)) polynomial_retainedData)

def columnInput (x : ReconstructionInput) : OuterMatrixInput :=
  (x.1.1, retainedData (x.1.2.1, complementValues (x.2, x.1.2.2.2)))

def columnInputRealizer : Realizer columnInput :=
  pair first.fst (composition (pair first.snd.fst
    (composition (pair second first.snd.snd.snd) complementValuesRealizer)) retainedDataRealizer)

theorem polynomial_columnInput : PolynomialTime columnInputRealizer := by
  unfold columnInputRealizer Realizer.fst Realizer.snd
  exact polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      (polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition
          (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second)
          polynomial_second)) polynomial_complementValues)) polynomial_retainedData)

/-- Every input list produces two matrix codes; no abstract fibre member
or feasibility witness is a program input. -/
def reconstructViews (x : ReconstructionInput) : MatrixCode × MatrixCode :=
  (outputMatrix (rowInput x), outputMatrix (columnInput x))

def reconstructViewsRealizer : Realizer reconstructViews :=
  pair (composition rowInputRealizer outputMatrixRealizer)
    (composition columnInputRealizer outputMatrixRealizer)

theorem polynomial_reconstructViews : PolynomialTime reconstructViewsRealizer := by
  unfold reconstructViewsRealizer
  exact polynomial_pair (polynomial_composition polynomial_rowInput polynomial_outputMatrix)
    (polynomial_composition polynomial_columnInput polynomial_outputMatrix)

lemma retainedData_entry (K : List (ℕ × ℕ)) (v : List ℕ) (i j : ℕ) (hij : (i, j) ∈ K) :
    outputEntry (retainedData (K, v), (i, j)) = lookupView ((K, v), (i, j)) := by
  rw [outputEntry, ite_eq_left (show outputCellPosition (retainedData (K, v), (i, j)) <
    (retainedData (K, v)).1.1.1.length from List.idxOf_lt_length_iff.mpr hij)]
  rfl

noncomputable section
open scoped Classical
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The stored false view extended as an ordinary natural matrix. -/
def storedRows (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (z : States r c U L) : I → J → ℕ :=
  smallView (firstPaperSmall r c U) (physicalProfile _ (capacity r c U L) r c L z) false

/-- The physical column view is the capacity minus the stored true view. -/
def storedColumns (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (z : States r c U L) : I → J → ℕ :=
  fun i j => capacity r c U L i j -
    smallView (firstPaperSmall r c U) (physicalProfile _ (capacity r c U L) r c L z) true i j

/-- Direct data construction. A feasible fibre witness is eliminated only
inside the erased proofs of margins and fibre membership. -/
def allSmallCompletion (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hsmall : ∀ i j, firstPaperSmall r c U i j = true) (z : States r c U L) : Fibre r c U L z := by
  let views := (storedRows r c U L z, storedColumns r c U L z)
  have hviews (A : Fibre r c U L z) : views = A.val.val := by
    apply Prod.ext
    · funext i j
      simpa only [views, storedRows, smallView, dite_eq_left (hsmall i j)] using
        (A.property.2.2.1 i j (hsmall i j)).1.symm
    · funext i j
      simpa only [views, storedColumns, smallView, dite_eq_left (hsmall i j)] using
        (A.property.2.2.1 i j (hsmall i j)).2.symm
  have hpair :
      (∀ i, ∑ j, views.1 i j = r i + rowLargeCount (firstPaperSmall r c U) i * L) ∧
      (∀ j, ∑ i, views.2 i j = c j + columnLargeCount (firstPaperSmall r c U) j * L) := by
    obtain ⟨A⟩ := (inferInstance : Nonempty (Fibre r c U L z))
    have h := A.val.property
    rw [← hviews A] at h
    exact h
  let pair : RowColumnPair
      (fun i => r i + rowLargeCount (firstPaperSmall r c U) i * L)
      (fun j => c j + columnLargeCount (firstPaperSmall r c U) j * L) := ⟨views, hpair⟩
  refine ⟨pair, ?_⟩
  obtain ⟨A⟩ := (inferInstance : Nonempty (Fibre r c U L z))
  have hp : pair = A.val := Subtype.ext (hviews A)
  exact hp.symm ▸ A.property

/-- Readback of all output data is definitional; no chosen table supplies it. -/
lemma allSmallCompletion_views (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hsmall : ∀ i j, firstPaperSmall r c U i j = true) (z : States r c U L) :
    (allSmallCompletion r c U L hsmall z).val.val =
      (storedRows r c U L z, storedColumns r c U L z) := rfl

lemma allSmallCompletion_row (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hsmall : ∀ i j, firstPaperSmall r c U i j = true) (z : States r c U L) (i : I) (j : J) :
    (allSmallCompletion r c U L hsmall z).val.val.1 i j =
      physicalProfile _ (capacity r c U L) r c L z (⟨(i, j), hsmall i j⟩, false) := by
  rw [allSmallCompletion_views]
  simp only [storedRows, smallView, dite_eq_left (hsmall i j)]

lemma allSmallCompletion_column (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hsmall : ∀ i j, firstPaperSmall r c U i j = true) (z : States r c U L) (i : I) (j : J) :
    (allSmallCompletion r c U L hsmall z).val.val.2 i j = capacity r c U L i j -
      physicalProfile _ (capacity r c U L) r c L z (⟨(i, j), hsmall i j⟩, true) := by
  rw [allSmallCompletion_views]
  simp only [storedColumns, smallView, dite_eq_left (hsmall i j)]

lemma allSmallCompletion_unique (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hsmall : ∀ i j, firstPaperSmall r c U i j = true) (z : States r c U L) (A : Fibre r c U L z) :
    A = allSmallCompletion r c U L hsmall z := by
  letI : Subsingleton (Fibre r c U L z) := completionFibre_subsingleton _ _ _ _ _ _ _ hsmall
  exact Subsingleton.elim _ _

lemma allSmallCompletion_pointLaw_uniform (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hsmall : ∀ i j, firstPaperSmall r c U i j = true) (z : States r c U L) :
    pointLaw (allSmallCompletion r c U L hsmall z) = uniformLaw (α := Fibre r c U L z) := by
  letI : Subsingleton (Fibre r c U L z) := completionFibre_subsingleton _ _ _ _ _ _ _ hsmall
  exact pointLaw_eq_uniform _

lemma allSmall_of_empty (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U)) :
    ∀ i j, firstPaperSmall r c U i j = true := by
  intro i j
  have hs : r i < U ∨ c j < U := by
    rcases hempty with hr | hc
    · left
      by_contra h
      exact hr.false ⟨i, by omega⟩
    · right
      by_contra h
      exact hc.false ⟨j, by omega⟩
  simpa only [firstPaperSmall, decide_eq_true_eq] using hs

def emptyCompletion (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U)) (z : States r c U L) :
    Fibre r c U L z := allSmallCompletion r c U L (allSmall_of_empty r c U hempty) z

lemma emptyCompletion_views (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U)) (z : States r c U L) :
    (emptyCompletion r c U L hempty z).val.val =
      (storedRows r c U L z, storedColumns r c U L z) := rfl

lemma emptyCompletion_pointLaw_uniform (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U)) (z : States r c U L) :
    pointLaw (emptyCompletion r c U L hempty z) = uniformLaw (α := Fibre r c U L z) :=
  allSmallCompletion_pointLaw_uniform r c U L (allSmall_of_empty r c U hempty) z

lemma empty_of_not_both (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (h : ¬(Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U))) :
    IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U) := by
  by_cases hr : Nonempty (LargeRows r U)
  · right
    exact ⟨fun j => h ⟨hr, ⟨j⟩⟩⟩
  · left
    exact ⟨fun i => hr ⟨i⟩⟩

def emptyCompletionOfNotBoth (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (h : ¬(Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U))) (z : States r c U L) :
    Fibre r c U L z := emptyCompletion r c U L (empty_of_not_both r c U h) z

lemma emptyCompletionOfNotBoth_views (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (h : ¬(Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U))) (z : States r c U L) :
    (emptyCompletionOfNotBoth r c U L h z).val.val =
      (storedRows r c U L z, storedColumns r c U L z) := rfl

lemma emptyCompletionOfNotBoth_pointLaw_uniform (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (h : ¬(Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U))) (z : States r c U L) :
    pointLaw (emptyCompletionOfNotBoth r c U L h z) = uniformLaw (α := Fibre r c U L z) :=
  emptyCompletion_pointLaw_uniform r c U L (empty_of_not_both r c U h) z

abbrev idealEmptyCompletion (r : I → ℕ) (c : J → ℕ)
    (hempty : IsEmpty (LargeRows r (IdealOracleScales.cutoff (I := I) (J := J))) ∨
      IsEmpty (LargeColumns c (IdealOracleScales.cutoff (I := I) (J := J))))
    (z : States r c (IdealOracleScales.cutoff (I := I) (J := J))
      (IdealOracleScales.padding (I := I) (J := J))) :=
  emptyCompletion r c _ _ hempty z

lemma idealEmptyCompletion_pointLaw_uniform (r : I → ℕ) (c : J → ℕ)
    (hempty : IsEmpty (LargeRows r (IdealOracleScales.cutoff (I := I) (J := J))) ∨
      IsEmpty (LargeColumns c (IdealOracleScales.cutoff (I := I) (J := J))))
    (z : States r c (IdealOracleScales.cutoff (I := I) (J := J))
      (IdealOracleScales.padding (I := I) (J := J))) :
    pointLaw (idealEmptyCompletion r c hempty z) = uniformLaw (α := Fibre r c _ _ z) :=
  emptyCompletion_pointLaw_uniform r c _ _ hempty z

section FiniteCode
variable {m n q : ℕ}

def profileInput (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (e : Fin q ≃ Cells (firstPaperSmall r c U)) (z : States r c U L) : ReconstructionInput :=
  (((List.ofFn r, List.ofFn c),
    (cellCatalog (firstPaperSmall r c U) e,
      (viewList (firstPaperSmall r c U) e (physicalProfile _ (capacity r c U L) r c L z) false,
       viewList (firstPaperSmall r c U) e (physicalProfile _ (capacity r c U L) r c L z) true))), U)

/-- Exact semantics of both computed matrices, including defect states.
It does not turn the row matrix into an ordinary table before balance. -/
theorem reconstructViews_profile_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (hsmall : ∀ i j, firstPaperSmall r c U i j = true) (z : States r c U L) :
    reconstructViews (profileInput r c U L e z) =
      (matrixCode (allSmallCompletion r c U L hsmall z).val.val.1,
       matrixCode (allSmallCompletion r c U L hsmall z).val.val.2) := by
  apply Prod.ext
  · change outputMatrix ((List.ofFn r, List.ofFn c), retainedData
      (cellCatalog (firstPaperSmall r c U) e,
        viewList (firstPaperSmall r c U) e (physicalProfile _ (capacity r c U L) r c L z) false)) = _
    rw [outputMatrix_code]
    apply congrArg matrixCode
    funext i j
    rw [retainedData_entry _ _ _ _ ((mem_cellCatalog _ e (i, j)).mpr (hsmall i j)),
      lookupView_eq]
    rw [allSmallCompletion_views]
    rfl
  · change outputMatrix ((List.ofFn r, List.ofFn c), retainedData
      (cellCatalog (firstPaperSmall r c U) e,
        complementValues (U,
          viewList (firstPaperSmall r c U) e (physicalProfile _ (capacity r c U L) r c L z) true))) = _
    rw [outputMatrix_code]
    apply congrArg matrixCode
    funext i j
    rw [retainedData_entry _ _ _ _ ((mem_cellCatalog _ e (i, j)).mpr (hsmall i j)),
      lookupComplement_eq _ e (capacity r c U L) _ U
        (fun a => capacity_small r c U L a.val.1 a.val.2 a.property)]
    rw [allSmallCompletion_views]
    simp only [storedColumns, smallQ, smallView, dite_eq_left (hsmall i j)]

/-- Data from the actual computed catalogue and stored profile lists. -/
def computedInput (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ) (z : States r c U L) :
    ReconstructionInput :=
  (((List.ofFn r, List.ofFn c),
    (PhysicalComputedProposal.computedCatalog r c U,
      PhysicalComputedProposal.computedStateCode r c U L z)), U)

lemma computedInput_eq_profileInput (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ) (z : States r c U L) :
    computedInput r c U L z =
      profileInput r c U L (PhysicalComputedProposal.computedCellEquiv r c U) z := by
  unfold computedInput profileInput PhysicalComputedProposal.computedStateCode
    PhysicalComputedProposal.stateCode profileCode
  rw [PhysicalComputedProposal.computedCellEquiv_catalog]

theorem reconstructViews_computed_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U)) (z : States r c U L) :
    reconstructViews (computedInput r c U L z) =
      (matrixCode (emptyCompletion r c U L hempty z).val.val.1,
       matrixCode (emptyCompletion r c U L hempty z).val.val.2) := by
  rw [computedInput_eq_profileInput]
  exact reconstructViews_profile_code r c U L _ (allSmall_of_empty r c U hempty) z

theorem reconstructViews_computed_not_both_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (h : ¬(Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U))) (z : States r c U L) :
    reconstructViews (computedInput r c U L z) =
      (matrixCode (emptyCompletionOfNotBoth r c U L h z).val.val.1,
       matrixCode (emptyCompletionOfNotBoth r c U L h z).val.val.2) :=
  reconstructViews_computed_code r c U L (empty_of_not_both r c U h) z

lemma empty_of_no_large_lists (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ)
    (h : (largeIndices (U, List.ofFn r)).length = 0 ∨
      (largeIndices (U, List.ofFn c)).length = 0) :
    IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U) := by
  rcases h with hr | hc
  · left
    exact ⟨fun i => by have hp := largeIndices_pos r U i; omega⟩
  · right
    exact ⟨fun j => by have hp := largeIndices_pos c U j; omega⟩

end FiniteCode
end
end Math115.PhysicalEmptyCompletion
