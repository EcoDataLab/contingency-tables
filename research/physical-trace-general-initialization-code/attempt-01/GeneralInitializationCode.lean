/-
SPDX-License-Identifier: Apache-2.0
Literal catalog-ordered inverse profile code and computational searched
initializer, with pointwise correspondence to the actual semantic start.
No encoded realizer or initialization runtime bound is asserted.
-/
import ResearchPhysicalTraceJoin.GeneralInitialization
import Math115.PhysicalComputedProposal

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture SmallContextFibres PaddedCompletions
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace Math115.PhysicalComputedProposal
open scoped BigOperators

/-- Padding is computed on the decoded ordinary matrix, including the large crossing. -/
def listedInitializationPaddedEntry (rs cs : List ℕ) (U L : ℕ) (A : MatrixCode)
    (ij : ℕ × ℕ) : ℕ :=
  matrixEntry (A,ij) + if smallCellTest (((rs,cs),U),ij) then 0 else L

/-- Integer subtraction before toNat matches the inherited inverse transfer,
including coincident source/receiver positions. -/
def listedInitializationTransfer (rs cs : List ℕ) (U L : ℕ) (A : MatrixCode)
    (source receiver ij : ℕ × ℕ) : ℕ :=
  ((listedInitializationPaddedEntry rs cs U L A ij : ℤ) -
    (if ij = source then 1 else 0) + (if ij = receiver then 1 else 0)).toNat

/-- The second list is the profile's capacity complement of the column
view, as required by computedStateCode; both lists use the existing catalog. -/
def listedInverseProfileCode (rs cs : List ℕ) (U L : ℕ) (A : MatrixCode)
    (s t : ℕ × ℕ) : List ℕ × List ℕ :=
  let catalog := smallCellCatalog ((rs,cs),U)
  (catalog.map (listedInitializationTransfer rs cs U L A (t.1,s.2) t),
    catalog.map (fun ij => U - listedInitializationTransfer rs cs U L A (t.1,s.2) s ij))

/-- The existing dimension-recursive greedy matrix, without a semantic choice. -/
def positiveTraceFallbackCode (xs ys : List ℕ) : MatrixCode :=
  matrixCode (GreedyFeasibleTable.matrix (filteredMargin xs) (filteredMargin ys))

/-- Finite first-match label search and explicit inverse arithmetic. The
equal-total input is a proof erased by execution; no feasible table is supplied. -/
def positiveTraceInitializationCode (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) :
    Option (List ℕ × List ℕ) :=
  match initializationLabelSearch (filteredMargin xs) (filteredMargin ys)
      (positiveTraceCutoff xs ys) (positiveTraceFallback xs ys htotal) with
  | none => none
  | some st => some (listedInverseProfileCode (positiveMargins xs) (positiveMargins ys)
      (positiveTraceCutoff xs ys) 7 (positiveTraceFallbackCode xs ys)
      (st.1.1.val,st.1.2.val) (st.2.1.val,st.2.2.val))

open scoped Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

lemma listedInitializationPaddedEntry_code (X : Table r c) (i : Fin m) (j : Fin n) :
    listedInitializationPaddedEntry (List.ofFn r) (List.ofFn c) U L (matrixCode X.val)
      (i.val,j.val) = (inverseTarget r c U L X).val i j := by
  rw [listedInitializationPaddedEntry, matrixEntry_code, listedSmallCellTest_code]
  rfl

lemma listedInitializationTransfer_code (X : Table r c) (source receiver : Fin m × Fin n)
    (i : Fin m) (j : Fin n) :
    listedInitializationTransfer (List.ofFn r) (List.ofFn c) U L (matrixCode X.val)
      (source.1.val,source.2.val) (receiver.1.val,receiver.2.val) (i.val,j.val) =
        (transferInt (inverseTarget r c U L X).val source receiver i j).toNat := by
  rw [listedInitializationTransfer, listedInitializationPaddedEntry_code]
  simp only [transferInt, Prod.mk.injEq, Fin.ext_iff]

private lemma map_computedCatalog (f : (ℕ × ℕ) → ℕ) :
    (computedCatalog r c U).map f = List.ofFn (fun i =>
      f ((computedCellEquiv r c U i).val.1.val,(computedCellEquiv r c U i).val.2.val)) := by
  simpa only [cellCatalog, List.map_ofFn] using
    congrArg (List.map f) (computedCellEquiv_catalog r c U).symm

/-- Pointwise representation theorem for every actual inverse candidate.
The raw constructor is fixed before the valid-input theorem is invoked. -/
theorem listedInverseProfileCode_inverseDefectState (X : Table r c)
    (st : InverseLocalLabels r c U L X) :
    listedInverseProfileCode (List.ofFn r) (List.ofFn c) U L (matrixCode X.val)
      (st.val.1.val.1.val,st.val.1.val.2.val) (st.val.2.val.1.val,st.val.2.val.2.val) =
      computedStateCode r c U L (inverseDefectState r c U L X st).val := by
  have hprofile : physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c L
      (inverseDefectState r c U L X st).val = inverseNaturalProfile r c U L X st.val := rfl
  unfold computedStateCode stateCode
  rw [hprofile]
  unfold listedInverseProfileCode
  change ((computedCatalog r c U).map _, (computedCatalog r c U).map _) = _
  rw [map_computedCatalog, map_computedCatalog]
  apply Prod.ext
  · change List.ofFn _ = List.ofFn _
    congr 1
    funext i
    rw [listedInitializationTransfer_code]
    rfl
  · change List.ofFn _ = List.ofFn _
    congr 1
    funext i
    rw [listedInitializationTransfer_code]
    change U - inverseColumnView (inverseTarget r c U L X).val st.val.1.val st.val.2.val
      (computedCellEquiv r c U i).val.1 (computedCellEquiv r c U i).val.2 =
      capacity r c U L (computedCellEquiv r c U i).val.1
        (computedCellEquiv r c U i).val.2 - _
    rw [capacity_small r c U L _ _ (computedCellEquiv r c U i).property]

lemma positiveTraceFallbackCode_code (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) :
    positiveTraceFallbackCode xs ys = matrixCode (positiveTraceFallback xs ys htotal).val := rfl

/-- The search-driven ordinary definition computes exactly the profile code
of the actual initialized state, without a caller-supplied table or label pair. -/
theorem positiveTraceInitializationCode_initialStart (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) :
    positiveTraceInitializationCode xs ys htotal =
      some (computedStateCode (filteredMargin xs) (filteredMargin ys)
        (positiveTraceCutoff xs ys) 7 (positiveTraceInitialStart xs ys htotal hb).val) := by
  let X := positiveTraceFallback xs ys htotal
  have hg := positiveTraceReference_conditions xs ys hb
  have h := initializationLabelSearch_isSome (filteredMargin xs) (filteredMargin ys)
    (positiveTraceCutoff xs ys) X (filteredMargin_positive xs) (filteredMargin_positive ys)
    hg.1 hg.2.1 (by have hp := hg.2.2.1; omega)
  let st := initializationSupportLabels (filteredMargin xs) (filteredMargin ys)
    (positiveTraceCutoff xs ys) X h
  have he := listedInverseProfileCode_inverseDefectState (filteredMargin xs) (filteredMargin ys)
    (positiveTraceCutoff xs ys) 7 X
    ⟨st.val, (inverseLocalTest_iff_support _ _ _ _ (by decide) X st.val).mpr st.property⟩
  have hsearch := Option.eq_some_of_isSome h
  unfold positiveTraceInitializationCode
  rw [hsearch]
  rw [positiveTraceFallbackCode_code]
  simpa only [show List.ofFn (filteredMargin xs) = positiveMargins xs from
      ofFn_listMargin (positiveMargins xs),
    show List.ofFn (filteredMargin ys) = positiveMargins ys from
      ofFn_listMargin (positiveMargins ys)] using congrArg some he

end
end Math115.PhysicalTraceJoin
