import Research.RetainedChainSquare
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalOriginalResiduals
import OAI.Combinatorics.ContingencyTables.Sampling.SmallCoordinateSums

namespace Math115.PhysicalDefectTrace

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallGraphProfiles FiniteExposureVariance CompletionTranslation RowMajorEnumeration
open IntegerWeightedTransport FactorialSignatures
open Math115.ReducedSmallChain

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

lemma physical_smallRow_fixed (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x : States r c U L) (i : I) (hi : r i<U) :
    selectedRow (firstPaperSmall r c U) (physicalProfile _ (capacity r c U L) r c L x) false i=r i := by
  let small := firstPaperSmall r c U
  let B := capacity r c U L
  have hcap := physical_paper_capacity small r c (dimensionAllowance (I:=I) (J:=J)) L U dimension_le_allowance
  have hzero := physical_residual_row_zero r c U L B x (hcap x) i (by omega)
  have hbound := (physical_original_residuals small B r c L x (hcap x)).1 i
  have hcount : rowLargeCount small i=0 := by
    simp [rowLargeCount,small,firstPaperSmall,hi]
  rw [selectedRow_eq_smallRow]
  change _=r i
  change r i-smallRow small (smallView small (physicalProfile small B r c L x) false) i+
    rowLargeCount small i*L=0 at hzero
  rw [hcount] at hzero
  dsimp only [small,B] at hzero hbound ⊢
  omega

lemma physical_smallColumn_fixed (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x : States r c U L) (j : J) (hj : c j<U) :
    smallColumn (firstPaperSmall r c U) (capacity r c U L)
      (smallView _ (physicalProfile _ (capacity r c U L) r c L x) true) j=c j := by
  let small := firstPaperSmall r c U
  let B := capacity r c U L
  have hcap := physical_paper_capacity small r c (dimensionAllowance (I:=I) (J:=J)) L U dimension_le_allowance
  have hzero := physical_residual_column_zero r c U L B x (hcap x) j (by omega)
  have hbound := (physical_original_residuals small B r c L x (hcap x)).2 j
  have hcount : columnLargeCount small j=0 := by
    simp [columnLargeCount,small,firstPaperSmall,hj]
  change c j-smallColumn small B (smallView small (physicalProfile small B r c L x) true) j+
    columnLargeCount small j*L=0 at hzero
  rw [hcount] at hzero
  dsimp only [small,B] at hzero hbound ⊢
  omega

lemma physical_selectedColumn_equal (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x y : States r c U L) (j : J) (hj : c j<U) :
    selectedColumn (firstPaperSmall r c U) (physicalProfile _ (capacity r c U L) r c L x) true j=
      selectedColumn (firstPaperSmall r c U) (physicalProfile _ (capacity r c U L) r c L y) true j := by
  let small := firstPaperSmall r c U
  let B := capacity r c U L
  have hx := smallColumn_cast_selected small B (physicalProfile small B r c L x)
    (naturalProfile_bounded x.val.val) j
  have hy := smallColumn_cast_selected small B (physicalProfile small B r c L y)
    (naturalProfile_bounded y.val.val) j
  rw [physical_smallColumn_fixed r c U L x j hj] at hx
  rw [physical_smallColumn_fixed r c U L y j hj] at hy
  dsimp only [small,B] at hx hy ⊢
  omega

end
end Math115.PhysicalDefectTrace

#print axioms Math115.PhysicalDefectTrace.physical_smallRow_fixed
#print axioms Math115.PhysicalDefectTrace.physical_selectedColumn_equal
