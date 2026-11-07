import Research.AggregateDefectTrace

set_option maxHeartbeats 800000

namespace Math115.AggregateDefectTrace
open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open SmallContextCoordinates CompletionCounts
open Math115.RetainedChainSquare Math115.PhysicalDefectTrace
open Research.ResidualSelectedBudget

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

lemma small_line_count_le {T : Type*} [Fintype T] (v : T → ℕ) (U : ℕ) :
    smallLineCount v U ≤ Fintype.card T := Fintype.card_subtype_le _

/-- Scalar simplification uses a proved large cutoff, not a new kernel cap. -/
lemma aggregateCT_le_line_square (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (hcut : 4*Fintype.card (Cells (firstPaperSmall r c U)) ≤ U+1) :
    aggregateCT r c U ≤ (4*(smallLineCount r U+smallLineCount c U:ℕ)+2:ℝ)*(U:ℝ)^2 := by
  have hcutR : 4*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ) ≤ (U:ℝ)+1 := by exact_mod_cast hcut
  have hm := mul_le_mul_of_nonneg_right hcutR (Nat.cast_nonneg U : (0:ℝ) ≤ U)
  unfold aggregateCT aggregateK0
  push_cast
  nlinarith only [hm]

lemma small_count_le_dimension (r : I → ℕ) (c : J → ℕ) (U : ℕ) :
    Fintype.card (Cells (firstPaperSmall r c U)) ≤ dimensionAllowance (I:=I) (J:=J) := by
  apply (Fintype.card_subtype_le (fun a : I×J => firstPaperSmall r c U a.1 a.2=true)).trans
  rw [Fintype.card_prod]
  exact dimension_le_allowance

lemma squareCutoff_four_small_count (r : I → ℕ) (c : J → ℕ)
    (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J) :
    4*Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I:=I) (J:=J)))) ≤ squareCutoff (I:=I) (J:=J)+1 := by
  have hp := small_count_le_dimension r c (squareCutoff (I:=I) (J:=J))
  have hs : 2 ≤ Fintype.card I+Fintype.card J-2 := by omega
  have hh := Nat.mul_le_mul_left (dimensionAllowance (I:=I) (J:=J)) hs
  unfold squareCutoff at hp ⊢
  nlinarith only [hp,hh]

/-- Every actual small-line count is bounded by the original shape. -/
lemma aggregateCT_le_shape_square (r : I → ℕ) (c : J → ℕ)
    (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J) :
    aggregateCT r c (squareCutoff (I:=I) (J:=J)) ≤ (9*((Fintype.card I+Fintype.card J-2:ℕ):ℝ))*(squareCutoff (I:=I) (J:=J):ℝ)^2 := by
  let U := squareCutoff (I:=I) (J:=J)
  let s := Fintype.card I+Fintype.card J-2
  let k := smallLineCount r U+smallLineCount c U
  have hbase := aggregateCT_le_line_square r c U (squareCutoff_four_small_count r c hI hJ)
  have hk : k ≤ s+2 := by
    have hr := small_line_count_le r U
    have hc := small_line_count_le c U
    dsimp only [k,s]
    omega
  have hs : 2 ≤ s := by dsimp only [s]; omega
  have hkR : (k:ℝ) ≤ (s:ℝ)+2 := by exact_mod_cast hk
  have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hline : 4*(k:ℝ)+2 ≤ 9*(s:ℝ) := by linarith only [hkR,hsR]
  exact hbase.trans (mul_le_mul_of_nonneg_right hline (sq_nonneg (U:ℝ)))

/-- The SAME canonical actual rational trace has the new aggregate shape
bound at the original U=11d(m+n-2),L=7. Nonempty defect support remains explicit. -/
theorem actualRationalTrace_poincare_aggregate_shape (r : I → ℕ) (c : J → ℕ)
    (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J)
    [Nonempty (Math115.PhysicalDefectTrace.DefectVertices r c (squareCutoff (I:=I) (J:=J)) 7)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I:=I) (J:=J)))))
    (g : Math115.PhysicalDefectTrace.DefectVertices r c (squareCutoff (I:=I) (J:=J)) 7 → ℝ) :
    (actualRationalTrace r c (squareCutoff (I:=I) (J:=J)) 7 hp).variance g ≤ (34848*(dimensionAllowance (I:=I) (J:=J):ℝ)^5*
        ((Fintype.card I+Fintype.card J-2:ℕ):ℝ)^3)*
        (actualRationalTrace r c (squareCutoff (I:=I) (J:=J)) 7 hp).energy g := by
  let d := dimensionAllowance (I:=I) (J:=J)
  let p := Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I:=I) (J:=J))))
  let s := Fintype.card I+Fintype.card J-2
  let U := squareCutoff (I:=I) (J:=J)
  have hpdR : (p:ℝ) ≤ (d:ℝ) := by exact_mod_cast small_count_le_dimension r c U
  have hpow : (p:ℝ)^3 ≤ (d:ℝ)^3 := by gcongr
  have hCT := aggregateCT_le_shape_square r c hI hJ
  have hUeq : (U:ℝ)=11*(d:ℝ)*(s:ℝ) := by
    change ((11*d*s:ℕ):ℝ)=11*(d:ℝ)*(s:ℝ)
    push_cast
    rfl
  have hCT0 : 0 ≤ aggregateCT r c U := by
    have hh := aggregateCT_at_least_six r c U (squareCutoff_at_least_two hI hJ) hp
    linarith
  have hcoef : 32*(p:ℝ)^3*aggregateCT r c U ≤ 34848*(d:ℝ)^5*(s:ℝ)^3 := by
    calc
      _ ≤ 32*(d:ℝ)^3*(9*(s:ℝ)*(U:ℝ)^2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ) ≤ 32)) hCT hCT0 (by positivity)
      _ = _ := by rw [hUeq]; ring
  exact (actualRationalTrace_poincare_aggregate r c U 7 (squareCutoff_at_least_two hI hJ) (by omega) hp g).trans
    (mul_le_mul_of_nonneg_right hcoef (FiniteChain.energy_nonneg _ g))

end
end Math115.AggregateDefectTrace
