import Research.AggregateShapeTrace

set_option maxHeartbeats 800000

namespace Math115.AggregateDefectTrace
open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open SmallContextCoordinates CompletionCounts
open Math115.RetainedChainSquare Math115.PhysicalDefectTrace

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

/-- A polynomial squared certificate for the bounded-aspect interpretation.
No fractional power notation or variance hypothesis is needed. -/
lemma aggregate_shape_coefficient_sq (d s A : ℝ) (hd : 0 ≤ d) (hs : 0 ≤ s)
    (hA : 0 ≤ A) (haspect : s^2 ≤ A*d) :
    (34848*d^5*s^3)^2 ≤ 34848^2*A^3*d^13 := by
  have hcub : (s^2)^3 ≤ (A*d)^3 := by gcongr
  calc
    _ = 34848^2*d^10*(s^2)^3 := by ring
    _ ≤ 34848^2*d^10*(A*d)^3 :=
      mul_le_mul_of_nonneg_left hcub (by positivity)
    _ = _ := by ring

/-- Actual normalized variance obeys the squared d13 certificate whenever
original dimensions obey s² ≤ A*d. The chain is exactly the canonical trace. -/
theorem actualRationalTrace_poincare_aggregate_aspect_sq (r : I → ℕ) (c : J → ℕ)
    (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J)
    [Nonempty (DefectVertices r c (squareCutoff (I:=I) (J:=J)) 7)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I:=I) (J:=J)))))
    (A : ℝ) (hA : 0 ≤ A)
    (haspect : ((Fintype.card I+Fintype.card J-2:ℕ):ℝ)^2 ≤ A*(dimensionAllowance (I:=I) (J:=J):ℝ))
    (g : DefectVertices r c (squareCutoff (I:=I) (J:=J)) 7 → ℝ) :
    ((actualRationalTrace r c (squareCutoff (I:=I) (J:=J)) 7 hp).variance g)^2 ≤ (34848^2*A^3*(dimensionAllowance (I:=I) (J:=J):ℝ)^13)*
        ((actualRationalTrace r c (squareCutoff (I:=I) (J:=J)) 7 hp).energy g)^2 := by
  let C := actualRationalTrace r c (squareCutoff (I:=I) (J:=J)) 7 hp
  let d := dimensionAllowance (I:=I) (J:=J)
  let s := Fintype.card I+Fintype.card J-2
  let B : ℝ := 34848*(d:ℝ)^5*(s:ℝ)^3
  have hv := actualRationalTrace_poincare_aggregate_shape r c hI hJ hp g
  have hv0 : 0 ≤ C.variance g := C.inner_nonneg _
  have hv2 : (C.variance g)^2 ≤ (B*C.energy g)^2 := by
    simpa only [pow_two] using mul_le_mul hv hv hv0 (hv0.trans hv)
  have hc := aggregate_shape_coefficient_sq (d:ℝ) (s:ℝ) A
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA haspect
  calc
    _ ≤ (B*C.energy g)^2 := hv2
    _ = B^2*(C.energy g)^2 := mul_pow _ _ _
    _ ≤ (34848^2*A^3*(d:ℝ)^13)*(C.energy g)^2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)

end
end Math115.AggregateDefectTrace
