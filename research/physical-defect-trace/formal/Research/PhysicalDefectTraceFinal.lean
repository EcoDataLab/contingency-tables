import Research.PhysicalDefectTrace
import Research.PhysicalDefectDegree

namespace Math115.PhysicalDefectTrace
open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallGraphProfiles FiniteExposureVariance
open Math115.ReducedSmallChain Math115.RetainedChainSquare

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

def defectAllowance (r : I → ℕ) (c : J → ℕ) (U : ℕ) : ℕ :=
  4*Fintype.card (Cells (firstPaperSmall r c U))-3

lemma actual_defect_degree (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :
    ∀ d : DefectVertices r c U L,
      (Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) d.val)).card≤
        defectAllowance r c U := by
  intro d
  exact Math115.PhysicalDefectDegree.physical_nonbalanced_degree_le r c U L d.val d.property

omit [LinearOrder I] [LinearOrder J] in
lemma defectAllowance_positive (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (hp : 2≤Fintype.card (Cells (firstPaperSmall r c U))) : 1≤defectAllowance r c U := by
  unfold defectAllowance
  omega

/-- The concrete changed accepted-conductance defect trace. Its exact rational
proposal is1/[2(4p−3)], supported by the proved actual defect degree geometry. -/
def actualRationalTrace (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (DefectVertices r c U L)]
    (hp : 2≤Fintype.card (Cells (firstPaperSmall r c U))) : FiniteChain (DefectVertices r c U L) :=
  rationalPhysicalTrace r c U L (defectAllowance r c U) (defectAllowance_positive r c U hp)
    (actual_defect_degree r c U L)

/-- Complete actual normalized defect trace bound. The actual full variance,
source capacities, acceptance, decomposition, and linear degree are all proved
inputs within the dependency closure, rather than hypotheses of this theorem. -/
theorem actualRationalTrace_poincare_square (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (DefectVertices r c U L)] (hU : 2≤U) (hL : 7≤L)
    (hp : 2≤Fintype.card (Cells (firstPaperSmall r c U))) (g : DefectVertices r c U L → ℝ) :
    (actualRationalTrace r c U L hp).variance g≤
      (32*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^4*(U:ℝ)^2)*
        (actualRationalTrace r c U L hp).energy g :=
  rationalPhysicalTrace_square_of_degree r c U L _ hU hL hp
    (defectAllowance_positive r c U hp) le_rfl (actual_defect_degree r c U L) g

lemma actualRationalTrace_pi (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (DefectVertices r c U L)]
    (hp : 2≤Fintype.card (Cells (firstPaperSmall r c U))) (d : DefectVertices r c U L) :
    (actualRationalTrace r c U L hp).π d=defectWeight r c U L d/(∑ e,defectWeight r c U L e) := rfl

lemma actualRationalTrace_lazy (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (DefectVertices r c U L)]
    (hp : 2≤Fintype.card (Cells (firstPaperSmall r c U))) (d : DefectVertices r c U L) :
    1/2≤(actualRationalTrace r c U L hp).P d d := (actualRationalTrace r c U L hp).lazy d

/-- The chosen source cutoff yields the exact shape-dependent coefficient. -/
theorem actualRationalTrace_poincare_shape_square (r : I → ℕ) (c : J → ℕ)
    (hI : 2≤Fintype.card I) (hJ : 2≤Fintype.card J)
    [Nonempty (DefectVertices r c (squareCutoff (I:=I) (J:=J)) 7)]
    (hp : 2≤Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I:=I) (J:=J)))))
    (g : DefectVertices r c (squareCutoff (I:=I) (J:=J)) 7 → ℝ) :
    (actualRationalTrace r c (squareCutoff (I:=I) (J:=J)) 7 hp).variance g≤
      (3872*(dimensionAllowance (I:=I) (J:=J):ℝ)^6*
        ((Fintype.card I+Fintype.card J-2:ℕ):ℝ)^2)*
        (actualRationalTrace r c (squareCutoff (I:=I) (J:=J)) 7 hp).energy g := by
  let d := dimensionAllowance (I:=I) (J:=J)
  let p := Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I:=I) (J:=J))))
  let s := Fintype.card I+Fintype.card J-2
  have hpd : p≤d := by
    apply (Fintype.card_subtype_le (fun a : I×J => firstPaperSmall r c (squareCutoff (I:=I) (J:=J)) a.1 a.2=true)).trans
    rw [Fintype.card_prod]
    exact dimension_le_allowance
  have hpdR : (p:ℝ)≤(d:ℝ) := by exact_mod_cast hpd
  have hpow : (p:ℝ)^4≤(d:ℝ)^4 := by gcongr
  have hUeq : (squareCutoff (I:=I) (J:=J):ℝ)=11*(d:ℝ)*(s:ℝ) := by
    change ((11*d*s:ℕ):ℝ)=11*(d:ℝ)*(s:ℝ)
    push_cast
    rfl
  have hcoef : 32*(p:ℝ)^4*(squareCutoff (I:=I) (J:=J):ℝ)^2≤
      3872*(d:ℝ)^6*(s:ℝ)^2 := by
    calc
      _ ≤ 32*(d:ℝ)^4*(squareCutoff (I:=I) (J:=J):ℝ)^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤32))
          (sq_nonneg (squareCutoff (I:=I) (J:=J):ℝ))
      _ = _ := by rw [hUeq]; ring
  exact (actualRationalTrace_poincare_square r c _ 7 (squareCutoff_at_least_two hI hJ) (by omega) hp g).trans
    (mul_le_mul_of_nonneg_right hcoef (FiniteChain.energy_nonneg _ g))

/-- Actual rational accepted defect trace at U=11d(m+n−2),L=7 has the universal
431d⁸ normalized Poincare allowance. Nonempty positive defect support is
explicit: this constructor does not assign a trace chain to an empty branch. -/
theorem actualRationalTrace_poincare_d8 (r : I → ℕ) (c : J → ℕ)
    (hI : 2≤Fintype.card I) (hJ : 2≤Fintype.card J)
    [Nonempty (DefectVertices r c (squareCutoff (I:=I) (J:=J)) 7)]
    (hp : 2≤Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I:=I) (J:=J)))))
    (g : DefectVertices r c (squareCutoff (I:=I) (J:=J)) 7 → ℝ) :
    (actualRationalTrace r c (squareCutoff (I:=I) (J:=J)) 7 hp).variance g≤
      (431*(dimensionAllowance (I:=I) (J:=J):ℝ)^8)*
        (actualRationalTrace r c (squareCutoff (I:=I) (J:=J)) 7 hp).energy g := by
  let d := dimensionAllowance (I:=I) (J:=J)
  let s := Fintype.card I+Fintype.card J-2
  have hshapeN : 3*s≤d := by have := shapeWidth_three hI hJ; omega
  have hshape : 3*(s:ℝ)≤d := by exact_mod_cast hshapeN
  have hsquare : (s:ℝ)^2≤(d:ℝ)^2/9 := by nlinarith [sq_nonneg ((d:ℝ)-3*s)]
  have hscalar : 3872*(d:ℝ)^6*(s:ℝ)^2≤431*(d:ℝ)^8 := by
    have hm := mul_le_mul_of_nonneg_left hsquare (by positivity : 0≤3872*(d:ℝ)^6)
    have hdn : 0≤(d:ℝ)^8 := by positivity
    nlinarith only [hm,hdn]
  exact (actualRationalTrace_poincare_shape_square r c hI hJ hp g).trans
    (mul_le_mul_of_nonneg_right hscalar (FiniteChain.energy_nonneg _ g))

end
end Math115.PhysicalDefectTrace

#print axioms Math115.PhysicalDefectTrace.actualRationalTrace_poincare_d8
#check Math115.PhysicalDefectTrace.actualRationalTrace_poincare_d8
