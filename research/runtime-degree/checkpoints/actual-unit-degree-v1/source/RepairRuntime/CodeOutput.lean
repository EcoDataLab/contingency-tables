import RepairRuntime.BaseDegree
namespace Math115.RepairRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open ProfilePrograms Math115.DegreeBounds Math115.PrinterRuntimeNext Math115.AffineMapWithNext
open Math115.UnitRuntimeNext
noncomputable section
variable {A B : Type} [Codec A] [Codec B]
/-- Extract a size certificate from an already proved exact charged certificate.
Used below only for primitive projection/pair DAGs of degree one. -/
lemma output_of_typed {f : A→B} {F : Realizer f} {e : ℕ} (hF : Typed F e) : OutputBound f e := by
  obtain ⟨p,hp,hpb⟩ := hF
  exact ⟨p,hp,fun z => (Nat.le_add_left _ _).trans (hpb z)⟩
lemma output_listExchange : OutputBound listExchange 2 := by
  refine ⟨4*X^2+10*X+1,?_,fun z => ?_⟩
  · have h2 : (4*X^2 : Polynomial ℕ).natDegree≤2 := by
      simpa using degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree≤2 by simp)
    have h1 : (10*X : Polynomial ℕ).natDegree≤1 := by
      simpa using degree_scale 10 (show (X : Polynomial ℕ).natDegree≤1 by simp)
    exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h2 (h1.trans (by decide))) (by simp)
  · simpa only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one] using listExchange_output_weight z
lemma output_listDifference : OutputBound listDifference 2 := by
  refine ⟨4*X^2+6*X+1,?_,?_⟩
  · have h2 : (4*X^2 : Polynomial ℕ).natDegree≤2 := by
      simpa using degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree≤2 by simp)
    have h1 : (6*X : Polynomial ℕ).natDegree≤1 := by
      simpa using degree_scale 6 (show (X : Polynomial ℕ).natDegree≤1 by simp)
    exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h2 (h1.trans (by decide))) (by simp)
  · rintro ⟨xs,ys⟩
    let S := weight (xs,ys)
    have hl : ys.length≤S := (list_length_le_weight ys).trans (weight_snd (xs,ys))
    have hi : ∀ i∈List.range ys.length,weight (differenceEntry ((xs,ys),i))≤4*S+5 := by
      intro i hi
      have hsub := weight_nat_small (Nat.sub_le (xs.getD i 0) (ys.getD i 0))
      have hget := getD_zero_weight xs i
      have hx : weight xs≤S := by dsimp [S]; rw [weight_prod]; omega
      change weight (xs.getD i 0-ys.getD i 0) ≤ _
      omega
    have hm := weight_map_bound (as:=List.range ys.length) (f:=fun i => differenceEntry ((xs,ys),i)) hi
    simp only [List.length_range] at hm
    simp only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
    change weight ((List.range ys.length).map (fun i => differenceEntry ((xs,ys),i))) ≤4*S^2+6*S+1
    nlinarith [Nat.mul_le_mul_right (4*S+6) hl]
lemma output_crossingIndex : OutputBound crossingIndex 1 := by
  refine ⟨4*X+1,by simpa using degree_affine 4 1,fun z => ?_⟩
  have hi : crossingIndex z≤z.1.length := List.idxOf_le_length
  have hl := (list_length_le_weight z.1).trans (weight_fst z)
  have hn := Math115.RetryRuntimeNext.weight_nat_numeric (crossingIndex z)
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  omega
lemma output_repairRows : OutputBound
    (fun z : RepairInput => listExchange (z.1,(z.2.2.2,z.2.2.1))) 2 := by
  exact output_composition
    (output_of_typed (typed_pair (typed_first (A:=List ℕ) (B:=List ℕ×(ℕ×ℕ))) (typed_pair
      (typed_composition (typed_composition typed_second typed_second) typed_second)
      (typed_composition (typed_composition typed_second typed_second) typed_first)))) output_listExchange
lemma output_repairedViews : OutputBound repairedViews 4 := by
  exact output_pair output_repairRows (output_composition
    (output_pair (output_of_typed (typed_composition (typed_second (A:=List ℕ) (B:=List ℕ×(ℕ×ℕ))) typed_first))
      output_repairRows) output_listDifference)
lemma output_backwardRows : OutputBound backwardRows 2 := by
  exact output_composition
    (output_of_typed (typed_pair (typed_first (A:=List ℕ) (B:=List ℕ×(ℕ×(ℕ×ℕ))))
      (typed_composition (typed_composition typed_second typed_second) typed_second))) output_listExchange
lemma output_backwardColumns : OutputBound backwardColumns 4 := by
  exact output_composition (output_pair output_backwardRows
    (output_of_typed (typed_pair
      (typed_composition (typed_composition (typed_second (A:=List ℕ) (B:=List ℕ×(ℕ×(ℕ×ℕ)))) typed_second) typed_first)
      (typed_composition (typed_composition (typed_composition typed_second typed_second) typed_second) typed_first)))) output_listExchange
lemma output_backwardViews : OutputBound backwardViews 8 := by
  exact output_pair output_backwardRows (output_composition
    (output_pair (output_of_typed (typed_composition (typed_second (A:=List ℕ) (B:=List ℕ×(ℕ×(ℕ×ℕ)))) typed_first))
      output_backwardColumns) output_listDifference)
lemma output_repairDataCaps : OutputBound
    (fun z : LabelledRepairData => capacityList (z.1.2,z.1.1.2.1)) 2 :=
  output_composition (output_of_typed (typed_pair (typed_composition (typed_first (A:=RepairData) (B:=ℕ×ℕ)) typed_second)
    typed_repairDataRows)) capacityList_output
lemma output_repairDataCross : OutputBound
    (fun z : LabelledRepairData => crossingIndex (z.1.1.1,z.2)) 1 :=
  output_composition (output_of_typed (typed_pair typed_repairDataCatalog typed_second)) output_crossingIndex
lemma output_forwardRepairCode : OutputBound forwardRepairCode 8 := by
  exact output_composition (output_pair (output_of_typed typed_repairDataRows)
    (output_pair output_repairDataCaps (output_pair
      (output_of_typed (typed_composition (typed_second (A:=RepairData) (B:=ℕ×ℕ)) typed_second))
      output_repairDataCross))) output_repairedViews
lemma output_inverseRepairCode : OutputBound inverseRepairCode 16 := by
  exact output_composition (output_pair (output_of_typed typed_repairDataRows)
    (output_pair output_repairDataCaps (output_pair
      (output_of_typed (typed_composition (typed_second (A:=RepairData) (B:=ℕ×ℕ)) typed_first))
      (output_pair
        (output_of_typed (typed_composition (typed_second (A:=RepairData) (B:=ℕ×ℕ)) typed_second))
        output_repairDataCross)))) output_backwardViews
end
end Math115.RepairRuntimeNext
