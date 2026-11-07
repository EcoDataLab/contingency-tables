import DrawRuntime.RangeSeed

/-! A numerical degree certificate for the exact frozen large-block branch test.
All costs are those of its original TreeTyped realizers, including encoded
output weight. No replacement predicate, codec, or machine is introduced. -/
namespace Math115.DrawRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open ProfilePrograms Math115.DegreeBounds Math115.WordCountSeedDegrees
open Math115.DrawDegree Math115.ListRepeatDegreeV1
open Math115.ScalarCircuitDegreeV2

noncomputable section

lemma circuit_successor : Circuit successor 1 := by
  unfold successor
  apply circuit_congr
  simpa using circuit_composition (circuit_pair circuit_identity (circuit_constant 1)) circuit_add

lemma circuit_cube : Circuit PhysicalComputedProposal.cubeNat 6 := by
  have hs : Circuit squareNat 6 := by
    unfold squareNat
    simpa using circuit_composition (circuit_pair circuit_identity circuit_identity) circuit_multiply
  unfold PhysicalComputedProposal.cubeNat
  apply circuit_congr
  simpa using circuit_composition (circuit_pair hs circuit_identity) circuit_multiply

lemma circuit_dimension : Circuit marginDimensionRealizer 6 := by
  have h := circuit_composition (circuit_pair (circuit_constant (A:=List ℕ × List ℕ) 10)
    (circuit_composition (circuit_pair
      (circuit_composition (circuit_composition circuit_first circuit_listLength) circuit_successor)
      (circuit_composition (circuit_composition circuit_second circuit_listLength) circuit_successor))
      circuit_multiply)) circuit_add
  unfold marginDimensionRealizer
  constructor
  · obtain ⟨p,hp,hpb⟩ := h.1
    refine ⟨p,(by simpa using hp),fun z => ?_⟩
    simpa only [marginDimension, Function.comp_apply] using hpb z
  · obtain ⟨a,b,hab⟩ := h.2
    refine ⟨a,b,fun z => ?_⟩
    simpa only [marginDimension, Function.comp_apply] using hab z

lemma circuit_cutoff : Circuit PhysicalComputedProposal.idealMarginThresholdRealizer 6 := by
  unfold PhysicalComputedProposal.idealMarginThresholdRealizer
  apply circuit_congr
  simpa using circuit_composition (circuit_pair (circuit_constant 5)
    (circuit_composition circuit_dimension circuit_cube)) circuit_multiply

lemma typed_boolAnd : Typed boolAnd 1 := by
  unfold boolAnd
  apply typed_congr
  exact typed_choose_same typed_first typed_second (typed_constant false) (by decide)

/-- The actual indexed comparison reads the original margin via getDFast. -/
lemma typed_largeIndexTest : Typed largeIndexTestRealizer 2 := by
  have harg : Typed (pair
      (composition (first (A:=ℕ×List ℕ) (B:=ℕ)) second) second) 1 :=
    typed_pair_same (typed_composition_pos typed_first typed_second (by decide)) typed_second (by decide)
  have hget : Typed (composition (pair
      (composition (first (A:=ℕ×List ℕ) (B:=ℕ)) second) second) (getDFast 0)) 2 :=
    typed_composition_pos harg (typed_getDFast 0) (by decide)
  unfold largeIndexTestRealizer
  exact typed_composition_pos
    (typed_pair_same
      (typed_weaken (typed_composition_pos typed_first typed_first (by decide)) (by decide))
      hget (by decide)) typed_leNat (by decide)

/-- Numeric range construction is bounded by the stored list length, not by
an arbitrary binary encoded number. This discharges the required size premise. -/
lemma typed_storedLengthRange :
    Typed (composition (composition (second (A:=ℕ) (B:=List ℕ)) listLength) range) 3 := by
  apply typed_boundedRange (e:=2) (d:=1)
    (typed_composition_pos typed_second typed_listLength_seed (by decide)) X (by simp)
  intro z
  simpa only [Function.comp_apply, eval_X] using
    (list_length_le_weight z.2).trans (by rw [weight_prod]; omega)

/-- The unchanged filterWith constructs and filters the full index list. -/
theorem typed_largeIndices : Typed largeIndicesRealizer 1008 := by
  have hprep : Typed (pair (identity (A:=ℕ×List ℕ))
      (composition (composition second listLength) range)) 3 :=
    typed_pair_same (typed_weaken typed_identity (by decide)) typed_storedLengthRange (by decide)
  have hfilter : Typed (filterWith largeIndexTestRealizer) 336 := by
    simpa using typed_filterWith typed_largeIndexTest (by decide)
  unfold largeIndicesRealizer
  exact typed_composition_pos hprep hfilter (by decide)

lemma typed_largeRows : Typed LatticeSamplerPreparation.largeRowsRealizer 1008 := by
  have hc := circuit_cutoff
  have hinput : Circuit (pair PhysicalComputedProposal.idealMarginThresholdRealizer
      (first (A:=List ℕ) (B:=List ℕ))) 6 := by
    simpa using circuit_pair hc circuit_first
  unfold LatticeSamplerPreparation.largeRowsRealizer
  obtain ⟨p,hp,hpb⟩ := typed_composition_linear hinput.1 typed_largeIndices hinput.2
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [Function.comp_apply, LatticeSamplerPreparation.largeRows] using hpb z

lemma typed_largeColumns : Typed LatticeSamplerPreparation.largeColumnsRealizer 1008 := by
  have hc := circuit_cutoff
  have hinput : Circuit (pair PhysicalComputedProposal.idealMarginThresholdRealizer
      (second (A:=List ℕ) (B:=List ℕ))) 6 := by
    simpa using circuit_pair hc circuit_second
  unfold LatticeSamplerPreparation.largeColumnsRealizer
  obtain ⟨p,hp,hpb⟩ := typed_composition_linear hinput.1 typed_largeIndices hinput.2
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [Function.comp_apply, LatticeSamplerPreparation.largeColumns] using hpb z

/-- A filtered stored-length range has quadratic encoded weight, independent
of its threshold value. This keeps execution degree separate from output size. -/
lemma largeIndices_weight_bound (u : ℕ) (xs : List ℕ) (S : ℕ) (hxs : xs.length ≤ S) :
    weight (largeIndices (u,xs)) ≤ 4*S^2+2*S+1 := by
  have hf := weight_sublist (List.filter_sublist
    (p:=fun i => largeIndexTest ((u,xs),i)) (l:=List.range xs.length))
  have hm := weight_map_bound (as:=List.range xs.length) (f:=id) (N:=4*S+1) (by
    intro n hn
    have hn' := List.mem_range.mp hn
    exact (weight_nat_numeric n).trans (by omega))
  simp only [List.map_id, List.length_range] at hm
  have hb := Nat.mul_le_mul_right (4*S+2) hxs
  unfold largeIndices
  exact hf.trans (hm.trans (by nlinarith only [hb]))

lemma largeRows_weight_bound (z : List ℕ × List ℕ) :
    weight (LatticeSamplerPreparation.largeRows z) ≤ 4*(weight z)^2+2*weight z+1 := by
  apply largeIndices_weight_bound
  exact (list_length_le_weight z.1).trans (by rw [weight_prod]; omega)

lemma largeColumns_weight_bound (z : List ℕ × List ℕ) :
    weight (LatticeSamplerPreparation.largeColumns z) ≤ 4*(weight z)^2+2*weight z+1 := by
  apply largeIndices_weight_bound
  exact (list_length_le_weight z.2).trans (by rw [weight_prod]; omega)

lemma quadratic_output_degree : (4*X^2+2*X+1 : Polynomial ℕ).natDegree ≤ 2 := by
  have h1 := degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree≤2 by simp)
  have h2 := degree_scale 2 (show (X : Polynomial ℕ).natDegree≤1 by simp)
  simpa using degree_add (degree_add h1 h2) (show (1 : Polynomial ℕ).natDegree≤0 by simp)

/-- One of the seven formerly open ActualDrawSeams fields, globally over
arbitrary encoded margin lists. Equal totals or well-formed sampler inputs are
not assumptions. Costs include threshold preparation, complete range/filter,
list-length folds, comparisons, Boolean conjunction, and encoded output. -/
theorem typed_actual_bothLargeTest :
    Typed LatticeSamplerPreparation.bothLargeTestRealizer 1008 := by
  have hrows : Typed (composition LatticeSamplerPreparation.largeRowsRealizer listLength) 1008 :=
    by
      simpa using Math115.ScalarOutputDegree.typed_composition_from_output_size
        typed_largeRows typed_listLength_seed (4*X^2+2*X+1) quadratic_output_degree
        (fun z => by simpa using largeRows_weight_bound z)
  have hcolumns : Typed (composition LatticeSamplerPreparation.largeColumnsRealizer listLength) 1008 :=
    by
      simpa using Math115.ScalarOutputDegree.typed_composition_from_output_size
        typed_largeColumns typed_listLength_seed (4*X^2+2*X+1) quadratic_output_degree
        (fun z => by simpa using largeColumns_weight_bound z)
  have hr : Typed (composition (pair (constant 0)
      (composition LatticeSamplerPreparation.largeRowsRealizer listLength)) less) 1008 :=
    typed_composition_pos (typed_pair_same (typed_weaken (typed_constant 0) (by decide)) hrows (by decide))
      typed_less (by decide)
  have hc : Typed (composition (pair (constant 0)
      (composition LatticeSamplerPreparation.largeColumnsRealizer listLength)) less) 1008 :=
    typed_composition_pos (typed_pair_same (typed_weaken (typed_constant 0) (by decide)) hcolumns (by decide))
      typed_less (by decide)
  unfold LatticeSamplerPreparation.bothLargeTestRealizer
  exact typed_composition_pos (typed_pair_same hr hc (by decide)) typed_boolAnd (by decide)

/-- Explicit pointwise charged-work endpoint for the same actual realizer. -/
theorem actual_bothLargeTest_polynomial :
    ∃ p : Polynomial ℕ, p.natDegree ≤ 1008 ∧
      ∀ z : List ℕ × List ℕ,
        LatticeSamplerPreparation.bothLargeTestRealizer.cost z +
          weight (LatticeSamplerPreparation.bothLargeTest z) ≤ p.eval (weight z) :=
  typed_actual_bothLargeTest

end
end Math115.DrawRuntimeNext
