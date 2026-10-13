import InitialRuntime.GreedyDegree
import DrawRuntime.BranchDegree
import ResearchBounds.SmallCellCatalogueDegree
import OAI.Combinatorics.ContingencyTables.Sampling.OriginalProfileProgram

set_option maxHeartbeats 1000000
namespace Math115.InitialRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open ProfilePrograms DensePrograms Math115.DegreeBounds
open Math115.DrawDegree Math115.CatalogueDegreeV1 Math115.WordCountSeedDegrees
open Math115.ScalarCircuitDegreeV2
noncomputable section

lemma typed_idealCatalog : Typed PhysicalComputedProposal.idealMarginCatalogRealizer 1008 := by
  have hinput := circuit_pair (circuit_identity (A:=List ℕ × List ℕ)) Math115.DrawRuntimeNext.circuit_cutoff
  unfold PhysicalComputedProposal.idealMarginCatalogRealizer
  obtain ⟨p,hp,hpb⟩ := typed_composition_linear hinput.1 typed_smallCellCatalog hinput.2
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [Function.comp_apply,id_eq,PhysicalComputedProposal.idealMarginCatalog] using hpb z

lemma typed_idealPrepare : Typed PhysicalComputedProposal.idealPrepareProfileInputRealizer 1008 := by
  unfold PhysicalComputedProposal.idealPrepareProfileInputRealizer
  apply typed_pair_same (e:=1008)
  · apply typed_pair_same (e:=1008)
    · exact typed_pair_same (e:=1008)
        (by simpa using typed_composition_pos typed_first typed_idealCatalog (by decide))
        (typed_weaken typed_second (by decide)) (by decide)
    · exact typed_weaken typed_first (by decide)
    · decide
  · exact typed_weaken
      (typed_composition_pos typed_first Math115.DrawRuntimeNext.circuit_cutoff.1 (by decide)) (by decide)
  · decide

lemma typed_idealPadding : Typed LatticeSamplerPreparation.idealPaddingRealizer 6 := by
  unfold LatticeSamplerPreparation.idealPaddingRealizer
  obtain ⟨p,hp,hpb⟩ := (circuit_composition
    (circuit_pair (circuit_constant (A:=List ℕ × List ℕ) 3) Math115.DrawRuntimeNext.circuit_dimension)
    circuit_multiply).1
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [LatticeSamplerPreparation.idealPadding,Function.comp_apply,id_eq] using hpb z

lemma typed_matrixEntry : Typed matrixEntryRealizer 4 := by
  have hinput : Typed (pair (first (A:=MatrixCode) (B:=ℕ×ℕ))
      (composition (second (A:=MatrixCode) (B:=ℕ×ℕ)) (first (A:=ℕ) (B:=ℕ)))) 1 :=
    typed_pair_same typed_first (typed_composition_pos typed_second typed_first (by decide)) (by decide)
  have hrow : Typed (composition (pair (first (A:=MatrixCode) (B:=ℕ×ℕ))
      (composition second first)) (getDFast ([] : List ℕ))) 2 :=
    typed_composition_pos hinput (typed_getDFast ([] : List ℕ)) (by decide)
  have harg : Typed (pair (composition (pair (first (A:=MatrixCode) (B:=ℕ×ℕ))
      (composition second first)) (getDFast ([] : List ℕ))) (composition second second)) 2 :=
    typed_pair_same hrow (typed_weaken (typed_composition_pos typed_second typed_second (by decide)) (by decide)) (by decide)
  unfold matrixEntryRealizer
  obtain ⟨p,hp,hpb⟩ := typed_composition_pos harg (typed_getDFast 0) (by decide)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [matrixEntry,Function.comp_apply,id_eq] using hpb z

lemma typed_originalFirstView : Typed originalFirstViewRealizer 42 := by
  have harg : Typed (pair (second (A:=List (ℕ×ℕ)×ℕ) (B:=MatrixCode))
      (composition (first (A:=List (ℕ×ℕ)×ℕ) (B:=MatrixCode)) (first (A:=List (ℕ×ℕ)) (B:=ℕ)))) 1 :=
    typed_pair_same typed_second (typed_composition_pos typed_first typed_first (by decide)) (by decide)
  unfold originalFirstViewRealizer
  obtain ⟨p,hp,hpb⟩ := typed_composition_pos harg
    (typed_mapWith typed_matrixEntry (by decide)) (by decide)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [originalFirstView,Function.comp_apply,id_eq] using hpb z

lemma typed_originalViews : Typed originalViewsRealizer 252 := by
  have hcomplement : Typed complementValuesRealizer 6 := by
    unfold complementValuesRealizer
    obtain ⟨p,hp,hpb⟩ := typed_mapWith typed_subtract_actual (by decide)
    refine ⟨p,(by simpa using hp),fun z => ?_⟩
    simpa only [complementValues] using hpb z
  have harg : Typed (pair (composition first second) originalFirstViewRealizer) 42 :=
    typed_pair_same (typed_weaken (typed_composition_pos typed_first typed_second (by decide)) (by decide))
      typed_originalFirstView (by decide)
  have hsecond : Typed (composition (pair (composition first second) originalFirstViewRealizer) complementValuesRealizer) 252 :=
    by simpa using typed_composition_pos harg hcomplement (by decide)
  unfold originalViewsRealizer
  obtain ⟨p,hp,hpb⟩ := typed_pair_same
    (typed_weaken typed_originalFirstView (by decide : 42 ≤ 252)) hsecond (by decide)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [originalViews,Function.comp_apply,id_eq] using hpb z

theorem typed_actual_initialFallback : Typed LatticeSamplerPreparation.initialFallbackRealizer 18 :=
  typed_actual_greedyTable

lemma typed_initialViewInput : Typed LatticeSamplerPreparation.initialViewInputRealizer 1008 := by
  unfold LatticeSamplerPreparation.initialViewInputRealizer
  exact typed_pair_same (e:=1008)
    (typed_pair_same (e:=1008) typed_idealCatalog
      (typed_weaken Math115.DrawRuntimeNext.circuit_cutoff.1 (by decide)) (by decide))
    (typed_weaken typed_actual_greedyTable (by decide)) (by decide)

lemma idealCatalog_weight_output (z : List ℕ × List ℕ) :
    weight (PhysicalComputedProposal.idealMarginCatalog z) ≤ 8*(weight z)^3+4*(weight z)^2+1 := by
  exact (weight_sublist (List.filter_sublist
    (p:=fun a => smallCellTest ((z,PhysicalComputedProposal.idealMarginThreshold z),a))
    (l:=cellPairs z))).trans (weight_cellPairs_output z)

lemma idealCatalog_length_output (z : List ℕ × List ℕ) :
    (PhysicalComputedProposal.idealMarginCatalog z).length ≤ (weight z)^2 := by
  have hf : (PhysicalComputedProposal.idealMarginCatalog z).length ≤ (cellPairs z).length :=
    List.length_filter_le _ _
  have hr : z.1.length ≤ weight z := (list_length_le_weight z.1).trans (by rw [weight_prod]; omega)
  have hc : z.2.length ≤ weight z := (list_length_le_weight z.2).trans (by rw [weight_prod]; omega)
  exact hf.trans (by simpa only [cellPairs,List.length_map,List.length_range,pow_two] using Nat.mul_le_mul hr hc)

lemma degree_initialInputOutput (a b : ℕ) :
    (8*X^3+16*X^2+C (a+24)*X+C (b+15) : Polynomial ℕ).natDegree ≤ 3 := by
  have h1 := degree_scale 8 (show (X^3 : Polynomial ℕ).natDegree ≤ 3 by simp)
  have h2 := degree_scale 16 (show (X^2 : Polynomial ℕ).natDegree ≤ 2 by simp)
  have h3 := degree_scale (a+24) (show (X : Polynomial ℕ).natDegree ≤ 1 by simp)
  have h4 : (C (b+15) : Polynomial ℕ).natDegree ≤ 0 := by rw [Polynomial.natDegree_C]
  simpa using degree_add (degree_add (degree_add h1 h2) h3) h4

lemma initialViewInput_weight_output (a b : ℕ)
    (hthreshold : ∀ z,weight (PhysicalComputedProposal.idealMarginThreshold z) ≤ a*weight z+b)
    (z : List ℕ × List ℕ) :
    weight (LatticeSamplerPreparation.initialViewInput z) ≤
      (8*X^3+16*X^2+C (a+24)*X+C (b+15) : Polynomial ℕ).eval (weight z) := by
  have hc := idealCatalog_weight_output z
  have ht := hthreshold z
  have hg := greedyTable_weight_output z
  simp only [LatticeSamplerPreparation.initialViewInput,LatticeSamplerPreparation.initialFallback,weight_prod]
  simp only [eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_ofNat]
  nlinarith

lemma typed_initialViews : Typed LatticeSamplerPreparation.initialViewsRealizer 1008 := by
  obtain ⟨a,b,hab⟩ := Math115.DrawRuntimeNext.circuit_cutoff.2
  unfold LatticeSamplerPreparation.initialViewsRealizer
  obtain ⟨p,hp,hpb⟩ := Math115.ScalarOutputDegree.typed_composition_from_output_size
    typed_initialViewInput typed_originalViews
    (8*X^3+16*X^2+C (a+24)*X+C (b+15)) (degree_initialInputOutput a b)
    (initialViewInput_weight_output a b hab)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [LatticeSamplerPreparation.initialViews,Function.comp_apply,id_eq] using hpb z

lemma matrixEntry_weight_bound (M : MatrixCode) (i j : ℕ) :
    weight (matrixEntry (M,(i,j))) ≤ weight M+2 := by
  have hr := weight_getD_bound M i ([] : List ℕ)
  have hc := weight_getD_bound (M.getD i []) j 0
  norm_num [weight_nil,weight_nat] at hr hc
  exact hc.trans (by omega)

lemma initialFirstView_weight_output (z : List ℕ × List ℕ) :
    weight (originalFirstView (LatticeSamplerPreparation.initialViewInput z)) ≤
      12*(weight z)^4+24*(weight z)^3+15*(weight z)^2+1 := by
  let S := weight z
  have hm := greedyTable_weight_output z
  have hl := idealCatalog_length_output z
  have hh := weight_map_bound
    (as:=PhysicalComputedProposal.idealMarginCatalog z)
    (f:=fun ij => matrixEntry (GreedyFeasibleTable.listMatrix z.1 z.2,ij))
    (N:=12*(S+1)^2+2) (by
      intro ij _
      exact (matrixEntry_weight_bound _ ij.1 ij.2).trans (by dsimp [S]; omega))
  have hp := Nat.mul_le_mul_right (12*(S+1)^2+3) hl
  change weight ((PhysicalComputedProposal.idealMarginCatalog z).map
    (fun ij => matrixEntry (GreedyFeasibleTable.listMatrix z.1 z.2,ij))) ≤ _
  dsimp only [S] at hh hp
  nlinarith only [hh,hp]

lemma initialViews_weight_output (a b : ℕ)
    (hthreshold : ∀ z,weight (PhysicalComputedProposal.idealMarginThreshold z) ≤ a*weight z+b)
    (z : List ℕ × List ℕ) :
    weight (LatticeSamplerPreparation.initialViews z) ≤
      12*(weight z)^4+(24+4*a)*(weight z)^3+(17+4*b)*(weight z)^2+3 := by
  let V := originalFirstView (LatticeSamplerPreparation.initialViewInput z)
  have hfirst := initialFirstView_weight_output z
  have hl : V.length ≤ (weight z)^2 := by
    simpa only [V,originalFirstView,List.length_map,LatticeSamplerPreparation.initialViewInput] using idealCatalog_length_output z
  have ht := hthreshold z
  have hm := weight_map_bound (as:=V) (f:=fun x => PhysicalComputedProposal.idealMarginThreshold z-x)
    (N:=4*(a*weight z+b)+1) (by
      intro x _
      exact (weight_nat_small (Nat.sub_le _ _)).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 ht) 1))
  have hp := Nat.mul_le_mul_right (4*(a*weight z+b)+2) hl
  change weight (V,complementValues (PhysicalComputedProposal.idealMarginThreshold z,V)) ≤ _
  rw [weight_prod]
  unfold complementValues at *
  nlinarith only [hfirst,hm,hp]

lemma degree_initialViewsOutput (a b : ℕ) :
    (12*X^4+C (24+4*a)*X^3+C (17+4*b)*X^2+X+4 : Polynomial ℕ).natDegree ≤ 4 := by
  have h1 := degree_scale 12 (show (X^4 : Polynomial ℕ).natDegree ≤ 4 by simp)
  have h2 := degree_scale (24+4*a) (show (X^3 : Polynomial ℕ).natDegree ≤ 3 by simp)
  have h3 := degree_scale (17+4*b) (show (X^2 : Polynomial ℕ).natDegree ≤ 2 by simp)
  have h4 : (X : Polynomial ℕ).natDegree ≤ 1 := by simp
  have h5 : (4 : Polynomial ℕ).natDegree ≤ 0 := by simp
  simpa using degree_add (degree_add (degree_add (degree_add h1 h2) h3) h4) h5

lemma typed_initialCheck : Typed LatticeSamplerPreparation.initialCheckRealizer 4032 := by
  obtain ⟨a,b,hab⟩ := Math115.DrawRuntimeNext.circuit_cutoff.2
  unfold LatticeSamplerPreparation.initialCheckRealizer
  obtain ⟨p,hp,hpb⟩ := Math115.ScalarOutputDegree.typed_composition_from_output_size
    (typed_pair_same (e:=1008) (typed_weaken typed_identity (by decide)) typed_initialViews (by decide))
    typed_idealPrepare (12*X^4+C (24+4*a)*X^3+C (17+4*b)*X^2+X+4)
    (degree_initialViewsOutput a b) (by
      intro z
      have hh := initialViews_weight_output a b hab z
      simp only [id_eq,weight_prod,eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_ofNat]
      omega)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [LatticeSamplerPreparation.initialCheck,PhysicalComputedProposal.idealPrepareProfileInput,Function.comp_apply,id_eq] using hpb z

/-- Exact initial realizer, for arbitrary literal margin lists and precision.
All inner folds, views, catalogue, preparation, tuple copies and output included.
No equal totals, feasibility, successful parse or desired cost premise. -/
theorem typed_actual_initialConfiguration : Typed LatticeSamplerPreparation.initialConfigurationRealizer 4032 := by
  unfold LatticeSamplerPreparation.initialConfigurationRealizer
  apply typed_pair_same (e:=4032)
  · apply typed_pair_same (e:=4032)
    · exact typed_pair_same (e:=4032)
        (by simpa using typed_composition_pos typed_first typed_initialCheck (by decide))
        (typed_weaken (typed_composition_pos typed_first typed_idealPadding (by decide)) (by decide)) (by decide)
    · exact typed_pair_same (e:=4032)
        (typed_weaken (typed_composition_pos typed_first Math115.DrawRuntimeNext.circuit_dimension.1 (by decide)) (by decide))
        (typed_weaken typed_second (by decide)) (by decide)
    · decide
  · exact typed_weaken (typed_composition_pos typed_first typed_initialViews (by decide)) (by decide)
  · decide

theorem actual_initialConfiguration_polynomial :
    ∃ P : Polynomial ℕ,P.natDegree ≤ 4032 ∧ ∀ z : LatticeSamplerPreparation.Margins × ℕ,
      LatticeSamplerPreparation.initialConfigurationRealizer.cost z+
        weight (LatticeSamplerPreparation.initialConfiguration z) ≤ P.eval (weight z) :=
  typed_actual_initialConfiguration

end
end Math115.InitialRuntimeNext
