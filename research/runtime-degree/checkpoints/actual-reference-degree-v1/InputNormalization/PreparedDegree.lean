import InputNormalization.SwapDegree

namespace Math115.InputNormalization
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open DensePrograms Math115.DegreeBounds Math115.DrawDegree Math115.InitialRuntimeNext
noncomputable section

lemma typed_swapMargins : Typed swapMarginsRealizer 42 := by
  unfold swapMarginsRealizer
  obtain ⟨p,hp,hpb⟩ := typed_pair_same
    (typed_composition_pos
      (typed_pair_same (typed_composition_pos typed_first typed_first (by decide))
        (typed_composition_pos typed_second typed_first (by decide)) (by decide))
      (typed_swapZeroList (A:=ℕ)) (by decide))
    (typed_composition_pos
      (typed_pair_same (typed_composition_pos typed_first typed_second (by decide))
        (typed_composition_pos typed_second typed_second (by decide)) (by decide))
      (typed_swapZeroList (A:=ℕ)) (by decide)) (by decide)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [swapMargins,Function.comp_apply] using hpb z

lemma swapMargins_weight (i j : ℕ) (rs cs : List ℕ) :
    weight (swapMargins ((i,j),(rs,cs))) ≤ 3*weight (rs,cs)+2 := by
  have hr := swapZeroList_weight i rs
  have hc := swapZeroList_weight j cs
  have h0 : weight (default : ℕ)=1 := by decide
  rw [h0] at hr hc
  simp only [swapMargins,weight_prod]
  omega

lemma typed_swapFlatData : Typed swapFlatDataRealizer 42 := by
  have harg : Typed (pair (first (A:=ℕ×ℕ) (B:=FlatExponentData))
      (composition (composition second first) first)) 1 :=
    typed_pair_same typed_first (typed_composition_pos
      (typed_composition_pos typed_second typed_first (by decide)) typed_first (by decide)) (by decide)
  have hm := typed_composition_pos harg typed_swapMargins (by decide)
  unfold swapFlatDataRealizer
  obtain ⟨p,hp,hpb⟩ := typed_pair_same
    (typed_pair_same hm
      (typed_weaken (typed_composition_pos (typed_composition_pos typed_second typed_first (by decide))
        typed_second (by decide)) (by decide)) (by decide))
    (typed_weaken (typed_composition_pos typed_second typed_second (by decide)) (by decide)) (by decide)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [swapFlatData,Function.comp_apply] using hpb z

lemma swapFlatData_weight (idx : ℕ×ℕ) (z : FlatExponentData) :
    weight (swapFlatData (idx,z)) ≤ 3*weight z+2 := by
  rcases z with ⟨⟨⟨rs,cs⟩,grid⟩,d⟩
  rcases idx with ⟨i,j⟩
  have hh := swapMargins_weight i j rs cs
  simp only [swapFlatData,weight_prod] at hh ⊢
  omega

lemma typed_marginIndices : Typed marginIndicesRealizer 2 := by
  unfold marginIndicesRealizer
  obtain ⟨p,hp,hpb⟩ := typed_pair_same
    (typed_composition_pos (typed_first (A:=List ℕ) (B:=List ℕ)) typed_maximumIndex (by decide))
    (typed_composition_pos typed_second typed_maximumIndex (by decide)) (by decide)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [marginIndices,Function.comp_apply] using hpb z

lemma marginIndices_weight (z : List ℕ×List ℕ) :
    weight (marginIndices z) ≤ 4*weight z+3 := by
  have hr := weight_nat_numeric (maximumIndex z.1)
  have hc := weight_nat_numeric (maximumIndex z.2)
  have hrl := List.idxOf_le_length (l:=z.1) (a:=listMaximum (z.1,0))
  have hcl := List.idxOf_le_length (l:=z.2) (a:=listMaximum (z.2,0))
  have hwr := list_length_le_weight z.1
  have hwc := list_length_le_weight z.2
  rw [←Prod.eta z,weight_prod]
  simp only [marginIndices,maximumIndex,weight_prod] at hr hc ⊢
  omega

lemma typed_drawIndices : Typed drawIndicesRealizer 2 := by
  unfold drawIndicesRealizer
  obtain ⟨p,hp,hpb⟩ := typed_composition_pos
    (typed_composition_pos (typed_composition_pos (typed_composition_pos
      (typed_composition_pos (typed_first (A:=DenseDrawParameters×MatrixCode) (B:=List Bool))
        typed_first (by decide)) typed_first (by decide)) typed_first (by decide)) typed_first (by decide))
    typed_marginIndices (by decide)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [drawIndices,Function.comp_apply] using hpb z

lemma drawIndices_argument_affine : Math115.PrinterRuntimeNext.AffineOutput
    (fun z : DenseDrawData => (drawIndices z,z)) := by
  refine ⟨5,4,fun z => ?_⟩
  have hh := marginIndices_weight z.1.1.1.1.1
  have hm : weight z.1.1.1.1.1 ≤ weight z :=
    (weight_fst _).trans ((weight_fst _).trans ((weight_fst _).trans ((weight_fst _).trans (weight_fst _))))
  change weight (marginIndices z.1.1.1.1.1,z) ≤ _
  rw [weight_prod]
  omega

lemma typed_permuteDrawData : Typed permuteDrawDataRealizer 3614 := by
  have hparams : Typed (composition (composition (second (A:=ℕ×ℕ) (B:=DenseDrawData)) first) first) 1 :=
    typed_composition_pos (typed_composition_pos typed_second typed_first (by decide)) typed_first (by decide)
  have hdata : Typed (composition (pair (first (A:=ℕ×ℕ) (B:=DenseDrawData))
      (composition (composition (composition second first) first) first)) swapFlatDataRealizer) 42 :=
    typed_composition_pos (typed_pair_same typed_first (typed_composition_pos hparams typed_first (by decide)) (by decide))
      typed_swapFlatData (by decide)
  have hfallback : Typed (composition (pair (first (A:=ℕ×ℕ) (B:=DenseDrawData))
      (composition (composition second first) second)) swapMatrixRealizer) 3614 :=
    typed_composition_pos (typed_pair_same typed_first
      (typed_composition_pos (typed_composition_pos typed_second typed_first (by decide)) typed_second (by decide))
      (by decide)) typed_swapMatrix (by decide)
  unfold permuteDrawDataRealizer
  obtain ⟨p,hp,hpb⟩ := typed_pair_same
    (typed_pair_same
      (typed_pair_same (typed_weaken hdata (by decide : 42 ≤ 3614))
        (typed_weaken (typed_composition_pos hparams typed_second (by decide)) (by decide)) (by decide))
      hfallback (by decide))
    (typed_weaken (typed_composition_pos typed_second typed_second (by decide)) (by decide)) (by decide)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [permuteDrawData,Function.comp_apply] using hpb z

lemma permuteDrawData_weight (idx : ℕ×ℕ) (z : DenseDrawData) :
    weight (permuteDrawData (idx,z)) ≤ 18*weight z+16 := by
  rcases z with ⟨⟨⟨F,h⟩,M⟩,bits⟩
  rcases idx with ⟨i,j⟩
  have hF := swapFlatData_weight (i,j) F
  have hM := swapMatrix_weight i j M
  simp only [permuteDrawData,weight_prod] at hF hM ⊢
  omega

/-- All eager normalization work, including the original fallback matrix,
is charged. No shape, maximum-position or input-feasibility premise. -/
theorem typed_preparedDraw : Typed preparedDrawRealizer 3614 := by
  have hp : Typed (pair drawIndicesRealizer (identity (A:=DenseDrawData))) 2 :=
    typed_pair_same typed_drawIndices (typed_weaken typed_identity (by decide)) (by decide)
  unfold preparedDrawRealizer
  obtain ⟨p,hp,hpb⟩ := Math115.PrinterRuntimeNext.typed_comp_affine hp typed_permuteDrawData drawIndices_argument_affine
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [preparedDraw,Function.comp_apply,id_eq] using hpb z

lemma preparedDraw_weight (z : DenseDrawData) :
    weight (preparedDraw z) ≤ 18*weight z+16 := permuteDrawData_weight _ _

end
end Math115.InputNormalization
