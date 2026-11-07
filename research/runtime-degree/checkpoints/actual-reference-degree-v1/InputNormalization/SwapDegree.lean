import InputNormalization.SwapEnvelope
import ResearchBounds.SmallCellCatalogueDegree

namespace Math115.InputNormalization
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open DensePrograms Math115.DegreeBounds Math115.DrawDegree
open Math115.CatalogueDegreeV1 Math115.WordCountSeedDegrees Math115.ListRepeatDegreeV1
noncomputable section

lemma typed_swapZeroIndex : Typed swapZeroIndexRealizer 1 := by
  unfold swapZeroIndexRealizer
  apply typed_congr
  exact typed_choose_same
    (typed_composition_pos (typed_pair_same typed_second (typed_constant 0) (by decide)) typed_natEqual (by decide))
    typed_first
    (typed_choose_same
      (typed_composition_pos (typed_pair_same typed_second typed_first (by decide)) typed_natEqual (by decide))
      (typed_constant 0) typed_second (by decide)) (by decide)

variable {A : Type} [Codec A] [Inhabited A]

lemma typed_swapZeroEntry : Typed (swapZeroEntryRealizer (A:=A)) 2 := by
  unfold swapZeroEntryRealizer
  exact typed_composition_pos
    (typed_pair_same (typed_composition_pos typed_first typed_second (by decide))
      (typed_composition_pos (typed_pair_same
        (typed_composition_pos typed_first typed_first (by decide)) typed_second (by decide))
        typed_swapZeroIndex (by decide)) (by decide)) (typed_getDFast (default : A)) (by decide)

lemma typed_swapZeroIndices : Typed (swapZeroIndicesRealizer (A:=A)) 3 := by
  unfold swapZeroIndicesRealizer
  apply typed_boundedRange (e:=2) (d:=1)
    (typed_composition_pos (typed_second (A:=ℕ) (B:=List A)) typed_listLength_seed (by decide)) X (by simp)
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.2).trans (weight_snd z)

lemma typed_swapZeroList : Typed (swapZeroListRealizer (A:=A)) 42 := by
  have hprep : Typed (pair (identity (A:=ℕ×List A)) swapZeroIndicesRealizer) 3 :=
    typed_pair_same (typed_weaken typed_identity (by decide)) typed_swapZeroIndices (by decide)
  unfold swapZeroListRealizer
  obtain ⟨p,hp,hpb⟩ := typed_composition_pos hprep (typed_mapWith (typed_swapZeroEntry (A:=A)) (by decide)) (by decide)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [swapZeroList,Function.comp_apply,id_eq] using hpb z

lemma typed_swapMatrixColumns : Typed swapMatrixColumnsRealizer 3614 := by
  unfold swapMatrixColumnsRealizer
  obtain ⟨p,hp,hpb⟩ := typed_mapWith (typed_swapZeroList (A:=ℕ)) (by decide)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [swapMatrixColumns] using hpb z

lemma swapMatrixColumns_weight (j : ℕ) (M : MatrixCode) :
    weight (swapMatrixColumns (j,M)) ≤ 6*weight M := by
  have hz : weight (default : ℕ)=1 := by decide
  have hh := Math115.PrinterRuntimeNext.map_affine_weight (f:=fun row : List ℕ => swapZeroList (j,row)) 3 2
    (fun row => by simpa only [hz] using swapZeroList_weight j row) M
  exact hh

lemma swapMatrix_weight (i j : ℕ) (M : MatrixCode) :
    weight (swapMatrix ((i,j),M)) ≤ 18*weight M+12 := by
  have hh := swapMatrixColumns_weight j (swapZeroList (i,M))
  have hr := swapZeroList_weight i M
  have hd : weight (default : List ℕ)=1 := rfl
  unfold swapMatrix
  rw [hd] at hr
  nlinarith

lemma swapMatrix_prep_affine : Math115.PrinterRuntimeNext.AffineOutput
    (fun z : (ℕ×ℕ)×MatrixCode => (z.1.2,swapZeroList (z.1.1,z.2))) := by
  refine ⟨3,2,?_⟩
  rintro ⟨⟨i,j⟩,M⟩
  have hh := swapZeroList_weight i M
  have hd : weight (default : List ℕ)=1 := rfl
  rw [hd] at hh
  simp only [weight_prod]
  nlinarith

/-- The original eager row/column swap retains all work for arbitrary
indices and ragged matrices. Its affine output bound is proved independently. -/
theorem typed_swapMatrix : Typed swapMatrixRealizer 3614 := by
  have hrow : Typed (composition (pair (composition first first) second) (swapZeroListRealizer (A:=List ℕ))) 42 :=
    typed_composition_pos
      (typed_pair_same (typed_composition_pos
        (typed_first (A:=ℕ×ℕ) (B:=MatrixCode)) typed_first (by decide)) typed_second (by decide))
      (typed_swapZeroList (A:=List ℕ)) (by decide)
  have hprep : Typed (pair (composition (first (A:=ℕ×ℕ) (B:=MatrixCode)) second)
      (composition (pair (composition first first) second) swapZeroListRealizer)) 42 :=
    typed_pair_same (typed_weaken (typed_composition_pos typed_first typed_second (by decide)) (by decide)) hrow (by decide)
  unfold swapMatrixRealizer
  obtain ⟨p,hp,hpb⟩ := Math115.PrinterRuntimeNext.typed_comp_affine hprep typed_swapMatrixColumns swapMatrix_prep_affine
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [swapMatrix,Function.comp_apply,id_eq] using hpb z

end
end Math115.InputNormalization
