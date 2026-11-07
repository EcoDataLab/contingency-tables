import InputNormalization.PreparedDegree
import OAI.Combinatorics.ContingencyTables.Dense.DenseReservedWord
import ResearchBounds.ScalarOutputSizeDegree

set_option maxHeartbeats 4000000

namespace Math115.InputNormalization
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open DensePrograms ProfilePrograms Math115.DegreeBounds Math115.DrawDegree
open Math115.InitialRuntimeNext Math115.CatalogueDegreeV1 Math115.ListRepeatDegreeV1
noncomputable section

lemma typed_zeroGrid : Typed zeroGridRealizer 1008 := by
  have hmap : Typed (OAI.MatchingFPRAS.TreeTyped.map (constant (A:=ℕ×ℕ) (0:ℕ))) 2 :=
    Math115.PrinterRuntimeNext.typed_map_affine (typed_constant 0) (by decide)
      ⟨0,1,fun x => by change 1 ≤ 0*weight x+1; omega⟩
  unfold zeroGridRealizer
  obtain ⟨p,hp,hpb⟩ := typed_composition_pos
    (typed_composition_pos
      (typed_pair_same (typed_composition_pos (typed_first (A:=List ℕ) (B:=List ℕ)) typed_tail (by decide))
        (typed_composition_pos typed_second typed_tail (by decide)) (by decide)) typed_cellPairs (by decide)) hmap (by decide)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [zeroGrid,Function.comp_apply] using hpb z

lemma zeroGrid_weight (z : List ℕ×List ℕ) :
    weight (zeroGrid z) ≤ 2*(weight z)^2+1 := by
  have hr : z.1.tail.length ≤ weight z :=
    (by simp only [List.length_tail]; exact Nat.sub_le _ _ : z.1.tail.length ≤ z.1.length).trans ((list_length_le_weight z.1).trans (weight_fst z))
  have hc : z.2.tail.length ≤ weight z :=
    (by simp only [List.length_tail]; exact Nat.sub_le _ _ : z.2.tail.length ≤ z.2.length).trans ((list_length_le_weight z.2).trans (weight_snd z))
  have hh := weight_map_bound (as:=cellPairs (z.1.tail,z.2.tail)) (f:=fun _ => (0:ℕ))
    (N:=1) (fun x hx => by decide)
  have hl : (cellPairs (z.1.tail,z.2.tail)).length ≤ (weight z)^2 := by
    simpa only [cellPairs,List.length_map,List.length_range,pow_two] using Nat.mul_le_mul hr hc
  unfold zeroGrid
  omega

lemma typed_canonicalInput : Typed canonicalInputRealizer 1008 := by
  have hm : Typed (composition (first (A:=CanonicalParameters) (B:=List Bool)) first) 1 :=
    typed_composition_pos typed_first typed_first (by decide)
  have hd : Typed (composition (first (A:=CanonicalParameters) (B:=List Bool)) second) 1 :=
    typed_composition_pos typed_first typed_second (by decide)
  unfold canonicalInputRealizer
  dsimp only
  exact typed_pair_same
    (typed_pair_same
      (typed_pair_same
        (typed_pair_same
          (typed_pair_same (typed_weaken hm (by decide)) (typed_composition_pos hm typed_zeroGrid (by decide)) (by decide))
          (typed_weaken (typed_composition_pos hd typed_first (by decide)) (by decide)) (by decide))
        (typed_weaken (typed_composition_pos hd typed_second (by decide)) (by decide)) (by decide))
      (typed_weaken (typed_composition_pos hm typed_actual_greedyTable (by decide)) (by decide)) (by decide))
    (typed_weaken typed_second (by decide)) (by decide)

lemma canonicalInput_weight (z : CanonicalDrawData) :
    weight (canonicalInput z) ≤ 20*(weight z+1)^2 := by
  have hg := zeroGrid_weight z.1.1
  have hf := greedyTable_weight_output z.1.1
  have hm : weight z.1.1 ≤ weight z := (weight_fst _).trans (weight_fst _)
  rcases z with ⟨⟨margins,⟨d,h⟩⟩,bits⟩
  simp only [canonicalInput,weight_prod] at hg hf hm ⊢
  nlinarith

lemma degree_quadratic_envelope (a b : ℕ) :
    (C a*(X+C b)^2 : Polynomial ℕ).natDegree ≤ 2 := by
  have hh : (X+C b : Polynomial ℕ).natDegree ≤ 1 := by simpa using degree_affine 1 b
  simpa only [pow_two] using degree_scale a (degree_mul hh hh)

/-- Exact original prepared-parameter realizer. Its eager greedy fallback and
all literal input components are charged before the final parameter projection. -/
theorem typed_preparedCanonicalParameters : Typed preparedCanonicalParametersRealizer 7228 := by
  have hblank : Typed (pair (identity (A:=CanonicalParameters)) (constant ([]:List Bool))) 1 :=
    typed_pair_same typed_identity (typed_constant []) (by decide)
  have hinput := typed_composition_pos hblank typed_canonicalInput (by decide)
  have hout : ∀ z : CanonicalParameters, weight (canonicalInput (z,[])) ≤
      (20*(X+3)^2 : Polynomial ℕ).eval (weight z) := by
    intro z
    have hh := canonicalInput_weight (z,[])
    simp only [weight_prod,weight_nil] at hh
    simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X]
    nlinarith
  have hprep := Math115.ScalarOutputDegree.typed_composition_from_output_size hinput typed_preparedDraw
    (20*(X+3)^2) (degree_quadratic_envelope 20 3) hout
  unfold preparedCanonicalParametersRealizer
  dsimp only
  obtain ⟨p,hp,hpb⟩ := typed_composition_pos hprep
    (typed_composition_pos (typed_first (A:=DenseDrawParameters×MatrixCode) (B:=List Bool)) typed_first (by decide)) (by decide)
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [preparedCanonicalParameters,Function.comp_apply,id_eq] using hpb z

/-- Independent semantic quadratic envelope, separate from the charged-work
polynomial. It applies to every raw canonical parameter tuple. -/
lemma preparedCanonicalParameters_output : ∀ z : CanonicalParameters,
    weight (preparedCanonicalParameters z) ≤
      (360*(X+3)^2+16 : Polynomial ℕ).eval (weight z) := by
  intro z
  have h0 := canonicalInput_weight (z,[])
  have h1 := preparedDraw_weight (canonicalInput (z,[]))
  have h2 : weight (preparedCanonicalParameters z) ≤ weight (preparedDraw (canonicalInput (z,[]))) :=
    (weight_fst _).trans (weight_fst _)
  simp only [weight_prod,weight_nil] at h0
  simp only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X]
  nlinarith

lemma preparedCanonicalParameters_output_degree :
    (360*(X+3)^2+16 : Polynomial ℕ).natDegree ≤ 2 := by
  have hh := degree_quadratic_envelope 360 3
  have hc : (16 : Polynomial ℕ).natDegree ≤ 0 := by simpa using (show (C (16:ℕ) : Polynomial ℕ).natDegree ≤ 0 by rw [natDegree_C])
  simpa using degree_add hh hc

end
end Math115.InputNormalization
