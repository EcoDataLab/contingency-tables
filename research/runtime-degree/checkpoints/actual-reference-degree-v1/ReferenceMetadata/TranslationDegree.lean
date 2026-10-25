import ReferenceRuntime.DenseWidthCoreDegree
import RepairRuntime.OutputHelpers
import OAI.Combinatorics.ContingencyTables.Machines.TranslationDecisionProgram

namespace Math115.ReferenceMetadata
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds Math115.DrawDegree Math115.CatalogueDegreeV1
open Math115.ReferenceRuntimeNext Math115.ListRepeatDegreeV1 Math115.WordCountSeedDegrees
open DensePrograms ProfilePrograms
set_option maxHeartbeats 1200000
noncomputable section

lemma typed_starParts : Typed starPartsRealizer 78 := by
  unfold starPartsRealizer
  exact typed_composition
    (typed_pair (typed_pair typed_first (typed_constant [])) typed_second) typed_completionParts

lemma typed_translationParts : Typed translationPartsRealizer 78 := by
  have ho : Typed (composition (pair (composition
      (first (A:=MarginPair×MarginPair) (B:=ℕ×ℕ)) first) second) starPartsRealizer) 78 :=
    typed_composition (typed_pair (typed_composition typed_first typed_first) typed_second) typed_starParts
  have hn : Typed (composition (pair (composition
      (first (A:=MarginPair×MarginPair) (B:=ℕ×ℕ)) second) second) starPartsRealizer) 78 :=
    typed_composition (typed_pair (typed_composition typed_first typed_second) typed_second) typed_starParts
  unfold translationPartsRealizer
  exact typed_pair
    (typed_composition (typed_pair (typed_composition hn typed_first)
      (typed_composition ho typed_second)) typed_add)
    (typed_composition (typed_pair (typed_composition hn typed_second)
      (typed_composition ho typed_first)) typed_add)

lemma typed_translatedCell : Typed translatedCellRealizer 78 := by
  have hp : Typed (composition (pair (composition
      (first (A:=TranslationData) (B:=ℕ×ℕ)) first) second) translationPartsRealizer) 78 :=
    typed_composition (typed_pair (typed_composition typed_first typed_first) typed_second) typed_translationParts
  have he : Typed (composition (pair (composition
      (first (A:=TranslationData) (B:=ℕ×ℕ)) second) second) matrixEntryRealizer) 4 :=
    typed_composition (typed_pair (typed_composition typed_first typed_second) typed_second) typed_denseMatrixEntry
  unfold translatedCellRealizer
  exact typed_composition (typed_pair (typed_composition hp typed_second)
    (typed_composition (typed_pair he (typed_composition hp typed_first)) typed_add)) typed_leNat

lemma typed_translatedCell_map : Typed (mapWith translatedCellRealizer) 79 := by
  apply Math115.RepairRuntimeNext.typed_mapWith_poly_output (d:=0) typed_translatedCell (by decide)
  refine ⟨3, (by simp), fun z => ?_⟩
  simpa using weight_bool (translatedCell z)

lemma translationPreparation_weight (z : TranslationData) :
    weight (z,cellPairs z.1.1) ≤
      (8*X^3+4*X^2+X+2 : Polynomial ℕ).eval (weight z) := by
  have hc := weight_cellPairs_output z.1.1
  have hz : weight z.1.1 ≤ weight z := (weight_fst _).trans (weight_fst _)
  have hh : weight (cellPairs z.1.1) ≤ 8*(weight z)^3+4*(weight z)^2+1 := by
    apply hc.trans
    gcongr <;> exact hz
  simp only [weight_prod,eval_add,eval_mul,eval_pow,eval_ofNat,eval_X]
  omega

lemma translationPreparation_degree :
    (8*X^3+4*X^2+X+2 : Polynomial ℕ).natDegree ≤ 3 := by
  have h1 := degree_scale 8 (show (X^3 : Polynomial ℕ).natDegree ≤ 3 by simp)
  have h2 := degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree ≤ 2 by simp)
  have h3 := degree_add (degree_add h1 h2) (show (X : Polynomial ℕ).natDegree ≤ 1 by simp)
  simpa using degree_add h3 (show (2 : Polynomial ℕ).natDegree ≤ 0 by simp)

lemma translatedCells_weight (z : TranslationData) :
    weight ((cellPairs z.1.1).map (fun ij => translatedCell (z,ij))) ≤
      (4*X^2+1 : Polynomial ℕ).eval (weight z) := by
  have hr : z.1.1.1.length ≤ weight z :=
    (list_length_le_weight _).trans ((weight_fst _).trans ((weight_fst _).trans (weight_fst _)))
  have hc : z.1.1.2.length ≤ weight z :=
    (list_length_le_weight _).trans ((weight_snd _).trans ((weight_fst _).trans (weight_fst _)))
  have hl : (cellPairs z.1.1).length ≤ (weight z)^2 := by
    simpa only [cellPairs,List.length_map,List.length_range,pow_two] using Nat.mul_le_mul hr hc
  have hm := weight_map_bound (as:=cellPairs z.1.1) (f:=fun ij => translatedCell (z,ij))
    (N:=3) (fun ij _ => weight_bool _)
  simp only [eval_add,eval_mul,eval_pow,eval_ofNat,eval_X,eval_one]
  nlinarith

/-- Original cell enumeration, every translation test, full Boolean map and
the original all fold. Validity/shape/success assumptions are not required. -/
theorem typed_translationValid : Typed translationValidRealizer 504 := by
  have hp : Typed (pair (identity (A:=TranslationData))
      (composition (composition first first) cellPairsRealizer)) 504 :=
    typed_pair typed_identity (typed_composition (typed_composition typed_first typed_first) typed_cellPairs)
  have hm := Math115.ScalarOutputDegree.typed_composition_from_output_size hp typed_translatedCell_map
    (8*X^3+4*X^2+X+2) translationPreparation_degree translationPreparation_weight
  have hd : (4*X^2+1 : Polynomial ℕ).natDegree ≤ 2 := by
    simpa using degree_add (degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree ≤ 2 by simp))
      (show (1 : Polynomial ℕ).natDegree ≤ 0 by simp)
  have h := Math115.ScalarOutputDegree.typed_composition_from_output_size hm typed_all
    (4*X^2+1) hd (by intro z; exact translatedCells_weight z)
  unfold translationValidRealizer
  apply typed_congr
  simpa using h

#check typed_translationValid
#print axioms typed_translationValid
end
end Math115.ReferenceMetadata
