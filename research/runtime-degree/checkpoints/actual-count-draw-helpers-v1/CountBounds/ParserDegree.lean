/- Private checkpoint12 candidate, source-only and uncompiled.
The public parser's literal codec, realizer and malformed-input behavior are fixed.
Cost certificates include final encoded output weight. -/
import CountBounds.ListRepeatDegree
import Math115.PublicLatticeSampler

namespace Math115.ParserDegreeV1
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped
open OAI.MatchingFPRAS.LiteralParse OAI.MatchingFPRAS.LiteralCodec
open ProfilePrograms Math115.DegreeBounds Math115.ListRepeatDegreeV1
open Math115.ScalarOutputDegree Polynomial

noncomputable section

lemma typed_val : Typed valRealizer 2 := by
  unfold valRealizer
  exact typed_reencode (typed_composition typed_first Math115.WordCountSeedDegrees.typed_listLength_seed)
    parts Fin.val encode_parts (fun a=>by simp [parts])

lemma typed_eqSymbol (a : Symbol) : Typed (eqSymbol a) 2 := by
  unfold eqSymbol
  apply typed_congr
  exact typed_composition (typed_pair typed_val (typed_constant a.val)) typed_natEqual

lemma typed_numStep : Typed numStepRealizer 6 := by
  unfold numStepRealizer
  apply typed_congr
  simp only [Realizer.mulNat,Realizer.addNat]
  apply typed_choose (e:=2) (t:=1) (u:=6)
  · exact typed_composition typed_first (typed_eqSymbol 3)
  · exact typed_composition (typed_pair (typed_constant 0) typed_second) typed_listCons_arithmetic
  · apply typed_choose (e:=2) (t:=6) (u:=6)
    · exact typed_composition typed_first (typed_eqSymbol 1)
    · exact typed_composition (typed_pair
        (typed_composition (typed_pair (typed_constant 2)
          (typed_composition typed_second (typed_head 0))) typed_multiply)
        (typed_composition typed_second typed_tail)) typed_listCons_arithmetic
    · apply typed_choose (e:=2) (t:=6) (u:=1)
      · exact typed_composition typed_first (typed_eqSymbol 2)
      · exact typed_composition (typed_pair
          (typed_composition (typed_pair
            (typed_composition (typed_pair (typed_constant 2)
              (typed_composition typed_second (typed_head 0))) typed_multiply)
            (typed_constant 1)) typed_add)
          (typed_composition typed_second typed_tail)) typed_listCons_arithmetic
      · exact typed_second

lemma typed_numFold : Typed (fold numStepRealizer) 7 := by
  apply typed_fold (e:=6) (s:=1) typed_numStep (7*X)
    (show (7*X : Polynomial ℕ).natDegree≤1 by exact degree_scale 7 (by simp))
    (by omega) (by omega)
  intro as ns pre post he
  have h := fold_weight pre ns
  have hlen : pre.length≤as.length := by rw [he,List.length_append]; omega
  have hlen' := list_length_le_weight as
  simp only [eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

/-- The existing reverse/fold parser, including malformed words. -/
lemma typed_parse : Typed parseRealizer 14 := by
  unfold parseRealizer
  apply typed_congr
  exact typed_composition (typed_pair typed_reverse (typed_constant [])) typed_numFold

lemma parse_output_weight (as : List Symbol) : weight (parse as)≤7*weight as+1 := by
  have h := fold_weight as.reverse ([] : List ℕ)
  rw [List.foldl_reverse,List.length_reverse,weight_nil] at h
  change weight (parse as)≤1+6*as.length at h
  have hl := list_length_le_weight as
  omega

lemma typed_marginLists : Typed GreedyFeasibleTable.marginListsRealizer 16 := by
  unfold GreedyFeasibleTable.marginListsRealizer
  apply typed_congr
  exact typed_pair
    (typed_composition (typed_pair (typed_composition typed_tail typed_tail) (typed_head 0)) typed_takeFast)
    (typed_composition (typed_pair
      (typed_composition (typed_pair (typed_composition typed_tail typed_tail) (typed_head 0)) typed_dropFast)
      (typed_composition typed_tail (typed_head 0))) typed_takeFast)

lemma typed_samplingPrecision : Typed samplingPrecisionRealizer 2 := by
  unfold samplingPrecisionRealizer
  exact typed_composition (typed_composition (typed_pair typed_identity
    (typed_composition (typed_pair
      (typed_composition (typed_pair (typed_constant 2) (typed_head 0)) typed_add)
      (typed_composition typed_tail (typed_head 0))) typed_add)) typed_dropFast) (typed_head 0)

lemma typed_samplingInput : Typed samplingInputRealizer 16 := by
  unfold samplingInputRealizer
  exact typed_pair typed_marginLists typed_samplingPrecision

/-- Numerical degree certificate for the exact parser used by the public count
and public supplied-word draw. Independent parser output size prevents a fake
cost-polynomial composition from inflating 14*16 to 224. -/
theorem typed_parsedSampling : Typed parsedSamplingRealizer 16 := by
  unfold parsedSamplingRealizer
  exact typed_composition_from_output_size typed_parse typed_samplingInput (7*X+1)
    (show (7*X+1 : Polynomial ℕ).natDegree≤1 by simpa using degree_affine 7 1)
    (by
      intro as
      simpa only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one] using parse_output_weight as)

end
end Math115.ParserDegreeV1
