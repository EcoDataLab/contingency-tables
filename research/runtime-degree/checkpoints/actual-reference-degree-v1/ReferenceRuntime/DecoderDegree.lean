import DivisionRuntime.Degree
import DrawRuntime.RangeSeed
import Math115.LatticeCompletionProgram

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds Math115.DrawDegree
open Math115.LatticeCompletionProgram DensePrograms

set_option maxHeartbeats 1200000

noncomputable section

lemma typed_successor : Typed successor 1 := by
  unfold successor
  apply typed_congr
  exact typed_composition (typed_pair typed_identity (typed_constant 1)) typed_add

lemma typed_some {A : Type} [Codec A] [Inhabited A] :
    Typed (OAI.MatchingFPRAS.TreeTyped.some (A:=A)) 1 := by
  unfold OAI.MatchingFPRAS.TreeTyped.some
  apply typed_recode
  exact typed_pair_same (typed_constant true) typed_identity (by decide)

lemma typed_any : Typed any 2 := by
  unfold any
  apply typed_congr
  apply typed_composition_pos (e:=1) (t:=2)
    (typed_pair_same typed_identity (typed_constant false) (by decide))
  apply typed_fold (e:=1) (s:=1)
    (typed_choose_same typed_first (typed_constant true) typed_second (by decide)) (X+4)
    (by simpa using degree_affine 1 4) (by decide) (by decide)
  · intro as z pre post he
    have hw := weight_bool (pre.foldl (fun z b => if b then true else z) z)
    simp only [eval_add,eval_X,eval_ofNat]
    omega
  · decide

lemma typed_all : Typed all 12 := by
  unfold all
  apply typed_congr
  exact typed_composition_pos
    (typed_composition_pos
      (typed_map Math115.ListRepeatDegreeV1.typed_boolNot (by decide)) typed_any (by decide))
    Math115.ListRepeatDegreeV1.typed_boolNot (by decide)

lemma typed_rowPrefix : Typed rowPrefixRealizer 24 := by
  unfold rowPrefixRealizer
  exact typed_composition_pos
    (typed_composition_pos (typed_pair_same typed_second typed_first (by decide))
      Math115.ListRepeatDegreeV1.typed_takeFast (by decide))
    Math115.WordCountSeedDegrees.typed_listSum_seed (by decide)

lemma typed_prefix : Typed prefixRealizer 28848 := by
  unfold prefixRealizer Realizer.fst Realizer.snd
  exact typed_composition_pos
    (typed_composition_pos
      (typed_pair_same
        (typed_weaken (typed_composition_pos typed_second typed_second (by decide)) (by decide))
        (typed_composition_pos
          (typed_pair_same typed_first (typed_composition_pos typed_second typed_first (by decide)) (by decide))
          Math115.ListRepeatDegreeV1.typed_takeFast (by decide)) (by decide))
      (typed_mapWith typed_rowPrefix (by decide)) (by decide))
    Math115.WordCountSeedDegrees.typed_listSum_seed (by decide)

lemma typed_floorPrefix : Typed floorPrefixRealizer 115392 := by
  unfold floorPrefixRealizer Realizer.fst Realizer.snd
  exact typed_composition_pos
    (typed_pair_same
      (typed_composition_pos
        (typed_pair_same (typed_composition_pos typed_first typed_second (by decide)) typed_second (by decide))
        typed_prefix (by decide))
      (typed_weaken (typed_composition_pos typed_first typed_first (by decide)) (by decide)) (by decide))
    Math115.DivisionRuntimeNext.typed_quotient (by decide)

lemma typed_cellTotals : Typed cellTotalsRealizer 115392 := by
  unfold cellTotalsRealizer Realizer.fst Realizer.snd
  apply typed_congr
  apply typed_pair_same (e:=115392)
  · apply typed_composition_pos (e:=115392) (t:=1)
    · apply typed_pair_same (e:=115392)
      · apply typed_composition_pos (e:=1) (t:=115392) _ typed_floorPrefix (by decide)
        exact typed_pair_same typed_first (typed_pair_same
          (typed_composition_pos (typed_composition_pos typed_second typed_first (by decide)) typed_successor (by decide))
          (typed_composition_pos (typed_composition_pos typed_second typed_second (by decide)) typed_successor (by decide)) (by decide)) (by decide)
      · exact typed_floorPrefix
      · decide
    · exact typed_add
    · decide
  · apply typed_composition_pos (e:=115392) (t:=1)
    · apply typed_pair_same (e:=115392)
      · apply typed_composition_pos (e:=115392) (t:=1)
        · apply typed_pair_same (e:=115392)
          · apply typed_composition_pos (e:=1) (t:=115392) _ typed_floorPrefix (by decide)
            exact typed_pair_same typed_first (typed_pair_same
              (typed_composition_pos typed_second typed_first (by decide))
              (typed_composition_pos (typed_composition_pos typed_second typed_second (by decide)) typed_successor (by decide)) (by decide)) (by decide)
          · apply typed_composition_pos (e:=1) (t:=115392) _ typed_floorPrefix (by decide)
            exact typed_pair_same typed_first (typed_pair_same
              (typed_composition_pos (typed_composition_pos typed_second typed_first (by decide)) typed_successor (by decide))
              (typed_composition_pos typed_second typed_second (by decide)) (by decide)) (by decide)
          · decide
        · exact typed_add
        · decide
      · exact typed_weaken (typed_constant 2) (by decide)
      · decide
    · exact typed_add
    · decide
  · decide

lemma typed_cell : Typed cellRealizer 115392 := by
  unfold cellRealizer
  exact typed_composition_pos typed_cellTotals
    (typed_pair_same
      (typed_composition_pos (typed_pair_same typed_second typed_first (by decide))
        Math115.ListRepeatDegreeV1.typed_leNat (by decide))
      Math115.DivisionRuntimeNext.typed_subtract_actual (by decide)) (by decide)

lemma typed_indices {A : Type} [Codec A] : Typed (indicesRealizer (A:=A)) 3 := by
  unfold indicesRealizer
  apply Math115.DrawRuntimeNext.typed_boundedRange (e:=2) (d:=1)
    Math115.WordCountSeedDegrees.typed_listLength_seed X (by simp)
  intro as
  simpa only [eval_X] using list_length_le_weight as

lemma typed_rowCells : Typed rowCellsRealizer 159785148684 := by
  have hin : Typed (pair (identity (A:=(ℕ×MatrixCode)×ℕ))
      (composition (composition (pair first.snd second) (getDFast [])) indicesRealizer)) 6 := by
    apply typed_pair_same (e:=6) (typed_weaken typed_identity (by decide))
    · exact typed_composition_pos
        (typed_composition_pos
          (typed_pair_same (typed_composition_pos typed_first typed_second (by decide)) typed_second (by decide))
          (Math115.DrawRuntimeNext.typed_getDFast []) (by decide)) typed_indices (by decide)
    · decide
  have hcell : Typed (composition (pair first.fst (pair first.snd second)) cellRealizer) 115392 := by
    exact typed_composition_pos
      (typed_pair_same (typed_composition_pos typed_first typed_first (by decide))
        (typed_pair_same (typed_composition_pos typed_first typed_second (by decide)) typed_second (by decide)) (by decide))
      typed_cell (by decide)
  unfold rowCellsRealizer
  exact typed_composition_pos hin (typed_mapWith hcell (by decide)) (by decide)

lemma typed_cells : Typed cellsRealizer 153187762440766632483246 := by
  unfold cellsRealizer
  exact typed_composition_pos
    (typed_pair_same (typed_weaken typed_identity (by decide))
      (typed_composition_pos typed_second typed_indices (by decide)) (by decide))
    (typed_mapWith typed_rowCells (by decide)) (by decide)

lemma typed_accepted : Typed acceptedRealizer 126168 := by
  unfold acceptedRealizer
  exact typed_composition_pos
    (typed_map (typed_composition_pos (typed_map typed_first (by decide)) typed_all (by decide)) (by decide))
    typed_all (by decide)

lemma typed_values : Typed valuesRealizer 86 := by
  unfold valuesRealizer
  exact typed_map (typed_map typed_second (by decide)) (by decide)

lemma typed_finish : Typed finishRealizer 126168 := by
  unfold finishRealizer
  apply typed_choose_same typed_accepted
  · exact typed_weaken (typed_composition_pos typed_values typed_some (by decide)) (by decide)
  · exact typed_weaken (typed_constant none) (by decide)
  · decide

/-- Uniform work-plus-codec bound for the original prefix-floor decoder,
including divisor zero, empty dimensions, ragged rows, and rejection. -/
theorem typed_decode : Typed decodeRealizer 19327393611626644487146181328 := by
  unfold decodeRealizer
  exact typed_composition_pos typed_cells typed_finish (by decide)

#check typed_decode
#print axioms typed_decode
end
end Math115.ReferenceRuntimeNext
