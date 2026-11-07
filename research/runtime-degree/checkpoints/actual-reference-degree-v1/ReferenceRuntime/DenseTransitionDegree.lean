import ReferenceRuntime.DenseAcceptanceDegree
import ReferenceRuntime.DenseExponentDegree
import RetryRuntime.ActualRetryWordsDegree
import AffineMapWith.ChunkExample

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms ProfilePrograms
set_option maxHeartbeats 1600000
noncomputable section

lemma typed_replaceFlat : Typed replaceFlatRealizer 1 := by
  unfold replaceFlatRealizer
  exact typed_pair
    (typed_pair (typed_composition (typed_composition typed_first typed_first) typed_first) typed_second)
    (typed_composition typed_first typed_second)

lemma typed_flatAcceptCandidate : Typed flatAcceptCandidateRealizer 13175441535124223947225652064416206147584 := by
  unfold flatAcceptCandidateRealizer
  exact typed_choose
    (typed_composition
      (typed_pair
        (typed_composition (typed_composition typed_first typed_second) typed_second)
        (typed_composition
          (typed_pair
            (typed_composition
              (typed_composition
                (typed_pair (typed_composition typed_first typed_first) typed_second) typed_replaceFlat) typed_flatExponent)
            (typed_composition (typed_composition typed_first typed_first) typed_flatExponent))
          Math115.DivisionRuntimeNext.typed_subtract_actual)) typed_dyadicWordAccept)
    typed_second
    (typed_composition (typed_composition (typed_composition typed_first typed_first) typed_first) typed_second)

lemma typed_flatStepCandidate : Typed flatStepCandidateRealizer 2612736 := by
  unfold flatStepCandidateRealizer
  exact typed_composition
    (typed_pair
      (typed_pair
        (typed_composition
          (typed_pair (typed_constant 4)
            (typed_composition (typed_composition typed_first typed_second) typed_denseEighthPower)) typed_multiply)
        (typed_composition (typed_composition typed_first typed_first) typed_second))
      (typed_composition typed_second typed_first)) typed_axisWordStep

theorem typed_flatMetropolisStep : Typed flatMetropolisStepRealizer 34423950414714324378978561272174540785214029824 := by
  unfold flatMetropolisStepRealizer
  exact typed_composition
    (typed_pair typed_identity typed_flatStepCandidate)
    (Math115.DrawDegree.typed_optionCases
      (Math115.DrawDegree.typed_weaken
        (typed_composition (typed_composition typed_first typed_first) typed_second) (by decide))
      typed_flatAcceptCandidate (by decide))

lemma typed_denseProposalWidth : Typed proposalWidthRealizer 12 := by
  unfold proposalWidthRealizer
  exact typed_composition
    (typed_composition
      (typed_pair (typed_constant 8) (typed_composition typed_first typed_second)) typed_multiply)
    Math115.WordCountSeedDegrees.typed_ceilLogTwo_seed

lemma typed_flatWordStep : Typed flatWordStepRealizer 3304699239812575140381941882128755915380546863104 := by
  unfold flatWordStepRealizer
  exact typed_composition
    (typed_pair typed_first
      (typed_pair
        (typed_composition (typed_pair typed_second typed_denseProposalWidth) Math115.ListRepeatDegreeV1.typed_takeFast)
        (typed_composition (typed_pair typed_second typed_denseProposalWidth) Math115.ListRepeatDegreeV1.typed_dropFast)))
    typed_flatMetropolisStep

theorem typed_denseAdvance : Typed advanceRealizer 3304699239812575140381941882128755915380546863104 := by
  unfold advanceRealizer
  exact typed_composition
    (typed_pair typed_second (typed_composition (typed_pair typed_second typed_first) typed_flatWordStep)) typed_replaceFlat

/-- Retain the original quadratic intermediate-state envelope and actual
supplied-word list length, including malformed states and empty word banks. -/
theorem typed_denseWalkWords : Typed walkWordsRealizer 6609398479625150280763883764257511830761093726209 := by
  unfold walkWordsRealizer
  apply typed_composition (e:=1) (t:=6609398479625150280763883764257511830761093726209)
    (typed_pair typed_second typed_first)
  apply typed_fold (e:=3304699239812575140381941882128755915380546863104) (s:=2)
    typed_denseAdvance (20*(X+1)^2)
    (by simpa using degree_scale 20 (natDegree_pow_le_of_le 2 (show (X+1 : Polynomial ℕ).natDegree ≤ 1 by simpa using degree_affine 1 1)))
    (by decide) (by decide)
  intro bits data pre post he
  let S := weight (bits,data)
  let out := pre.foldl (fun data bits => advance (bits,data)) data
  have hd : weight data ≤ S := weight_snd (bits,data)
  have hp : pre.length ≤ S := (list_length_le_weight pre).trans
    ((weight_prefix he).trans (weight_fst (bits,data)))
  have hxs : weight data.1.2 ≤ S := (weight_snd data.1).trans ((weight_fst data).trans hd)
  have hn : data.1.2.length ≤ S := (list_length_le_weight _).trans hxs
  have hi : ∀ a ∈ data.1.2, a.size ≤ S := fun a ha => (size_le_weight a).trans ((weight_mem ha).trans hxs)
  have hs := fold_advance_sizes pre data S hi
  have ht := fold_advance_parameters pre data
  have hw : weight out.1.2 ≤ out.1.2.length*(4*(S+2*pre.length)+2)+1 := by
    have h := weight_map_bound (f:=id) (as:=out.1.2) (N:=4*(S+2*pre.length)+1)
      (fun a ha => (weight_nat_le a).trans (by have h := hs a ha; omega))
    simpa only [List.map_id_fun,id_eq,Nat.add_assoc] using h
  have hm : weight out.1.1 ≤ S := by
    rw [ht.1]
    exact (weight_fst data.1).trans ((weight_fst data).trans hd)
  have hd' : weight out.2 ≤ S := by
    rw [ht.2.1]
    exact (weight_snd data).trans hd
  have hl : out.1.2.length ≤ S := ht.2.2.trans_le hn
  have hmul : out.1.2.length*(4*(S+2*pre.length)+2) ≤ S*(12*S+2) := Nat.mul_le_mul hl (by omega)
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change weight out ≤ 20*(S+1)^2
  have heq : weight out = 1+(1+weight out.1.1+weight out.1.2)+weight out.2 := by rw [weight_prod,weight_prod]
  nlinarith

lemma typed_denseWordChunks : Typed wordChunksRealizer 1544 := by
  unfold wordChunksRealizer
  exact typed_composition (typed_pair typed_identity Math115.RetryRuntimeNext.typed_actual_completeWordRows)
    Math115.AffineMapWithNext.typed_mapWith_chunkProgram

theorem typed_denseFlatWordWalk : Typed flatWordWalkRealizer 13225564983293436715415269745489623353636886812393638016 := by
  unfold flatWordWalkRealizer
  exact typed_composition
    (typed_pair typed_first
      (typed_composition
        (typed_pair (typed_composition (typed_composition typed_first typed_second) typed_denseWidth) typed_second)
        typed_denseWordChunks)) typed_denseWalkWords

#check typed_denseFlatWordWalk
#print axioms typed_denseFlatWordWalk
#check typed_flatMetropolisStep
#print axioms typed_flatMetropolisStep
#check typed_denseAdvance
#print axioms typed_denseAdvance
#check typed_denseWalkWords
#print axioms typed_denseWalkWords
#check typed_denseWordChunks
#print axioms typed_denseWordChunks
end
end Math115.ReferenceRuntimeNext
