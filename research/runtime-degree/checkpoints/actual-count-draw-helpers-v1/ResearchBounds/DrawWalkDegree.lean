/- Preventative checkpoint12 elaboration adjustment v2, source-only. These dependent modules have not yet run.
   Exact cap/metadata/proposal realizers; conditional actual profile and unit folds. -/
import ResearchBounds.DrawControlDegree
import ResearchBounds.WordCountSeedDegrees
import CountBounds.ListRepeatDegree
import Math115.LatticeUnitWalk

namespace Math115.DrawDegree
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds ProfilePrograms

lemma typed_profileCatalog : Typed profileCatalog 1 := by
  unfold profileCatalog
  exact typed_composition_pos (typed_composition_pos typed_first typed_first (by decide)) typed_first (by decide)

lemma typed_profileMargins : Typed profileMargins 1 := by
  unfold profileMargins
  exact typed_composition_pos typed_first typed_second (by decide)

lemma typed_candidateData : Typed candidateDataRealizer 1 := by
  unfold candidateDataRealizer
  exact typed_pair_same (typed_pair_same
    (typed_pair_same (typed_composition_pos typed_first typed_profileCatalog (by decide)) typed_second (by decide))
    (typed_composition_pos typed_first typed_profileMargins (by decide)) (by decide))
    (typed_composition_pos typed_first typed_second (by decide)) (by decide)

lemma typed_currentParameters : Typed currentParametersRealizer 1 := by
  unfold currentParametersRealizer
  exact typed_pair_same (typed_pair_same
    (typed_composition_pos (typed_pair_same
      (typed_composition_pos (typed_composition_pos typed_first typed_first (by decide)) typed_first (by decide))
      typed_second (by decide)) typed_candidateData (by decide))
    (typed_composition_pos (typed_composition_pos typed_first typed_first (by decide)) typed_second (by decide)) (by decide))
    (typed_composition_pos typed_first typed_second (by decide)) (by decide)

lemma typed_minimum : Typed minimum 1 := by
  unfold minimum
  apply typed_congr
  exact typed_choose_same Math115.ListRepeatDegreeV1.typed_less typed_first typed_second (by decide)

lemma typed_capView : Typed capViewRealizer 48 := by
  have hmin : Typed (composition (pair (second (A:=ℕ) (B:=ℕ)) first) minimum) 1 :=
    typed_composition_pos (typed_pair_same typed_second typed_first (by decide)) typed_minimum (by decide)
  have htakeInput : Typed (pair (second (A:=ℕ×ℕ) (B:=List ℕ))
      (composition first first)) 1 :=
    typed_pair_same typed_second (typed_composition_pos typed_first typed_first (by decide)) (by decide)
  have htake : Typed (composition (pair (second (A:=ℕ×ℕ) (B:=List ℕ))
      (composition first first)) takeFast) 8 := by
    simpa only [Nat.mul_one] using typed_composition_pos htakeInput
      Math115.ListRepeatDegreeV1.typed_takeFast (by decide)
  have hprep : Typed (pair (composition (first (A:=ℕ×ℕ) (B:=List ℕ)) second)
      (composition (pair second (composition first first)) takeFast)) 8 :=
    typed_pair_same (typed_weaken (typed_composition_pos typed_first typed_second (by decide)) (by decide))
      htake (by decide)
  unfold capViewRealizer
  exact typed_composition_pos hprep (typed_mapWith hmin (by decide)) (by decide)

lemma typed_capBounds : Typed capBoundsRealizer 2 := by
  unfold capBoundsRealizer
  exact typed_pair_same
    (typed_composition_pos (typed_composition_pos typed_first typed_profileCatalog (by decide))
      Math115.WordCountSeedDegrees.typed_listLength_seed (by decide))
    (typed_weaken (typed_composition_pos typed_first typed_second (by decide)) (by decide)) (by decide)

lemma typed_capViews : Typed capViewsRealizer 96 := by
  have hrowInput : Typed (pair capBoundsRealizer (composition second first)) 2 :=
    typed_pair_same typed_capBounds
      (typed_weaken (typed_composition_pos typed_second typed_first (by decide)) (by decide)) (by decide)
  have hcolumnInput : Typed (pair capBoundsRealizer (composition second second)) 2 :=
    typed_pair_same typed_capBounds
      (typed_weaken (typed_composition_pos typed_second typed_second (by decide)) (by decide)) (by decide)
  have hrow : Typed (composition (pair capBoundsRealizer (composition second first)) capViewRealizer) 96 :=
    typed_composition_pos hrowInput typed_capView (by decide)
  have hcolumn : Typed (composition (pair capBoundsRealizer (composition second second)) capViewRealizer) 96 :=
    typed_composition_pos hcolumnInput typed_capView (by decide)
  unfold capViewsRealizer
  exact typed_pair_same hrow hcolumn (by decide)

lemma typed_profileBoundedNext {e : ℕ}
    (hstep : Typed Math115.LatticeProfileStep.profileStepRealizer e) (he : 1≤e) :
    Typed Math115.LatticeProfileWalk.boundedNextRealizer (96*e) := by
  have hcheck : Typed (composition (composition (composition
      (first (A:=ProfileConfiguration) (B:=ProfileWord)) first) first) first) 1 :=
    typed_composition_pos (typed_composition_pos (typed_composition_pos typed_first typed_first (by decide))
      typed_first (by decide)) typed_first (by decide)
  have hinput : Typed (pair (composition (first (A:=ProfileConfiguration) (B:=ProfileWord))
      currentParametersRealizer) second) 1 :=
    typed_pair_same (typed_composition_pos typed_first typed_currentParameters (by decide)) typed_second (by decide)
  have hnext : Typed (composition (pair (composition (first (A:=ProfileConfiguration) (B:=ProfileWord))
      currentParametersRealizer) second) Math115.LatticeProfileStep.profileStepRealizer) e := by
    simpa only [Nat.mul_one] using typed_composition_pos hinput hstep he
  have hpair : Typed (pair (composition (composition (composition
      (first (A:=ProfileConfiguration) (B:=ProfileWord)) first) first) first)
      (composition (pair (composition first currentParametersRealizer) second)
        Math115.LatticeProfileStep.profileStepRealizer)) e :=
    typed_pair_same (typed_weaken hcheck he) hnext he
  unfold Math115.LatticeProfileWalk.boundedNextRealizer
  exact typed_composition_pos (e:=e) (t:=96) hpair typed_capViews (by decide)

lemma typed_advanceProfile {e : ℕ}
    (hstep : Typed Math115.LatticeProfileStep.profileStepRealizer e) (he : 1≤e) :
    Typed Math115.LatticeProfileWalk.advanceProfileRealizer (96*e) := by
  have hswap : Typed (pair (second (A:=ProfileWord) (B:=ProfileConfiguration)) first) 1 :=
    typed_pair_same typed_second typed_first (by decide)
  have hnext : Typed (composition (pair (second (A:=ProfileWord) (B:=ProfileConfiguration)) first)
      Math115.LatticeProfileWalk.boundedNextRealizer) (96*e) := by
    simpa only [Nat.mul_one] using typed_composition_pos hswap (typed_profileBoundedNext hstep he) (by omega)
  unfold Math115.LatticeProfileWalk.advanceProfileRealizer
  exact typed_pair_same (e:=96*e)
    (typed_weaken (e:=1) (t:=96*e) (typed_composition_pos typed_second typed_first (by decide)) (by omega)) hnext (by omega)

lemma typed_profileWalk_from_advance {e : ℕ}
    (hstep : Typed Math115.LatticeProfileWalk.advanceProfileRealizer e) (he : 1≤e) :
    Typed Math115.LatticeProfileWalk.profileWalkRealizer (1+3*e) := by
  have hfold : Typed (fold Math115.LatticeProfileWalk.advanceProfileRealizer) (1+e*3) := by
    apply typed_fold (e:=e) (s:=3) hstep (20*(X+1)^3)
      (by simpa using degree_scale 20 (natDegree_pow_le_of_le 3
        (show (X+1 : Polynomial ℕ).natDegree≤1 by simpa using degree_affine 1 1))) he (by decide)
    intro words z pre post _
    simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
    exact Math115.LatticeProfileWalk.profileFold_weight pre z (weight (words,z)) (weight_snd (words,z))
  have hswap : Typed (pair (second (A:=ProfileConfiguration) (B:=List (ProfileWord))) first) 1 :=
    typed_pair_same typed_second typed_first (by decide)
  unfold Math115.LatticeProfileWalk.profileWalkRealizer
  exact typed_weaken (e:=(1+e*3)*1) (t:=1+3*e)
    (typed_composition_pos (e:=1) (t:=1+e*3) hswap hfold (by omega)) (by nlinarith)

lemma typed_profileWalk {e : ℕ}
    (hstep : Typed Math115.LatticeProfileStep.profileStepRealizer e) (he : 1≤e) :
    Typed Math115.LatticeProfileWalk.profileWalkRealizer (1+288*e) :=
  typed_weaken (typed_profileWalk_from_advance (typed_advanceProfile hstep he) (by omega)) (by nlinarith)

lemma typed_squareNat : Typed squareNat 6 := by
  unfold squareNat
  exact typed_weaken (typed_composition_pos
    (typed_pair_same typed_identity typed_identity (by decide)) Math115.DegreeBounds.typed_multiply (by decide)) (by decide)

lemma typed_proposalWidth : Typed Math115.LatticeUnitStep.proposalWidthRealizer 72 := by
  unfold Math115.LatticeUnitStep.proposalWidthRealizer
  apply typed_congr
  exact typed_weaken (typed_composition_pos
    (typed_composition_pos (typed_pair_same (e:=6) (typed_weaken (e:=1) (t:=6) (typed_constant 32) (by decide)) typed_squareNat (by decide))
      Math115.DegreeBounds.typed_multiply (by decide))
    Math115.WordCountSeedDegrees.typed_ceilLogTwo_seed (by decide)) (by decide)

lemma typed_wordDimension : Typed Math115.LatticeUnitStep.wordDimension 1 := by
  unfold Math115.LatticeUnitStep.wordDimension
  exact typed_composition_pos (typed_composition_pos typed_first typed_second (by decide)) typed_first (by decide)

lemma typed_proposalPrefix : Typed Math115.LatticeUnitStep.proposalPrefixRealizer 576 := by
  unfold Math115.LatticeUnitStep.proposalPrefixRealizer
  exact typed_weaken (typed_composition_pos
    (typed_pair_same (e:=72) (typed_weaken (e:=1) (t:=72) typed_second (by decide))
      (typed_composition_pos typed_wordDimension typed_proposalWidth (by decide)) (by decide))
    Math115.ListRepeatDegreeV1.typed_takeFast (by decide)) (by decide)

lemma typed_unitWordInput : Typed Math115.LatticeUnitStep.unitWordInputRealizer 576 := by
  unfold Math115.LatticeUnitStep.unitWordInputRealizer
  exact typed_pair_same (e:=576) (typed_weaken (e:=1) (t:=576) typed_first (by decide))
    (typed_pair_same (e:=576) typed_proposalPrefix (typed_weaken (e:=1) (t:=576) (typed_constant ([] : List Bool)) (by decide)) (by decide)) (by decide)

lemma typed_unitWordStep {e : ℕ} (hstep : Typed stepCandidateViewsRealizer e) (he : 1≤e) :
    Typed Math115.LatticeUnitStep.unitWordStepRealizer (576*e) := by
  obtain ⟨p,hp,hpb⟩ := typed_composition_pos typed_unitWordInput hstep he
  refine ⟨p,(by nlinarith [hp]),?_⟩
  intro z
  change (composition Math115.LatticeUnitStep.unitWordInputRealizer stepCandidateViewsRealizer).cost z+
    weight (stepCandidateViews (Math115.LatticeUnitStep.unitWordInput z)) ≤ p.eval (weight z)
  exact hpb z

lemma typed_unitBoundedNext {e : ℕ}
    (hstep : Typed Math115.LatticeUnitStep.unitWordStepRealizer e) (he : 1≤e) :
    Typed Math115.LatticeUnitWalk.boundedNextRealizer (96*e) := by
  have hcheck : Typed (composition (composition (composition
      (first (A:=ProfileConfiguration) (B:=List Bool)) first) first) first) 1 :=
    typed_composition_pos (typed_composition_pos (typed_composition_pos typed_first typed_first (by decide))
      typed_first (by decide)) typed_first (by decide)
  have hinput : Typed (pair (composition (first (A:=ProfileConfiguration) (B:=List Bool))
      currentParametersRealizer) second) 1 :=
    typed_pair_same (typed_composition_pos typed_first typed_currentParameters (by decide)) typed_second (by decide)
  have hnext : Typed (composition (pair (composition (first (A:=ProfileConfiguration) (B:=List Bool))
      currentParametersRealizer) second) Math115.LatticeUnitStep.unitWordStepRealizer) e := by
    simpa only [Nat.mul_one] using typed_composition_pos hinput hstep he
  have hpair : Typed (pair (composition (composition (composition
      (first (A:=ProfileConfiguration) (B:=List Bool)) first) first) first)
      (composition (pair (composition first currentParametersRealizer) second)
        Math115.LatticeUnitStep.unitWordStepRealizer)) e :=
    typed_pair_same (typed_weaken hcheck he) hnext he
  unfold Math115.LatticeUnitWalk.boundedNextRealizer
  exact typed_composition_pos (e:=e) (t:=96) hpair typed_capViews (by decide)

lemma typed_advanceUnit {e : ℕ}
    (hstep : Typed Math115.LatticeUnitStep.unitWordStepRealizer e) (he : 1≤e) :
    Typed Math115.LatticeUnitWalk.advanceUnitRealizer (96*e) := by
  have hswap : Typed (pair (second (A:=List Bool) (B:=ProfileConfiguration)) first) 1 :=
    typed_pair_same typed_second typed_first (by decide)
  have hnext : Typed (composition (pair (second (A:=List Bool) (B:=ProfileConfiguration)) first)
      Math115.LatticeUnitWalk.boundedNextRealizer) (96*e) := by
    simpa only [Nat.mul_one] using typed_composition_pos hswap (typed_unitBoundedNext hstep he) (by omega)
  unfold Math115.LatticeUnitWalk.advanceUnitRealizer
  exact typed_pair_same (e:=96*e)
    (typed_weaken (e:=1) (t:=96*e) (typed_composition_pos typed_second typed_first (by decide)) (by omega)) hnext (by omega)

lemma typed_unitWalk_from_advance {e : ℕ}
    (hstep : Typed Math115.LatticeUnitWalk.advanceUnitRealizer e) (he : 1≤e) :
    Typed Math115.LatticeUnitWalk.unitWalkRealizer (1+3*e) := by
  have hfold : Typed (fold Math115.LatticeUnitWalk.advanceUnitRealizer) (1+e*3) := by
    apply typed_fold (e:=e) (s:=3) hstep (20*(X+1)^3)
      (by simpa using degree_scale 20 (natDegree_pow_le_of_le 3
        (show (X+1 : Polynomial ℕ).natDegree≤1 by simpa using degree_affine 1 1))) he (by decide)
    intro words z pre post _
    simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
    exact Math115.LatticeUnitWalk.unitFold_weight pre z (weight (words,z)) (weight_snd (words,z))
  have hswap : Typed (pair (second (A:=ProfileConfiguration) (B:=List (List Bool))) first) 1 :=
    typed_pair_same typed_second typed_first (by decide)
  unfold Math115.LatticeUnitWalk.unitWalkRealizer
  exact typed_weaken (e:=(1+e*3)*1) (t:=1+3*e)
    (typed_composition_pos (e:=1) (t:=1+e*3) hswap hfold (by omega)) (by nlinarith)

lemma typed_unitWalk {e : ℕ} (hstep : Typed stepCandidateViewsRealizer e) (he : 1≤e) :
    Typed Math115.LatticeUnitWalk.unitWalkRealizer (1+165888*e) := by
  exact typed_weaken (typed_unitWalk_from_advance
    (typed_advanceUnit (typed_unitWordStep hstep he) (by omega)) (by omega)) (by nlinarith)

end Math115.DrawDegree
