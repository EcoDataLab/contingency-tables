/- Preventative checkpoint12 elaboration adjustment v2, source-only. This dependent module has not yet run.
   Conditional assembly of the literal fixed public draw, both branches and fallback. -/
import ResearchBounds.DrawControlDegree
import Math115.PublicLatticeSampler

namespace Math115.DrawDegree
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds

/-- The exact remaining upper-level seams, all certified against their original
    realizers. This record is a hypothesis list, not an assertion that such k has
    been numerically extracted. The reference packed trial contains dense
    completion, decoding, feasibility, terminal draw and output reconstruction. -/
structure ActualDrawSeams (k : ℕ) : Prop where
  positive : 1≤k
  parser : Typed ProfilePrograms.parsedSamplingRealizer k
  printer : Typed GreedyFeasibleTable.printMatrixRealizer k
  schedule : Typed Math115.LatticeScheduleProgram.scheduleRealizer k
  initial : Typed Math115.LatticeSamplerPreparation.initialConfigurationRealizer k
  fallback : Typed Math115.LatticeSamplerPreparation.initialFallbackRealizer k
  branch : Typed Math115.LatticeSamplerPreparation.bothLargeTestRealizer k
  referenceTrial : Typed Math115.LatticeOuterProgram.packedTrialRealizer k
  unitTrial : Typed Math115.LatticeUnitOuter.packedTrialRealizer k
  retryWords : Typed Math115.LatticeOuterProgram.retryWordsRealizer k

lemma typed_trialParameters {k : ℕ} (h : ActualDrawSeams k) :
    Typed Math115.LatticeSampler.trialParametersRealizer k := by
  have harg : Typed (pair
      (first (A:=Math115.LatticeSamplerPreparation.Margins) (B:=Math115.LatticeScheduleProgram.ScheduleOutput))
      (composition second second)) 1 :=
    typed_pair_same typed_first (typed_composition_pos typed_second typed_second (by decide)) (by decide)
  have hinit : Typed (composition (pair
      (first (A:=Math115.LatticeSamplerPreparation.Margins) (B:=Math115.LatticeScheduleProgram.ScheduleOutput))
      (composition second second)) Math115.LatticeSamplerPreparation.initialConfigurationRealizer) k := by
    simpa only [Nat.mul_one] using typed_composition_pos (e:=1) (t:=k) harg h.initial h.positive
  unfold Math115.LatticeSampler.trialParametersRealizer
  apply typed_pair_same (e:=k)
  · apply typed_pair_same (e:=k)
    · exact hinit
    · exact typed_weaken (e:=1) (t:=k) (typed_composition_pos (typed_composition_pos
        (typed_composition_pos typed_second typed_first (by decide)) typed_first (by decide)) typed_first (by decide)) h.positive
    · exact h.positive
  · exact typed_weaken (e:=1) (t:=k) (typed_composition_pos (typed_composition_pos
      (typed_composition_pos typed_second typed_first (by decide)) typed_first (by decide)) typed_second (by decide)) h.positive
  · exact h.positive

lemma typed_assembleParameters {k : ℕ} (h : ActualDrawSeams k) :
    Typed Math115.LatticeSampler.assembleParametersRealizer k := by
  have hfallback : Typed (composition
      (first (A:=Math115.LatticeSamplerPreparation.Margins) (B:=Math115.LatticeScheduleProgram.ScheduleOutput))
      Math115.LatticeSamplerPreparation.initialFallbackRealizer) k := by
    simpa only [Nat.mul_one] using typed_composition_pos (e:=1) (t:=k) typed_first h.fallback h.positive
  unfold Math115.LatticeSampler.assembleParametersRealizer
  exact typed_pair_same (e:=k) (typed_pair_same (e:=k) (typed_trialParameters h) hfallback h.positive)
    (typed_weaken (e:=1) (t:=k) (typed_composition_pos (typed_composition_pos typed_second typed_first (by decide))
      typed_second (by decide)) h.positive) h.positive

lemma typed_prepare {k : ℕ} (h : ActualDrawSeams k) :
    Typed Math115.LatticeSampler.prepareRealizer (k*k) := by
  unfold Math115.LatticeSampler.prepareRealizer
  exact typed_composition_pos (e:=k) (t:=k)
    (typed_pair_same (e:=k) (typed_weaken (e:=1) (t:=k) typed_first h.positive) h.schedule h.positive)
    (typed_assembleParameters h) h.positive

lemma typed_drawRetryInput {k : ℕ} (h : ActualDrawSeams k) :
    Typed Math115.LatticeSampler.drawRetryInputRealizer (k*k) := by
  have hprepared : Typed (composition
      (first (A:=Math115.LatticeScheduleProgram.ScheduleInput) (B:=List Bool))
      Math115.LatticeSampler.prepareRealizer) (k*k) := by
    simpa only [Nat.mul_one] using typed_composition_pos (e:=1) (t:=k*k)
      typed_first (typed_prepare h) (by nlinarith [h.positive])
  unfold Math115.LatticeSampler.drawRetryInputRealizer
  exact typed_pair_same (e:=k*k) hprepared
    (typed_weaken (e:=1) (t:=k*k) typed_second (by nlinarith [h.positive])) (by nlinarith [h.positive])

lemma typed_referenceRetry {k : ℕ} (h : ActualDrawSeams k) :
    Typed Math115.LatticeOuterProgram.retryRealizer (8*(1+k*(k+1))*k) := by
  unfold Math115.LatticeOuterProgram.retryRealizer
  exact typed_composition_pos (e:=k) (t:=8*(1+k*(k+1)))
    (typed_pair_same (e:=k)
      (typed_weaken (e:=1) (t:=k) (typed_composition_pos typed_first typed_first (by decide)) h.positive)
      h.retryWords h.positive)
    (typed_firstSuccessRetry h.referenceTrial h.positive) (by nlinarith)

lemma typed_unitRetry {k : ℕ} (h : ActualDrawSeams k) :
    Typed Math115.LatticeUnitOuter.retryRealizer (8*(1+k*(k+1))*k) := by
  unfold Math115.LatticeUnitOuter.retryRealizer
  exact typed_composition_pos (e:=k) (t:=8*(1+k*(k+1)))
    (typed_pair_same (e:=k)
      (typed_weaken (e:=1) (t:=k) (typed_composition_pos typed_first typed_first (by decide)) h.positive)
      h.retryWords h.positive)
    (typed_firstSuccessRetry h.unitTrial h.positive) (by nlinarith)

lemma typed_draw {k : ℕ} (h : ActualDrawSeams k) :
    Typed Math115.LatticeSampler.drawRealizer (8*(1+k*(k+1))*k^3) := by
  let D := 8*(1+k*(k+1))*k^3
  have hk := h.positive
  have hR : 1≤8*(1+k*(k+1)) := by omega
  have hkk : k≤k^3 := Nat.le_self_pow (by decide) k
  have hretry : 1≤8*(1+k*(k+1))*k := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hR hk
  have hD : 1≤D := by
    dsimp [D]
    simpa only [Nat.one_mul] using Nat.mul_le_mul hR (hk.trans hkk)
  have hkD : k≤D := by
    dsimp [D]
    exact hkk.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (k^3) hR)
  have htest : Typed Math115.LatticeSampler.drawTestRealizer k := by
    unfold Math115.LatticeSampler.drawTestRealizer
    simpa only [Nat.mul_one] using typed_composition_pos (e:=1) (t:=k)
      (typed_composition_pos typed_first typed_first (by decide)) h.branch hk
  have href : Typed Math115.LatticeSampler.drawReferenceRealizer D := by
    unfold Math115.LatticeSampler.drawReferenceRealizer
    exact typed_weaken (e:=(8*(1+k*(k+1))*k)*(k*k)) (t:=D)
      (typed_composition_pos (e:=k*k) (t:=8*(1+k*(k+1))*k)
        (typed_drawRetryInput h) (typed_referenceRetry h) hretry)
      (by dsimp [D]; ring_nf; simp)
  have hunit : Typed Math115.LatticeSampler.drawUnitRealizer D := by
    unfold Math115.LatticeSampler.drawUnitRealizer
    exact typed_weaken (e:=(8*(1+k*(k+1))*k)*(k*k)) (t:=D)
      (typed_composition_pos (e:=k*k) (t:=8*(1+k*(k+1))*k)
        (typed_drawRetryInput h) (typed_unitRetry h) hretry)
      (by dsimp [D]; ring_nf; simp)
  unfold Math115.LatticeSampler.drawRealizer
  exact typed_choose_same (e:=D) (typed_weaken (e:=k) (t:=D) htest hkD) href hunit hD

/-- Conditional degree of the actual supplied-word public realizer. The numeric
    bank is part of its input weight; no d^17/S^170 schedule power is substituted
    for a runtime certificate. All retries, fallback copies and final printing
    are included. -/
theorem typed_publicDraw_of_actual_seams {k : ℕ} (h : ActualDrawSeams k) :
    Typed Math115.PublicLatticeSampler.publicDrawRealizer (8*(1+k*(k+1))*k^5) := by
  have hk := h.positive
  have hparsed : Typed (composition
      (first (A:=List OAI.MatchingFPRAS.Symbol) (B:=List Bool))
      ProfilePrograms.parsedSamplingRealizer) k := by
    simpa only [Nat.mul_one] using typed_composition_pos (e:=1) (t:=k) typed_first h.parser hk
  have hinput : Typed (pair (composition
      (first (A:=List OAI.MatchingFPRAS.Symbol) (B:=List Bool))
      ProfilePrograms.parsedSamplingRealizer) second) k :=
    typed_pair_same (e:=k) hparsed (typed_weaken (e:=1) (t:=k) typed_second hk) hk
  have hR : 1≤8*(1+k*(k+1)) := by omega
  have hkk : k≤k^3 := Nat.le_self_pow (by decide) k
  have hdegree : 1≤8*(1+k*(k+1))*k^3 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hR (hk.trans hkk)
  have hdraw := typed_composition_pos (e:=k) (t:=8*(1+k*(k+1))*k^3)
    hinput (typed_draw h) hdegree
  have hprint := typed_composition_pos (e:=(8*(1+k*(k+1))*k^3)*k) (t:=k) hdraw h.printer hk
  unfold Math115.PublicLatticeSampler.publicDrawRealizer
  exact typed_weaken (e:=k*((8*(1+k*(k+1))*k^3)*k)) (t:=8*(1+k*(k+1))*k^5)
    hprint (by ring_nf; simp)

end Math115.DrawDegree
