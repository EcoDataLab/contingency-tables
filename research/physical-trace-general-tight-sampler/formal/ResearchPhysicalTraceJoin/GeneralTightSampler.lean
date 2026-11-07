/-
SPDX-License-Identifier: Apache-2.0
An optional typed complete reference sampler with the alternative tight
terminal bank. The existing correction coin, initializer, fallback, outer
attempt count and both outer precisions stay fixed. Exact law equality is
proved before restoring original ordered zero margins. The actual raw
implementation is unchanged; no encoded-machine or running-time claim.
-/
import ResearchPhysicalTraceJoin.GeneralTightWidth
import ResearchPhysicalTraceJoin.GeneralCompleteReference
import ResearchPhysicalTraceJoin.GeneralHybridSampler

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture FairBits
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.CompletionRetryBudget
open scoped BigOperators

/-- Ordinary list arithmetic for the unchanged inner schedule's tight bank. -/
def rawTightTerminalScheduleWordWidth (rs cs : List ℕ) (U L h : ℕ) : ℕ :=
  let t := rawScheduleStepPrecision rs cs U L h
  let d := rawScheduleDimension rs cs
  rawTightTerminalBankWidth rs cs U L (t+2) (t+2)
    (rawScheduleExitAttempts d t) (rawScheduleExitPrecision d t)
    (rawScheduleSteps rs cs U L h) (h+2)

def rawTightCorrectedRetryWordWidth (rs cs : List ℕ) (U L h k R : ℕ) : ℕ :=
  R * (rawTightTerminalScheduleWordWidth rs cs U L h + k)

/-- Current outer schedule; only its terminal-bank reservation is tightened. -/
def rawTightPositiveReferenceWordWidth (xs ys : List ℕ) (t : ℕ) : ℕ :=
  let k := rawPositiveOuterPrecision xs ys t
  rawTightCorrectedRetryWordWidth (positiveMargins xs) (positiveMargins ys)
    (positiveTraceCutoff xs ys) 7 k k (rawPositiveOuterAttempts xs ys t)

open scoped Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U,List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U,List.ofFn c)).length)
local notation "dimension" => dimensionAllowance (I := Fin m) (J := Fin n)

/-- The existing schedule parameters, evaluated with the alternative bank. -/
def tightTerminalScheduleWordWidth (h : ℕ) : ℕ :=
  let t := terminalScheduleStepPrecision r c U L h
  tightTerminalBankWidth r c U L (t+2) (t+2)
    (Math115.PhysicalStarBudget.attempts dimension t)
    (Math115.PhysicalStarBudget.precision dimension t)
    (terminalScheduleSteps r c U L h) (terminalScheduleTerminalPrecision h)

def tightTerminalScheduleWord (start : DefectVertices r c U L) (h : ℕ)
    (word : Fin (tightTerminalScheduleWordWidth r c U L h) → Bool) : DefectJoint r c U L :=
  let t := terminalScheduleStepPrecision r c U L h
  tightTerminalJoinedWord r c U L hr hc start (t+2) (t+2)
    (Math115.PhysicalStarBudget.attempts dimension t)
    (Math115.PhysicalStarBudget.precision dimension t)
    (terminalScheduleSteps r c U L h) (terminalScheduleTerminalPrecision h) word

lemma tightTerminalScheduleWordWidth_le_old (h : ℕ) :
    tightTerminalScheduleWordWidth r c U L h ≤ terminalScheduleWordWidth r c U L h :=
  tightTerminalBankWidth_le_old r c U L _ _ _ _ _ _

theorem tightTerminalScheduleWord_same_law (start : DefectVertices r c U L) (h : ℕ) :
    mapLaw (uniformLaw (α := Fin (tightTerminalScheduleWordWidth r c U L h) → Bool))
      (tightTerminalScheduleWord r c U L hr hc start h) =
    mapLaw (uniformLaw (α := Fin (terminalScheduleWordWidth r c U L h) → Bool))
      (terminalScheduleWord r c U L hr hc start h) :=
  tightTerminalJoinedWord_same_law r c U L hr hc start _ _ _ _ _ _

/-- The identical correction map and a separate identical k-bit coin. -/
def tightTerminalCorrectedWordWidth (h k : ℕ) : ℕ := tightTerminalScheduleWordWidth r c U L h + k

def tightTerminalCorrectedWord (start : DefectVertices r c U L) (h k : ℕ)
    (word : Fin (tightTerminalCorrectedWordWidth r c U L h k) → Bool) : Option (Table r c) :=
  let parts := splitWordEquiv (tightTerminalScheduleWordWidth r c U L h) k word
  terminalBitCorrection r c U L k (tightTerminalScheduleWord r c U L hr hc start h parts.1) parts.2

def tightTerminalCorrectedWordLaw (start : DefectVertices r c U L) (h k : ℕ) :
    RationalLaw (Option (Table r c)) :=
  mapLaw (uniformLaw (α := Fin (tightTerminalCorrectedWordWidth r c U L h k) → Bool))
    (tightTerminalCorrectedWord r c U L hr hc start h k)

lemma tightTerminalCorrectedWordWidth_le_old (h k : ℕ) :
    tightTerminalCorrectedWordWidth r c U L h k ≤ terminalCorrectedWordWidth r c U L h k :=
  Nat.add_le_add_right (tightTerminalScheduleWordWidth_le_old r c U L h) k

/-- Equality is on the entire option-valued law, before retry or conditioning. -/
theorem tightTerminalCorrectedWordLaw_eq (start : DefectVertices r c U L) (h k : ℕ) :
    tightTerminalCorrectedWordLaw r c U L hr hc start h k =
      terminalCorrectedWordLaw r c U L hr hc start h k := by
  have he := fresh_split_law (tightTerminalScheduleWord r c U L hr hc start h)
    (terminalBitCorrection r c U L k)
  rw [tightTerminalScheduleWord_same_law r c U L hr hc start h] at he
  exact he.trans (terminalCorrectedWordLaw_eq_bind r c U L hr hc start h k).symm

/-- Exactly R disjoint tight corrected-trial blocks. -/
def tightTerminalCorrectedRetryWordWidth (h k R : ℕ) : ℕ :=
  R * tightTerminalCorrectedWordWidth r c U L h k

def tightTerminalCorrectedRetryWord (start : DefectVertices r c U L) (h k : ℕ)
    (fallback : Table r c) (R : ℕ)
    (word : Fin (tightTerminalCorrectedRetryWordWidth r c U L h k R) → Bool) : Table r c :=
  Math115.CompletionBooleanRetry.flatRetry (tightTerminalCorrectedWord r c U L hr hc start h k)
    fallback R word

def tightTerminalCorrectedRetryWordLaw (start : DefectVertices r c U L) (h k : ℕ)
    (fallback : Table r c) (R : ℕ) : RationalLaw (Table r c) :=
  mapLaw (uniformLaw (α := Fin (tightTerminalCorrectedRetryWordWidth r c U L h k R) → Bool))
    (tightTerminalCorrectedRetryWord r c U L hr hc start h k fallback R)

theorem tightTerminalCorrectedRetryWordWidth_le_old (h k R : ℕ) :
    tightTerminalCorrectedRetryWordWidth r c U L h k R ≤ terminalCorrectedRetryWordWidth r c U L h k R :=
  Nat.mul_le_mul_left R (tightTerminalCorrectedWordWidth_le_old r c U L h k)

/-- First success and the original all-failure fallback are unchanged,
including success equal to fallback and R=0. No fresh accuracy premise. -/
theorem tightTerminalCorrectedRetryWordLaw_eq (start : DefectVertices r c U L) (h k : ℕ)
    (fallback : Table r c) (R : ℕ) :
    tightTerminalCorrectedRetryWordLaw r c U L hr hc start h k fallback R =
      terminalCorrectedRetryLaw r c U L hr hc start h k fallback R := by
  have he := Math115.CompletionBooleanRetry.flatRetry_law
    (tightTerminalCorrectedWord r c U L hr hc start h k) id fallback R
  change tightTerminalCorrectedRetryWordLaw r c U L hr hc start h k fallback R =
    retryLaw (tightTerminalCorrectedWordLaw r c U L hr hc start h k) id fallback R at he
  rw [tightTerminalCorrectedWordLaw_eq r c U L hr hc start h k] at he
  exact he

theorem tightTerminalCorrectedRetryWord_same_law (start : DefectVertices r c U L) (h k : ℕ)
    (fallback : Table r c) (R : ℕ) :
    tightTerminalCorrectedRetryWordLaw r c U L hr hc start h k fallback R =
      terminalCorrectedRetryWordLaw r c U L hr hc start h k fallback R :=
  (tightTerminalCorrectedRetryWordLaw_eq r c U L hr hc start h k fallback R).trans
    (terminalCorrectedRetryWordLaw_eq r c U L hr hc start h k fallback R).symm

/-- Code-level width correspondence, with no semantic schedule at runtime. -/
theorem rawTightTerminalScheduleWordWidth_eq (h : ℕ) :
    rawTightTerminalScheduleWordWidth (List.ofFn r) (List.ofFn c) U L h =
      tightTerminalScheduleWordWidth r c U L h := by
  simp only [rawTightTerminalScheduleWordWidth,rawScheduleStepPrecision_eq,
    rawScheduleDimension_eq,rawScheduleExitAttempts_eq,rawScheduleExitPrecision_eq,
    rawScheduleSteps_eq,tightTerminalScheduleWordWidth,tightTerminalBankWidth,
    rawTightTerminalBankWidth,terminalScheduleTerminalPrecision]

theorem rawTightCorrectedRetryWordWidth_eq (h k R : ℕ) :
    rawTightCorrectedRetryWordWidth (List.ofFn r) (List.ofFn c) U L h k R =
      tightTerminalCorrectedRetryWordWidth r c U L h k R := by
  simp only [rawTightCorrectedRetryWordWidth,rawTightTerminalScheduleWordWidth_eq,
    tightTerminalCorrectedRetryWordWidth,tightTerminalCorrectedWordWidth]

variable (xs ys : List ℕ)

def tightPositiveReferenceWordWidth (t : ℕ) : ℕ :=
  tightTerminalCorrectedRetryWordWidth (filteredMargin xs) (filteredMargin ys)
    (positiveTraceCutoff xs ys) 7 (positiveTraceLinearPrecision xs ys t)
    (positiveTraceLinearPrecision xs ys t) (positiveTraceLinearAttempts xs ys t)

/-- Same internally derived start, fallback, outer attempts/precisions, and
restoration to the original ordered margins. Only the terminal bank differs. -/
def tightPositiveReferenceWord
    (htotal : (∑ i,listMargin xs i) = ∑ j,listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (t : ℕ)
    (word : Fin (tightPositiveReferenceWordWidth xs ys t) → Bool) :
    Table (listMargin xs) (listMargin ys) :=
  (zeroMarginListEquiv xs ys).symm
    (tightTerminalCorrectedRetryWord (filteredMargin xs) (filteredMargin ys)
      (positiveTraceCutoff xs ys) 7
      (positiveTraceReference_conditions xs ys hb).2.2.2.1
      (positiveTraceReference_conditions xs ys hb).2.2.2.2
      (positiveTraceInitialStart xs ys htotal hb)
      (positiveTraceLinearPrecision xs ys t) (positiveTraceLinearPrecision xs ys t)
      (positiveTraceFallback xs ys htotal) (positiveTraceLinearAttempts xs ys t) word)

def tightPositiveReferenceWordLaw
    (htotal : (∑ i,listMargin xs i) = ∑ j,listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (t : ℕ) :
    RationalLaw (Table (listMargin xs) (listMargin ys)) :=
  mapLaw (uniformLaw (α := Fin (tightPositiveReferenceWordWidth xs ys t) → Bool))
    (tightPositiveReferenceWord xs ys htotal hb t)

theorem tightPositiveReferenceWordWidth_le_old (t : ℕ) :
    tightPositiveReferenceWordWidth xs ys t ≤ positiveReferenceWordWidth xs ys t :=
  tightTerminalCorrectedRetryWordWidth_le_old _ _ _ _ _ _ _

/-- Whole initialized original-margin output law, with the existing outer
schedule unchanged. No completion/correction error is newly introduced. -/
theorem tightPositiveReferenceWord_law
    (htotal : (∑ i,listMargin xs i) = ∑ j,listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (t : ℕ) :
    tightPositiveReferenceWordLaw xs ys htotal hb t = positiveReferenceWordLaw xs ys htotal hb t := by
  rw [positiveReferenceWord_law]
  calc
    _ = restoreZeroMarginListsLaw xs ys
        (tightTerminalCorrectedRetryWordLaw (filteredMargin xs) (filteredMargin ys)
          (positiveTraceCutoff xs ys) 7
          (positiveTraceReference_conditions xs ys hb).2.2.2.1
          (positiveTraceReference_conditions xs ys hb).2.2.2.2
          (positiveTraceInitialStart xs ys htotal hb)
          (positiveTraceLinearPrecision xs ys t) (positiveTraceLinearPrecision xs ys t)
          (positiveTraceFallback xs ys htotal) (positiveTraceLinearAttempts xs ys t)) :=
      mapLaw_equiv_output (zeroMarginListEquiv xs ys).symm _ _
    _ = _ := by rw [tightTerminalCorrectedRetryWordLaw_eq]; rfl

/-- Existing complete-reference accuracy transported through exact equality. -/
theorem tightPositiveReferenceWord_accuracy
    (htotal : (∑ i,listMargin xs i) = ∑ j,listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (t : ℕ) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    variation (tightPositiveReferenceWordLaw xs ys htotal hb t)
      (uniformLaw (α := Table (listMargin xs) (listMargin ys))) ≤ dyadic t := by
  letI := table_nonempty (listMargin xs) (listMargin ys) htotal
  rw [tightPositiveReferenceWord_law]
  exact positiveReferenceWord_accuracy xs ys htotal hb t

theorem rawTightPositiveReferenceWordWidth_eq (t : ℕ) :
    rawTightPositiveReferenceWordWidth xs ys t = tightPositiveReferenceWordWidth xs ys t := by
  have hw := rawTightCorrectedRetryWordWidth_eq (filteredMargin xs) (filteredMargin ys)
    (positiveTraceCutoff xs ys) 7 (positiveTraceLinearPrecision xs ys t)
    (positiveTraceLinearPrecision xs ys t) (positiveTraceLinearAttempts xs ys t)
  simp only [ofFn_filteredMargin] at hw
  simp only [rawTightPositiveReferenceWordWidth,rawPositiveOuterPrecision_eq,
    rawPositiveOuterAttempts_eq,hw,tightPositiveReferenceWordWidth]

/-- Total typed dispatcher: the deterministic and legacy backends are
identical, while the reference branch uses its smaller reserved domain. -/
def tightHybridSampler
    (htotal : (∑ i,listMargin xs i) = ∑ j,listMargin ys j) (t : ℕ) :
    (q : ℕ) × ((Fin q → Bool) → Table (listMargin xs) (listMargin ys)) :=
  if _hd : positiveTraceBranch xs ys = .deterministic then
    ⟨0,positiveDeterministicWord xs ys htotal⟩
  else if hb : positiveTraceBranch xs ys = .reference then
    ⟨tightPositiveReferenceWordWidth xs ys t,tightPositiveReferenceWord xs ys htotal hb t⟩
  else
    ⟨positiveLegacyWordWidth xs ys t,positiveLegacyWord xs ys htotal t⟩

def tightHybridWordLaw
    (htotal : (∑ i,listMargin xs i) = ∑ j,listMargin ys j) (t : ℕ) :
    RationalLaw (Table (listMargin xs) (listMargin ys)) :=
  bundledWordLaw (tightHybridSampler xs ys htotal t)

lemma tightHybridSampler_reference
    (htotal : (∑ i,listMargin xs i) = ∑ j,listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (t : ℕ) :
    tightHybridSampler xs ys htotal t =
      ⟨tightPositiveReferenceWordWidth xs ys t,tightPositiveReferenceWord xs ys htotal hb t⟩ := by
  have hd : ¬positiveTraceBranch xs ys = .deterministic := by rw [hb]; decide
  simp only [tightHybridSampler,dite_eq_right hd,dite_eq_left hb]

lemma tightHybridSampler_deterministic
    (htotal : (∑ i,listMargin xs i) = ∑ j,listMargin ys j)
    (hd : positiveTraceBranch xs ys = .deterministic) (t : ℕ) :
    tightHybridSampler xs ys htotal t = ⟨0,positiveDeterministicWord xs ys htotal⟩ := by
  simp only [tightHybridSampler,dite_eq_left hd]

lemma tightHybridSampler_legacy
    (htotal : (∑ i,listMargin xs i) = ∑ j,listMargin ys j)
    (hd : positiveTraceBranch xs ys ≠ .deterministic)
    (hb : positiveTraceBranch xs ys ≠ .reference) (t : ℕ) :
    tightHybridSampler xs ys htotal t =
      ⟨positiveLegacyWordWidth xs ys t,positiveLegacyWord xs ys htotal t⟩ := by
  simp only [tightHybridSampler,dite_eq_right hd,dite_eq_right hb]

theorem tightHybridSampler_width_le_old
    (htotal : (∑ i,listMargin xs i) = ∑ j,listMargin ys j) (t : ℕ) :
    (tightHybridSampler xs ys htotal t).1 ≤ (hybridSampler xs ys htotal t).1 := by
  by_cases hd : positiveTraceBranch xs ys = .deterministic
  · simp only [tightHybridSampler,hybridSampler,dite_eq_left hd,le_refl]
  by_cases hb : positiveTraceBranch xs ys = .reference
  · simp only [tightHybridSampler,hybridSampler,dite_eq_right hd,dite_eq_left hb]
    exact tightPositiveReferenceWordWidth_le_old xs ys t
  · simp only [tightHybridSampler,hybridSampler,dite_eq_right hd,dite_eq_right hb,le_refl]

/-- The Boolean word domains may differ; the complete output distributions
are exactly equal for every equal-total ordered natural-margin input. -/
theorem tightHybridWordLaw_eq
    (htotal : (∑ i,listMargin xs i) = ∑ j,listMargin ys j) (t : ℕ) :
    tightHybridWordLaw xs ys htotal t = hybridWordLaw xs ys htotal t := by
  unfold tightHybridWordLaw hybridWordLaw
  by_cases hd : positiveTraceBranch xs ys = .deterministic
  · rw [tightHybridSampler_deterministic xs ys htotal hd,
      hybridSampler_deterministic xs ys htotal hd]
  by_cases hb : positiveTraceBranch xs ys = .reference
  · rw [tightHybridSampler_reference xs ys htotal hb,hybridSampler_reference xs ys htotal hb]
    change tightPositiveReferenceWordLaw xs ys htotal hb t = positiveReferenceWordLaw xs ys htotal hb t
    exact tightPositiveReferenceWord_law xs ys htotal hb t
  · rw [tightHybridSampler_legacy xs ys htotal hd hb,hybridSampler_legacy xs ys htotal hd hb]

theorem tightHybridWord_accuracy
    (htotal : (∑ i,listMargin xs i) = ∑ j,listMargin ys j) (t : ℕ) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    (variation (tightHybridWordLaw xs ys htotal t)
      (uniformLaw (α := Table (listMargin xs) (listMargin ys))) : ℝ) ≤ (dyadic t : ℝ) := by
  letI := table_nonempty (listMargin xs) (listMargin ys) htotal
  rw [tightHybridWordLaw_eq]
  exact hybridWord_accuracy xs ys htotal t

end
end Math115.PhysicalTraceJoin
