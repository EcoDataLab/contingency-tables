/-
SPDX-License-Identifier: Apache-2.0
The checked scheduled joint draw followed by a fresh bounded correction coin.
Padding failures remain none. This is a typed finite-word one-trial result;
initialization, other branches and encoded running time are separate.
-/
import ResearchPhysicalTraceJoin.GeneralFiniteCorrection
import ResearchPhysicalTraceJoin.Schedule

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open FirstSuccess ResidualMixture FairBits CompletionCounts
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.CompletionRetryBudget
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

/-- Add the scalar endpoint budget before specializing the large word map. -/
private theorem terminalCorrectionBudget (hL : 1 ≤ L) (k : ℕ)
    (p q : RationalLaw (DefectJoint r c U L)) (ε : ℚ) (hε : variation p q ≤ ε) :
    variation (bindLaw p (terminalFiniteCorrectionRow r c U L k))
      (bindLaw q (terminalIdealCorrectionRow r c U L (inverseSupportAllowance r c U))) ≤
        ε + 1 / (2 : ℚ)^k := by
  have hb := terminalFiniteCorrectionRow_bind_variation r c U L hL k p q
  exact hb.trans (add_le_add_right hε _)

/-- Reserve a separate k-bit block after the scheduled joint draw. -/
def terminalCorrectedWordWidth (h k : ℕ) : ℕ :=
  terminalScheduleWordWidth r c U L h + k

def terminalCorrectedWord (start : DefectVertices r c U L) (h k : ℕ)
    (word : Fin (terminalCorrectedWordWidth r c U L h k) → Bool) : Option (Table r c) :=
  let parts := splitWordEquiv (terminalScheduleWordWidth r c U L h) k word
  terminalBitCorrection r c U L k
    (terminalScheduleWord r c U L hr hc start h parts.1) parts.2

def terminalCorrectedWordLaw (start : DefectVertices r c U L) (h k : ℕ) :
    RationalLaw (Option (Table r c)) :=
  mapLaw (uniformLaw (α := Fin (terminalCorrectedWordWidth r c U L h k) → Bool))
    (terminalCorrectedWord r c U L hr hc start h k)

def terminalIdealCorrectedLaw [Nonempty (DefectJoint r c U L)] :
    RationalLaw (Option (Table r c)) :=
  bindLaw (uniformLaw (α := DefectJoint r c U L))
    (terminalIdealCorrectionRow r c U L (inverseSupportAllowance r c U))

/-- The reserved second block supplies a fresh coin, including after
padding failure; a failure path ignores its reserved bits. -/
theorem terminalCorrectedWordLaw_eq_bind (start : DefectVertices r c U L) (h k : ℕ) :
    terminalCorrectedWordLaw r c U L hr hc start h k =
      bindLaw
        (mapLaw (uniformLaw (α := Fin (terminalScheduleWordWidth r c U L h) → Bool))
          (terminalScheduleWord r c U L hr hc start h))
        (terminalFiniteCorrectionRow r c U L k) :=
  fresh_split_law (terminalScheduleWord r c U L hr hc start h)
    (terminalBitCorrection r c U L k)

/-- Actual ordered-list counts discharge the coin premise. The entire
option-valued output is close before any conditioning or retry. -/
theorem terminalCorrectedWord_accuracy [Nonempty (DefectVertices r c U L)]
    (htotal : (∑ i, r i) = ∑ j, c j) (hU : 2 ≤ U) (hL : 7 ≤ L)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (start : DefectVertices r c U L) (h k : ℕ) :
    variation (terminalCorrectedWordLaw r c U L hr hc start h k)
      (terminalIdealCorrectedLaw r c U L) ≤ dyadic h + dyadic k := by
  let p := mapLaw (uniformLaw (α := Fin (terminalScheduleWordWidth r c U L h) → Bool))
    (terminalScheduleWord r c U L hr hc start h)
  let q := uniformLaw (α := DefectJoint r c U L)
  have he : terminalCorrectedWordLaw r c U L hr hc start h k =
      bindLaw p (terminalFiniteCorrectionRow r c U L k) :=
    terminalCorrectedWordLaw_eq_bind r c U L hr hc start h k
  have hv := congrArg (fun z : RationalLaw (Option (Table r c)) =>
    variation z (terminalIdealCorrectedLaw r c U L)) he
  have hw := terminalScheduleWord_accuracy r c U L hr hc htotal hU hL hp start h
  have hwQ : variation p q ≤ dyadic h := (Rat.cast_le (K := ℝ)).mp hw
  have hb := terminalCorrectionBudget r c U L (by omega) k p q (dyadic h) hwQ
  exact hv.le.trans hb

end
end Math115.PhysicalTraceJoin
