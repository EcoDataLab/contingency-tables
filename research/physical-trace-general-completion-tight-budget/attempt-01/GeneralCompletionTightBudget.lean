/-
SPDX-License-Identifier: Apache-2.0
A candidate smaller state-independent completion reservation. It bounds the
same frozen sampler's actual source-dependent word length by its exact scalar
schedule at fixed residual dimension and a mass/count upper bound. No existing
sampler, published reservation constant or completed accuracy proof is changed.
-/
import ResearchPhysicalTraceJoin.GeneralScheduleCode

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles CompletionCounts SmallContextCoordinates
open Math115.CompletionOuterSchedule Math115.CompletionRetryBudget
open Math115.CompletionRandomBudget Math115.LegacyPhysicalCompletion
open Math115.PhysicalCompletionWidth
open scoped BigOperators

private theorem tight_restart_mono (p P h : ℕ) (hp : p ≤ P) :
    restartCount p h ≤ restartCount P h := by
  unfold restartCount successFactor
  gcongr

private theorem tight_walk_mono (d p P base Base h : ℕ) (hp : p ≤ P) (hb : base ≤ Base) :
    walkCount p d base h ≤ walkCount P d Base h := by
  have hr := Nat.clog_mono_right 2 (tight_restart_mono p P h hp)
  have hl := Nat.clog_mono_right 2 hb
  unfold walkCount mixExponent
  exact Nat.mul_le_mul_left _
    (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) hr) (Nat.mul_le_mul_left _ hl))

private theorem tight_stepPrecision_mono (d p P base Base h : ℕ)
    (hp : p ≤ P) (hb : base ≤ Base) :
    stepPrecision p d base h ≤ stepPrecision P d Base h := by
  have hr := Nat.clog_mono_right 2 (tight_restart_mono p P h hp)
  have ht := Nat.clog_mono_right 2 (tight_walk_mono d p P base Base h hp hb)
  unfold stepPrecision
  exact Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) hr) ht

private theorem tight_terminalPrecision_mono (p P h : ℕ) (hp : p ≤ P) :
    terminalPrecision p h ≤ terminalPrecision P h := by
  exact Nat.add_le_add (Nat.le_refl _) (Nat.clog_mono_right 2 (tight_restart_mono p P h hp))

private theorem tight_retries_mono (t T : ℕ) (ht : t ≤ T) : retries t ≤ retries T := by
  unfold retries
  omega

private theorem tight_finePrecision_mono (t T : ℕ) (ht : t ≤ T) :
    finePrecision t ≤ finePrecision T := by
  unfold finePrecision
  exact Nat.add_le_add (Nat.add_le_add ht (Nat.le_refl _))
    (Nat.clog_mono_right 2 (tight_retries_mono t T ht))

private theorem tight_completionReservation_mono (d M N t T : ℕ)
    (hm : M ≤ N) (ht : t ≤ T) :
    completionReservation d M t ≤ completionReservation d N T := by
  have hf : fineBinaryBound d M ≤ fineBinaryBound d N := by
    unfold fineBinaryBound fineMarginBound
    apply Nat.clog_mono_right
    gcongr
  have hp := tight_finePrecision_mono t T ht
  have hinside : d + fineBinaryBound d M + finePrecision t + 1 ≤
      d + fineBinaryBound d N + finePrecision T + 1 := by omega
  unfold completionReservation
  exact Nat.mul_le_mul (tight_retries_mono t T ht)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hinside 62))

/-- Componentwise monotonicity of the exact existing reservation expression,
at fixed dimension/target. No polynomial envelope or sampler modification. -/
theorem completionBudget_totalReservedBits_mono (d p P M N h : ℕ)
    (hp : p ≤ P) (hm : M ≤ N) :
    totalReservedBits d p M h ≤ totalReservedBits d P N h := by
  let base := M + 3*d^2 + 5*d^3 + 3
  let Base := N + 3*d^2 + 5*d^3 + 3
  have hb : base ≤ Base := by dsimp [base, Base]; omega
  have hs := tight_stepPrecision_mono d p P base Base h hp hb
  have ht := tight_terminalPrecision_mono p P h hp
  unfold totalReservedBits
  exact Nat.mul_le_mul (tight_restart_mono p P h hp)
    (Nat.add_le_add
      (Nat.mul_le_mul (tight_walk_mono d p P base Base h hp hb)
        (Nat.add_le_add (Nat.le_refl _)
          (tight_completionReservation_mono d M N _ _ hm hs)))
      (tight_completionReservation_mono d M N _ _ hm ht))

/-- The physical residual shape is fixed before the state is drawn. -/
def rawCompletionRequestDimension (rs cs : List ℕ) (U : ℕ) : ℕ :=
  10 + ((largeIndices (U,rs)).length + 1) * ((largeIndices (U,cs)).length + 1)

def rawTightCompletionCandidate (rs cs : List ℕ) (U L h : ℕ) : ℕ :=
  let D := rawCompletionRequestDimension rs cs U
  totalReservedBits D D (rawScheduleResidualMass rs cs U L) h

/-- Retain the old allowance whenever the new scalar bound would be larger.
This candidate does not alter any existing word reservation or sampler. -/
def rawTightCompletionBits (rs cs : List ℕ) (U L h : ℕ) : ℕ :=
  min (rawUniformCompletionBits rs cs U L h) (rawTightCompletionCandidate rs cs U L h)

theorem rawTightCompletionBits_le_old (rs cs : List ℕ) (U L h : ℕ) :
    rawTightCompletionBits rs cs U L h ≤ rawUniformCompletionBits rs cs U L h :=
  Nat.min_le_left _ _

open scoped Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U,List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U,List.ofFn c)).length)

lemma rawCompletionRequestDimension_eq :
    rawCompletionRequestDimension (List.ofFn r) (List.ofFn c) U =
      dimensionAllowance (I := Fin (tailCount r U + 1)) (J := Fin (tailCount c U + 1)) := by
  have hr1 : 1 ≤ (largeIndices (U,List.ofFn r)).length := by omega
  have hc1 : 1 ≤ (largeIndices (U,List.ofFn c)).length := by omega
  simp only [rawCompletionRequestDimension, dimensionAllowance, Fintype.card_fin,
    tailCount, Nat.sub_add_cancel hr1, Nat.sub_add_cancel hc1]

lemma rawScheduleResidualMass_eq :
    rawScheduleResidualMass (List.ofFn r) (List.ofFn c) U L = residualMassBound r c U L := by
  simp only [rawScheduleResidualMass, rawScheduleLargeLines_row_eq r U,
    rawScheduleLargeLines_column_eq c U, List.sum_ofFn, residualMassBound]

/-- The comparison concerns exactly the frozen completion program's original
source-dependent width, on its actual fixed residual dimensions. -/
theorem completionBits_le_rawTightCandidate
    (z : Math115.ReducedSmallChain.States r c U L) (h : ℕ) :
    bits r c U L hr hc z h ≤ rawTightCompletionCandidate (List.ofFn r) (List.ofFn c) U L h := by
  unfold rawTightCompletionCandidate
  rw [rawCompletionRequestDimension_eq r c U hr hc, rawScheduleResidualMass_eq]
  unfold bits
  rw [LatticeScheduleProgram.totalBits_ofFn_budget]
  unfold physicalTotalReservedBits
  exact completionBudget_totalReservedBits_mono _ _ _ _ _ h
    (physicalSmallCount_le_dimension _ _)
    (coarseRows_total_le_massBound r c U L hr z)

/-- A checked candidate interface for future word-reservation work. No
existing completed word map is changed by proving this allowance. -/
theorem completionBits_le_rawTight
    (z : Math115.ReducedSmallChain.States r c U L) (h : ℕ) :
    bits r c U L hr hc z h ≤ rawTightCompletionBits (List.ofFn r) (List.ofFn c) U L h := by
  apply le_min
  · simpa only [rawUniformCompletionBits_eq] using completionBits_le_uniform r c U L hr hc z h
  · exact completionBits_le_rawTightCandidate r c U L hr hc z h

end
end Math115.PhysicalTraceJoin
