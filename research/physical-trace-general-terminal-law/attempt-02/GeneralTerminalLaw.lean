/-
SPDX-License-Identifier: Apache-2.0
Actual support/slack counting connected to ideal stationary acceptance.
This is an ideal one-trial law, not a finite-word or encoded sampler theorem.
-/
import ResearchPhysicalTraceJoin.GeneralAcceptance
import ResearchPhysicalTraceJoin.GeneralInverseLower
import ResearchPhysicalTraceJoin.GeneralCount

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open FirstSuccess ResidualMixture SmallContextCoordinates CompletionCounts
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalStationarySuccess
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

/-- The option-map fibre retains exactly the actual successful inputs. -/
def terminalPartialFibreEquiv (X : Table r c) :
    {a : DefectJoint r c U L // terminalPartialRepair r c U L a = some X} ≃
      TerminalOutputFibre r c U L X where
  toFun a := by
    have hs : TerminalRepairSuccess r c U L a.val := by
      by_contra hn
      have he := a.property
      simp [terminalPartialRepair, hn] at he
    refine ⟨⟨a.val,hs⟩,?_⟩
    have he := a.property
    simpa only [terminalPartialRepair, dite_eq_left hs, Option.some.injEq] using he
  invFun a := ⟨a.val.val, by
    simp only [terminalPartialRepair, dite_eq_left a.val.property, a.property]⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; apply Subtype.ext; rfl

/-- Exact count of the actual tested output map, using ordinary support/slack tests. -/
theorem terminalInverseCount_eq_supportCount (hL : 1 ≤ L) (X : Table r c) :
    terminalInverseCount r c U L X = inverseSupportCount r c U X := by
  unfold terminalInverseCount PartialRepairCorrection.fibreSize
  calc
    _ = Fintype.card (TerminalOutputFibre r c U L X) :=
      Fintype.card_congr (terminalPartialFibreEquiv r c U L X)
    _ = _ := terminalOutput_card_eq_supportCount r c U L hL X

theorem terminalInverseCount_lower (hL : 1 ≤ L) (X : Table r c)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) :
    inverseSupportAllowance r c U ≤ terminalInverseCount r c U L X := by
  rw [terminalInverseCount_eq_supportCount r c U L hL X]
  exact inverseSupportAllowance_le_count r c U X hr hc

/-- No supplied inverse count or acceptance lower bound: both are derived. -/
theorem terminalCorrected_mass [Nonempty (DefectJoint r c U L)]
    (hL : 1 ≤ L) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (X : Table r c) :
    (bindLaw (uniformLaw (α := DefectJoint r c U L))
      (terminalIdealCorrectionRow r c U L (inverseSupportAllowance r c U))).mass (some X) =
        (inverseSupportAllowance r c U : ℚ) / Fintype.card (DefectJoint r c U L) :=
  terminalIdealCorrection_mass_of_le r c U L _ X
    (terminalInverseCount_lower r c U L hL X hr hc)

/-- Unconditional stationary success probability of the actual corrected map. -/
theorem terminalCorrected_success [Nonempty (DefectJoint r c U L)]
    (hL : 1 ≤ L) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) :
    1 - (bindLaw (uniformLaw (α := DefectJoint r c U L))
      (terminalIdealCorrectionRow r c U L (inverseSupportAllowance r c U))).mass none =
      (Fintype.card (Table r c) : ℚ) * inverseSupportAllowance r c U /
        Fintype.card (DefectJoint r c U L) := by
  let law := bindLaw (uniformLaw (α := DefectJoint r c U L))
    (terminalIdealCorrectionRow r c U L (inverseSupportAllowance r c U))
  have ht := success_failure_total law id
  have hs (X : Table r c) : successMass law id X =
      (inverseSupportAllowance r c U : ℚ) / Fintype.card (DefectJoint r c U L) := by
    simpa only [successMass, id_eq, Option.some.injEq, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] using terminalCorrected_mass r c U L hL hr hc X
  have hf : failureMass law id = law.mass none := by simp [failureMass]
  simp only [hs, hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht
  change 1 - law.mass none = _
  rw [← mul_div_assoc] at ht
  linarith

/-- The successful masses have exactly the uniform ordinary-table proportions. -/
theorem terminalCorrected_uniform_proportions [Nonempty (DefectJoint r c U L)]
    (hL : 1 ≤ L) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (X : Table r c) :
    let law := bindLaw (uniformLaw (α := DefectJoint r c U L))
      (terminalIdealCorrectionRow r c U L (inverseSupportAllowance r c U))
    law.mass (some X) = (1 - law.mass none) * uniformMass (α := Table r c) := by
  dsimp only
  rw [terminalCorrected_mass r c U L hL hr hc,
    terminalCorrected_success r c U L hL hr hc]
  have hN : (Fintype.card (Table r c) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨X⟩).ne'
  unfold uniformMass
  field_simp

/-- The actual newer-scale count theorem supplies the denominator bound. -/
theorem actualShape_terminalCorrected_success_lower
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    [Nonempty (DefectJoint r c
      (11 * dimensionAllowance (I := Fin m) (J := Fin n) * (m + n - 2)) 7)] :
    let cutoff := 11 * dimensionAllowance (I := Fin m) (J := Fin n) * (m + n - 2)
    let cellCount := Fintype.card (Cells (firstPaperSmall r c cutoff))
    (inverseSupportAllowance r c cutoff : ℚ) / ((2 * (cellCount * (cellCount - 1)) : ℕ) : ℚ) ≤
      1 - (bindLaw (uniformLaw (α := DefectJoint r c cutoff 7))
        (terminalIdealCorrectionRow r c cutoff 7 (inverseSupportAllowance r c cutoff))).mass none := by
  dsimp only
  let cutoff := 11 * dimensionAllowance (I := Fin m) (J := Fin n) * (m + n - 2)
  let cellCount := Fintype.card (Cells (firstPaperSmall r c cutoff))
  let D := 2 * (cellCount * (cellCount - 1))
  have hZ : 0 < Fintype.card (DefectJoint r c cutoff 7) := Fintype.card_pos
  have hb := actualShape_defectJoint_card_le r c
  change Fintype.card (DefectJoint r c cutoff 7) ≤ D * Fintype.card (Table r c) at hb
  have hD : 0 < D := Nat.pos_of_mul_pos_right (hZ.trans_le hb)
  have hDR : (0 : ℚ) < D := by exact_mod_cast hD
  have hZR : (0 : ℚ) < Fintype.card (DefectJoint r c cutoff 7) := by exact_mod_cast hZ
  rw [terminalCorrected_success r c cutoff 7 (by omega) hr hc]
  apply (div_le_div_iff₀ hDR hZR).mpr
  have hbR : (Fintype.card (DefectJoint r c cutoff 7) : ℚ) ≤
      (D : ℚ) * Fintype.card (Table r c) := by exact_mod_cast hb
  have h := mul_le_mul_of_nonneg_left hbR
    (Nat.cast_nonneg (inverseSupportAllowance r c cutoff) : (0 : ℚ) ≤ _)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- In the nontrivial reduced branch the uniform proportions have positive mass. -/
theorem actualShape_terminalCorrected_success_positive
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    [Nonempty (DefectJoint r c
      (11 * dimensionAllowance (I := Fin m) (J := Fin n) * (m + n - 2)) 7)] :
    let cutoff := 11 * dimensionAllowance (I := Fin m) (J := Fin n) * (m + n - 2)
    0 < 1 - (bindLaw (uniformLaw (α := DefectJoint r c cutoff 7))
      (terminalIdealCorrectionRow r c cutoff 7 (inverseSupportAllowance r c cutoff))).mass none := by
  dsimp only
  let cutoff := 11 * dimensionAllowance (I := Fin m) (J := Fin n) * (m + n - 2)
  let cellCount := Fintype.card (Cells (firstPaperSmall r c cutoff))
  have hZ : 0 < Fintype.card (DefectJoint r c cutoff 7) := Fintype.card_pos
  have hb := actualShape_defectJoint_card_le r c
  change Fintype.card (DefectJoint r c cutoff 7) ≤
    2 * (cellCount * (cellCount - 1)) * Fintype.card (Table r c) at hb
  have hD : 0 < 2 * (cellCount * (cellCount - 1)) :=
    Nat.pos_of_mul_pos_right (hZ.trans_le hb)
  have hp : 0 < cellCount := by
    by_contra h
    have hz : cellCount = 0 := by omega
    simp [hz] at hD
  have hc0 := inverseSupportAllowance_positive r c cutoff hm hn hp
  have hpos : (0 : ℚ) < (inverseSupportAllowance r c cutoff : ℚ) /
      ((2 * (cellCount * (cellCount - 1)) : ℕ) : ℚ) :=
    div_pos (Nat.cast_pos.mpr hc0) (Nat.cast_pos.mpr hD)
  exact hpos.trans_le (actualShape_terminalCorrected_success_lower r c hr hc)

end
end Math115.PhysicalTraceJoin
