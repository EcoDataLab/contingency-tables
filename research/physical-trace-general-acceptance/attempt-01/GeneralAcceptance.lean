/-
SPDX-License-Identifier: Apache-2.0
Ideal reciprocal-fibre correction after the actual repair padding test.
The clipped formula is total, including outputs with empty inverse fibres.
Geometric count formulae and a positive lower bound are separate obligations.
-/
import ResearchPhysicalTraceJoin.GeneralRepair
import RepairAcceptanceCoin

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open FirstSuccess ResidualMixture Math115.RepairAcceptanceCoin
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalStationarySuccess
open scoped BigOperators Classical
noncomputable section

namespace PartialRepairCorrection
variable {S A : Type*} [Fintype S] [Fintype A]

def fibreSize (f : S → Option A) (a : A) : ℕ :=
  Fintype.card {x : S // f x = some a}

lemma clippedRatio_le_one (c ell : ℕ) : ((min c ell : ℕ) : ℚ) / ell ≤ 1 := by
  by_cases h : ell = 0
  · simp [h]
  · apply (div_le_iff₀ (show (0 : ℚ) < ell by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    simpa only [one_mul] using
      (show ((min c ell : ℕ) : ℚ) ≤ ell by exact_mod_cast min_le_right c ell)

def clippedCoin (a : A) (c ell : ℕ) : RationalLaw (Option A) :=
  coinLaw a (((min c ell : ℕ) : ℚ) / ell) (by positivity) (clippedRatio_le_one c ell)

def row (f : S → Option A) (c : ℕ) (x : S) : RationalLaw (Option A) :=
  match f x with
  | none => pointLaw none
  | some a => clippedCoin a c (fibreSize f a)

lemma row_some (f : S → Option A) (c : ℕ) (x : S) (a : A) :
    (row f c x).mass (some a) =
      if f x = some a then ((min c (fibreSize f a) : ℕ) : ℚ) / fibreSize f a else 0 := by
  cases hx : f x with
  | none => simp [row, hx, pointLaw]
  | some b =>
    by_cases hab : a = b
    · subst a
      simp [row, hx, clippedCoin]
    · simp [row, hx, clippedCoin, hab, Ne.symm hab]

lemma uniform_preimage_mass [Nonempty S] (f : S → Option A) (a : A) :
    (∑ x : S, if f x = some a then uniformMass (α := S) else 0) =
      (fibreSize f a : ℚ) / Fintype.card S := by
  rw [← Finset.sum_filter, Finset.sum_const, ← Fintype.card_subtype]
  simp [fibreSize, uniformMass, nsmul_eq_mul, div_eq_mul_inv]

/-- Includes unreachable outputs; no fibre lower bound is assumed. -/
theorem stationary_some [Nonempty S] (f : S → Option A) (c : ℕ) (a : A) :
    (bindLaw (uniformLaw (α := S)) (row f c)).mass (some a) =
      ((min c (fibreSize f a) : ℕ) : ℚ) / Fintype.card S := by
  change (∑ x : S, uniformMass (α := S) * (row f c x).mass (some a)) = _
  simp_rw [row_some]
  by_cases hz : fibreSize f a = 0
  · simp [hz]
  have hf : (fibreSize f a : ℚ) ≠ 0 := by exact_mod_cast hz
  have he : (∑ x : S, uniformMass (α := S) *
      (if f x = some a then ((min c (fibreSize f a) : ℕ) : ℚ) / fibreSize f a else 0)) =
      (∑ x : S, if f x = some a then uniformMass (α := S) else 0) *
        (((min c (fibreSize f a) : ℕ) : ℚ) / fibreSize f a) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [he, uniform_preimage_mass]
  field_simp

theorem stationary_some_of_le [Nonempty S] (f : S → Option A) (c : ℕ) (a : A)
    (hc : c ≤ fibreSize f a) :
    (bindLaw (uniformLaw (α := S)) (row f c)).mass (some a) =
      (c : ℚ) / Fintype.card S := by
  rw [stationary_some, Nat.min_eq_left hc]
end PartialRepairCorrection

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

/-- Test actual repaired entries before producing an ordinary output. -/
def terminalPartialRepair (a : DefectJoint r c U L) : Option (Table r c) :=
  if h : TerminalRepairSuccess r c U L a then
    some (terminalRepairOutput r c U L ⟨a,h⟩) else none

def terminalInverseCount (X : Table r c) : ℕ :=
  PartialRepairCorrection.fibreSize (terminalPartialRepair r c U L) X

def terminalIdealCorrectionRow (c0 : ℕ) (a : DefectJoint r c U L) :
    RationalLaw (Option (Table r c)) :=
  PartialRepairCorrection.row (terminalPartialRepair r c U L) c0 a

/-- Uses the true inverse count. Clipping vanishes after the geometric lower bound. -/
theorem terminalIdealCorrection_mass [Nonempty (DefectJoint r c U L)]
    (c0 : ℕ) (X : Table r c) :
    (bindLaw (uniformLaw (α := DefectJoint r c U L))
      (terminalIdealCorrectionRow r c U L c0)).mass (some X) =
        ((min c0 (terminalInverseCount r c U L X) : ℕ) : ℚ) /
          Fintype.card (DefectJoint r c U L) :=
  PartialRepairCorrection.stationary_some _ c0 X

/-- The desired constant mass, conditional on the separate count lower bound. -/
theorem terminalIdealCorrection_mass_of_le [Nonempty (DefectJoint r c U L)]
    (c0 : ℕ) (X : Table r c) (hc : c0 ≤ terminalInverseCount r c U L X) :
    (bindLaw (uniformLaw (α := DefectJoint r c U L))
      (terminalIdealCorrectionRow r c U L c0)).mass (some X) =
        (c0 : ℚ) / Fintype.card (DefectJoint r c U L) := by
  rw [terminalIdealCorrection_mass, Nat.min_eq_left hc]
end
end Math115.PhysicalTraceJoin
