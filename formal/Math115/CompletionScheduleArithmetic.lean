import Math115.PhysicalFiniteWalk
import Math115.PhysicalCompletionOracle
import Math115.CompletionRetryBudget
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Explicit natural outer schedules for dyadic accuracy

The arithmetic schedules are ordinary computable natural-number functions.
They bound all four scalar error terms. The physical dense-law wrappers
import this module separately. No outer finite-bit program or machine-cost
conclusion is supplied here.
-/

namespace Math115.CompletionOuterSchedule

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open CompletionRetryBudget PhysicalFiniteWalk PhysicalCompletionOracle
open SmallGraphProfiles SmallContextCoordinates CompletionCounts
open scoped BigOperators

/-- The reciprocal stationary-success allowance for p small cells. -/
def successFactor (p : ℕ) : ℕ := 2 * (1 + p ^ 2)

def gapFactor (d : ℕ) : ℕ := 80000 * d ^ 17

/-- Three spare precision bits allocate a half-target combined error. -/
def restartCount (p h : ℕ) : ℕ := successFactor p * (h + 3)

def mixExponent (p d base h : ℕ) : ℕ :=
  h + 3 + Nat.clog 2 (restartCount p h) + 2 * d * Nat.clog 2 base

def walkCount (p d base h : ℕ) : ℕ := gapFactor d * mixExponent p d base h

def terminalPrecision (p h : ℕ) : ℕ := h + 3 + Nat.clog 2 (restartCount p h)

def stepPrecision (p d base h : ℕ) : ℕ :=
  h + 3 + Nat.clog 2 (restartCount p h) + Nat.clog 2 (walkCount p d base h)

lemma successFactor_positive (p : ℕ) : 0 < successFactor p := by
  unfold successFactor
  positivity

lemma restartCount_positive (p h : ℕ) : 0 < restartCount p h := by
  unfold restartCount
  exact Nat.mul_pos (successFactor_positive p) (by omega)

lemma gapFactor_positive (d : ℕ) (hd : 1 ≤ d) : 0 < gapFactor d := by
  unfold gapFactor
  exact Nat.mul_pos (by decide) (Nat.pow_pos (by omega))

lemma walkCount_positive (p d base h : ℕ) (hd : 1 ≤ d) :
    0 < walkCount p d base h := by
  unfold walkCount
  apply Nat.mul_pos (gapFactor_positive d hd)
  unfold mixExponent
  omega

noncomputable section

lemma dyadic_real (h : ℕ) : (dyadic h : ℝ) = 1 / (2 : ℝ) ^ h := by
  simp only [dyadic, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]

/-- Natural exponents dominate the corresponding binary logarithms:
exp(-n) ≤ 2^(-n). -/
lemma exp_neg_nat_le_dyadic (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (dyadic n : ℝ) := by
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hn : Real.log ((2 : ℝ) ^ n) ≤ (n : ℝ) := by
    rw [Real.log_pow]
    exact mul_le_of_le_one_right (Nat.cast_nonneg n) hlog
  have h := PhysicalFiniteWalk.exp_neg_steps_le_inverse 1 ((2 : ℝ) ^ n)
    (by norm_num) (by positivity) n (by simpa using hn)
  simpa only [div_one, dyadic_real] using h

/-- An extra ceiling-log precision pays for a natural multiplicative charge. -/
lemma dyadic_charge (n extra h : ℕ) (hn : n ≤ 2 ^ extra) :
    (n : ℝ) * (dyadic (h + extra) : ℝ) ≤ (dyadic h : ℝ) := by
  have hnR : (n : ℝ) ≤ (2 : ℝ) ^ extra := by exact_mod_cast hn
  calc
    _ ≤ (2 : ℝ) ^ extra * (dyadic (h + extra) : ℝ) :=
      mul_le_mul_of_nonneg_right hnR (by rw [dyadic_real]; positivity)
    _ = (dyadic h : ℝ) := by
      rw [dyadic_real, dyadic_real, pow_add]
      field_simp

lemma natural_charge_bound (x y : ℕ) :
    x * y ≤ 2 ^ (Nat.clog 2 x + Nat.clog 2 y) := by
  calc
    _ ≤ 2 ^ Nat.clog 2 x * 2 ^ Nat.clog 2 y :=
      Nat.mul_le_mul (Nat.le_pow_clog (by decide) x) (Nat.le_pow_clog (by decide) y)
    _ = _ := (pow_add _ _ _).symm

lemma mass_charge_bound (R base d : ℕ) :
    R * base ^ (2 * d) ≤ 2 ^ (Nat.clog 2 R + 2 * d * Nat.clog 2 base) := by
  have hb := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) base) (2 * d)
  calc
    _ ≤ 2 ^ Nat.clog 2 R * (2 ^ Nat.clog 2 base) ^ (2 * d) :=
      Nat.mul_le_mul (Nat.le_pow_clog (by decide) R) hb
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring

lemma restart_error_bound (p h : ℕ) :
    Real.exp (-(restartCount p h : ℝ) / (successFactor p : ℝ)) ≤ (dyadic (h + 3) : ℝ) := by
  have hs : (successFactor p : ℝ) ≠ 0 := by exact_mod_cast (successFactor_positive p).ne'
  have hratio : -(restartCount p h : ℝ) / (successFactor p : ℝ) = -((h + 3 : ℕ) : ℝ) := by
    simp only [restartCount, Nat.cast_mul]
    field_simp [hs]
  rw [hratio]
  exact exp_neg_nat_le_dyadic (h + 3)

lemma walk_error_bound (p d base h : ℕ) (hd : 1 ≤ d) :
    (restartCount p h : ℝ) * ((base : ℝ) ^ (2 * d) *
      Real.exp (-(walkCount p d base h : ℝ) / (gapFactor d : ℝ))) ≤ (dyadic (h + 3) : ℝ) := by
  have hg : (gapFactor d : ℝ) ≠ 0 := by exact_mod_cast (gapFactor_positive d hd).ne'
  have hratio : -(walkCount p d base h : ℝ) / (gapFactor d : ℝ) =
      -(mixExponent p d base h : ℝ) := by
    simp only [walkCount, Nat.cast_mul]
    field_simp [hg]
  rw [hratio]
  have hexp := exp_neg_nat_le_dyadic (mixExponent p d base h)
  have hm := mul_le_mul_of_nonneg_left hexp
    (show 0 ≤ (restartCount p h : ℝ) * (base : ℝ) ^ (2 * d) by positivity)
  have hc := dyadic_charge (restartCount p h * base ^ (2 * d))
    (Nat.clog 2 (restartCount p h) + 2 * d * Nat.clog 2 base) (h + 3)
    (mass_charge_bound _ _ _)
  have he : h + 3 + (Nat.clog 2 (restartCount p h) + 2 * d * Nat.clog 2 base) =
      mixExponent p d base h := by unfold mixExponent; omega
  rw [he] at hc
  push_cast at hc
  calc
    _ ≤ (restartCount p h : ℝ) * (base : ℝ) ^ (2 * d) *
        (dyadic (mixExponent p d base h) : ℝ) := by
      simpa only [mul_assoc] using hm
    _ ≤ _ := hc

lemma terminal_error_bound (p h : ℕ) :
    (restartCount p h : ℝ) * (dyadic (terminalPrecision p h) : ℝ) ≤ (dyadic (h + 3) : ℝ) :=
  dyadic_charge (restartCount p h) (Nat.clog 2 (restartCount p h)) (h + 3)
    (Nat.le_pow_clog (by decide) _)

lemma step_error_bound (p d base h : ℕ) (γ : ℝ) (hγ : γ ≤ 1) :
    (restartCount p h : ℝ) * ((walkCount p d base h : ℝ) * γ *
      (dyadic (stepPrecision p d base h) : ℝ)) ≤ (dyadic (h + 3) : ℝ) := by
  have hc := dyadic_charge (restartCount p h * walkCount p d base h)
    (Nat.clog 2 (restartCount p h) + Nat.clog 2 (walkCount p d base h)) (h + 3)
    (natural_charge_bound _ _)
  have he : h + 3 + (Nat.clog 2 (restartCount p h) + Nat.clog 2 (walkCount p d base h)) =
      stepPrecision p d base h := by unfold stepPrecision; omega
  rw [he] at hc
  have hg := mul_le_mul_of_nonneg_left hγ
    (show 0 ≤ (restartCount p h : ℝ) * (walkCount p d base h : ℝ) *
      (dyadic (stepPrecision p d base h) : ℝ) by rw [dyadic_real]; positivity)
  push_cast at hc
  nlinarith only [hc, hg]

/-- All four terms of the outer error bound receive an explicit dyadic
budget. The total has a factor-two safety margin at the requested target. -/
theorem arithmetic_schedule_half (p d base h : ℕ) (hd : 1 ≤ d) (γ : ℝ) (hγ : γ ≤ 1) :
    Real.exp (-(restartCount p h : ℝ) / (successFactor p : ℝ)) +
      (restartCount p h : ℝ) * ((base : ℝ) ^ (2 * d) *
        Real.exp (-(walkCount p d base h : ℝ) / (gapFactor d : ℝ))) +
      (restartCount p h : ℝ) * ((walkCount p d base h : ℝ) * γ *
        (dyadic (stepPrecision p d base h) : ℝ) +
          (dyadic (terminalPrecision p h) : ℝ)) ≤ (dyadic (h + 1) : ℝ) := by
  have hr := restart_error_bound p h
  have hw := walk_error_bound p d base h hd
  have hs := step_error_bound p d base h γ hγ
  have ht := terminal_error_bound p h
  have hbQ : 4 * dyadic (h + 3) = dyadic (h + 1) := by
    unfold dyadic
    rw [show h + 3 = (h + 1) + 2 by omega, pow_add]
    norm_num
    ring
  have hbR : (4 : ℝ) * (dyadic (h + 3) : ℝ) = (dyadic (h + 1) : ℝ) := by exact_mod_cast hbQ
  nlinarith only [hr, hw, hs, ht, hbR]

theorem arithmetic_schedule (p d base h : ℕ) (hd : 1 ≤ d) (γ : ℝ) (hγ : γ ≤ 1) :
    Real.exp (-(restartCount p h : ℝ) / (successFactor p : ℝ)) +
      (restartCount p h : ℝ) * ((base : ℝ) ^ (2 * d) *
        Real.exp (-(walkCount p d base h : ℝ) / (gapFactor d : ℝ))) +
      (restartCount p h : ℝ) * ((walkCount p d base h : ℝ) * γ *
        (dyadic (stepPrecision p d base h) : ℝ) +
          (dyadic (terminalPrecision p h) : ℝ)) ≤ (dyadic h : ℝ) := by
  exact (arithmetic_schedule_half p d base h hd γ hγ).trans
    (by exact_mod_cast dyadic_antitone_step h)

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

local notation "d" => CompletionCounts.dimensionAllowance (I := I) (J := J)
local notation "U" => IdealOracleScales.cutoff (I := I) (J := J)
local notation "L" => IdealOracleScales.padding (I := I) (J := J)

/-- Concrete natural inputs to the arithmetic schedule. These counts use
the supplied finite index instances; the schedule functions above are
computable independently of the physical law's noncomputable representation. -/
def physicalSmallCount (r : I → ℕ) (c : J → ℕ) : ℕ :=
  Fintype.card (Cells (CompletionCounts.firstPaperSmall r c U))

def physicalMassBase (r : I → ℕ) : ℕ := (∑ i, r i) + d * L + U + 3

end

end Math115.CompletionOuterSchedule
