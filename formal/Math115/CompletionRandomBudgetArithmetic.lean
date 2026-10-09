import Math115.CompletionScheduleArithmetic

/-!
# Explicit polynomial allowance for the whole reserved fair-bit bank

This counts reserved random bits, including unused holding and rejected-trial
words. It does not assert machine time, expected bits inspected, or a runtime
exponent. The natural arithmetic definitions are independent of table types.
-/

namespace Math115.CompletionRandomBudget

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open CompletionOuterSchedule CompletionRetryBudget
open SmallGraphProfiles SmallContextCoordinates CompletionCounts
open scoped BigOperators

def binarySize (M : ℕ) : ℕ := Nat.clog 2 (M + 2)
def combinedSize (d M h : ℕ) : ℕ := d + binarySize M + (h + 3)
def fineMarginBound (d M : ℕ) : ℕ := d ^ 12 * (M + 3 * d ^ 2 + 2 * d)
def fineBinaryBound (d M : ℕ) : ℕ := Nat.clog 2 (fineMarginBound d M + 2)
def proposalReservation (d : ℕ) : ℕ := Nat.clog 2 (32 * d ^ 2)
def completionReservation (d M t : ℕ) : ℕ :=
  retries t * (25 * (d + fineBinaryBound d M + finePrecision t + 1) ^ 62)

/-- Full bank for R attempts, T transitions per attempt, a separate proposal
and completion word per transition, and one fresh terminal completion word. -/
def totalReservedBits (d p M h : ℕ) : ℕ :=
  restartCount p h *
    (walkCount p d (M + 3 * d ^ 2 + 5 * d ^ 3 + 3) h *
      (proposalReservation d + completionReservation d M
        (stepPrecision p d (M + 3 * d ^ 2 + 5 * d ^ 3 + 3) h)) +
      completionReservation d M (terminalPrecision p h))

def budgetCoefficient : ℕ := 12672000000 * 37 ^ 62

lemma clog_two_le_self (x : ℕ) : Nat.clog 2 x ≤ x :=
  Nat.clog_le_of_le_pow x.lt_two_pow_self.le

lemma clog_product_bound (x y : ℕ) :
    Nat.clog 2 (x * y) ≤ Nat.clog 2 x + Nat.clog 2 y := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by decide) x) (Nat.le_pow_clog (by decide) y)

lemma clog_power_bound (x k : ℕ) : Nat.clog 2 (x ^ k) ≤ k * Nat.clog 2 x := by
  apply Nat.clog_le_of_le_pow
  have h := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) x) k
  simpa only [← pow_mul, Nat.mul_comm] using h

lemma binarySize_positive (M : ℕ) : 1 ≤ binarySize M := by
  unfold binarySize
  exact Nat.clog_pos (by decide) (by omega)

lemma combinedSize_at_least_fifteen (d M h : ℕ) (hd : 11 ≤ d) :
    15 ≤ combinedSize d M h := by
  have hb := binarySize_positive M
  unfold combinedSize
  omega

lemma restart_polynomial (d p h : ℕ) (hd : 1 ≤ d) (hp : p ≤ d) :
    restartCount p h ≤ 4 * d ^ 2 * (h + 3) := by
  have hpp : p ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hp 2
  have hdd : 1 ≤ d ^ 2 := one_le_pow₀ hd
  unfold restartCount successFactor
  exact Nat.mul_le_mul_right _ (by nlinarith)

lemma restart_log_bound (d p h : ℕ) (hd : 1 ≤ d) (hp : p ≤ d) :
    Nat.clog 2 (restartCount p h) ≤ 2 + 2 * Nat.clog 2 d + Nat.clog 2 (h + 3) := by
  have hm := Nat.clog_mono_right 2 (restart_polynomial d p h hd hp)
  have ha := clog_product_bound (4 * d ^ 2) (h + 3)
  have hb := clog_product_bound 4 (d ^ 2)
  have hc := clog_power_bound d 2
  have h4 : Nat.clog 2 4 = 2 := by decide
  omega

lemma mass_base_log_bound (d M : ℕ) (hd : 1 ≤ d) :
    Nat.clog 2 (M + 3 * d ^ 2 + 5 * d ^ 3 + 3) ≤
      binarySize M + 3 * Nat.clog 2 d + 3 := by
  have h2 : d ^ 2 ≤ d ^ 3 := Nat.pow_le_pow_right hd (by decide : 2 ≤ 3)
  have h3 : 1 ≤ d ^ 3 := one_le_pow₀ hd
  have hm : M ≤ 6 * d ^ 3 * M := by nlinarith [Nat.mul_le_mul_right M h3]
  have hbase : M + 3 * d ^ 2 + 5 * d ^ 3 + 3 ≤ 8 * d ^ 3 * (M + 2) := by
    nlinarith
  have hl := Nat.clog_mono_right 2 hbase
  have ha := clog_product_bound (8 * d ^ 3) (M + 2)
  have hb := clog_product_bound 8 (d ^ 3)
  have hc := clog_power_bound d 3
  have h8 : Nat.clog 2 8 = 3 := by decide
  unfold binarySize
  omega

/-- The d^12 margin inflation contributes twelve of the fourteen log-d
units; two more come from the padded row-total bound. -/
lemma fineBinary_log_bound (d M : ℕ) (hd : 1 ≤ d) :
    fineBinaryBound d M ≤ binarySize M + 14 * Nat.clog 2 d + 2 := by
  have h12 : 1 ≤ d ^ 12 := one_le_pow₀ hd
  have h2 : 1 ≤ d ^ 2 := one_le_pow₀ hd
  have hd2 : d ≤ d ^ 2 := Nat.le_self_pow (by decide) d
  have hm : M ≤ 4 * d ^ 2 * M := by nlinarith [Nat.mul_le_mul_right M h2]
  have hinside : M + 3 * d ^ 2 + 2 * d + 2 ≤ 4 * d ^ 2 * (M + 2) := by
    nlinarith
  have hbound : fineMarginBound d M + 2 ≤ 4 * d ^ 14 * (M + 2) := by
    calc
      _ ≤ d ^ 12 * (M + 3 * d ^ 2 + 2 * d + 2) := by
        unfold fineMarginBound
        nlinarith
      _ ≤ d ^ 12 * (4 * d ^ 2 * (M + 2)) := Nat.mul_le_mul_left _ hinside
      _ = _ := by ring
  have hl := Nat.clog_mono_right 2 hbound
  have ha := clog_product_bound (4 * d ^ 14) (M + 2)
  have hb := clog_product_bound 4 (d ^ 14)
  have hc := clog_power_bound d 14
  have h4 : Nat.clog 2 4 = 2 := by decide
  unfold fineBinaryBound binarySize
  omega

lemma mix_polynomial (d p M h : ℕ) (hd : 11 ≤ d) (hp : p ≤ d) :
    mixExponent p d (M + 3 * d ^ 2 + 5 * d ^ 3 + 3) h ≤ 6 * d * combinedSize d M h := by
  have hd1 : 1 ≤ d := by omega
  have hb := binarySize_positive M
  have hr := restart_log_bound d p h hd1 hp
  have ha := mass_base_log_bound d M hd1
  have hl := clog_two_le_self d
  have hh := clog_two_le_self (h + 3)
  have hleft : Nat.clog 2 (restartCount p h) ≤ 2 + 2 * d + (h + 3) := by omega
  have hright : Nat.clog 2 (M + 3 * d ^ 2 + 5 * d ^ 3 + 3) ≤ binarySize M + 3 * d + 3 := by omega
  have hmid : mixExponent p d (M + 3 * d ^ 2 + 5 * d ^ 3 + 3) h ≤
      2 * (h + 3) + 2 * d * binarySize M + 6 * d ^ 2 + 8 * d + 2 := by
    calc
      _ ≤ (h + 3) + (2 + 2 * d + (h + 3)) + 2 * d * (binarySize M + 3 * d + 3) := by
        unfold mixExponent
        exact Nat.add_le_add (Nat.add_le_add_left hleft _) (Nat.mul_le_mul_left _ hright)
      _ = _ := by ring
  have hdh : 3 * d ≤ d * (h + 3) := by
    simpa only [Nat.mul_comm] using
      (Nat.mul_le_mul_left d (show 3 ≤ h + 3 by omega))
  have hH : h + 3 ≤ d * (h + 3) := by nlinarith [Nat.mul_le_mul_right (h + 3) hd1]
  have hdb : d ≤ d * binarySize M := by nlinarith [Nat.mul_le_mul_left d hb]
  unfold combinedSize
  nlinarith

lemma walk_polynomial (d p M h : ℕ) (hd : 11 ≤ d) (hp : p ≤ d) :
    walkCount p d (M + 3 * d ^ 2 + 5 * d ^ 3 + 3) h ≤
      480000 * d ^ 18 * combinedSize d M h := by
  calc
    _ ≤ gapFactor d * (6 * d * combinedSize d M h) :=
      Nat.mul_le_mul_left _ (mix_polynomial d p M h hd hp)
    _ = _ := by unfold gapFactor; ring

lemma walk_log_bound (d p M h : ℕ) (hd : 11 ≤ d) (hp : p ≤ d) :
    Nat.clog 2 (walkCount p d (M + 3 * d ^ 2 + 5 * d ^ 3 + 3) h) ≤
      20 + 18 * Nat.clog 2 d + Nat.clog 2 (combinedSize d M h) := by
  have hN := Nat.clog_mono_right 2 (mix_polynomial d p M h hd hp)
  have hNa := clog_product_bound (6 * d) (combinedSize d M h)
  have hNb := clog_product_bound 6 d
  have hT := clog_product_bound (gapFactor d)
    (mixExponent p d (M + 3 * d ^ 2 + 5 * d ^ 3 + 3) h)
  have hK := clog_product_bound 80000 (d ^ 17)
  have hd17 := clog_power_bound d 17
  have h6 : Nat.clog 2 6 = 3 := by decide
  have h80000 : Nat.clog 2 80000 = 17 := by decide
  unfold walkCount gapFactor at *
  omega

lemma step_precision_polynomial (d p M h : ℕ) (hd : 11 ≤ d) (hp : p ≤ d) :
    stepPrecision p d (M + 3 * d ^ 2 + 5 * d ^ 3 + 3) h ≤ 21 * combinedSize d M h := by
  have hd1 : 1 ≤ d := by omega
  have hb := binarySize_positive M
  have hr := restart_log_bound d p h hd1 hp
  have ht := walk_log_bound d p M h hd hp
  have hl := clog_two_le_self d
  have hh := clog_two_le_self (h + 3)
  have hn := clog_two_le_self (combinedSize d M h)
  unfold stepPrecision combinedSize at *
  omega

lemma terminal_precision_polynomial (d p M h : ℕ) (hd : 11 ≤ d) (hp : p ≤ d) :
    terminalPrecision p h ≤ 2 * combinedSize d M h := by
  have hr := restart_log_bound d p h (by omega) hp
  have hb := binarySize_positive M
  have hl := clog_two_le_self d
  have hh := clog_two_le_self (h + 3)
  unfold terminalPrecision combinedSize
  omega

lemma finePrecision_upper (t : ℕ) : finePrecision t ≤ t + 4 + Nat.clog 2 (t + 2) := by
  have h := clog_product_bound 4 (t + 2)
  have h4 : Nat.clog 2 4 = 2 := by decide
  unfold finePrecision retries
  omega

lemma finePrecision_polynomial (N t : ℕ) (hN : 15 ≤ N) (ht : t ≤ 21 * N) :
    finePrecision t ≤ 22 * N + 9 := by
  have ht2 : t + 2 ≤ 22 * N := by omega
  have hm := Nat.clog_mono_right 2 ht2
  have hx := clog_product_bound 22 N
  have h22 : Nat.clog 2 22 = 5 := by decide
  have hn := clog_two_le_self N
  have hf := finePrecision_upper t
  omega

lemma completion_product_factor (N : ℕ) :
    (88 * N) * (25 * (37 * N) ^ 62) = 2200 * 37 ^ 62 * N ^ 63 := by ring

lemma completion_reservation_polynomial (d M h t : ℕ) (hd : 11 ≤ d)
    (ht : t ≤ 21 * combinedSize d M h) :
    completionReservation d M t ≤ 2200 * 37 ^ 62 * (combinedSize d M h) ^ 63 := by
  have hN := combinedSize_at_least_fifteen d M h hd
  have hb := binarySize_positive M
  have hl := clog_two_le_self d
  have hf := fineBinary_log_bound d M (by omega)
  have hq := finePrecision_polynomial (combinedSize d M h) t hN ht
  have hi : d + fineBinaryBound d M + finePrecision t + 1 ≤ 37 * combinedSize d M h := by
    unfold combinedSize at *
    omega
  have hJ : retries t ≤ 88 * combinedSize d M h := by
    unfold retries
    omega
  calc
    _ ≤ (88 * combinedSize d M h) * (25 * (37 * combinedSize d M h) ^ 62) :=
      Nat.mul_le_mul hJ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hi 62))
    _ = _ := completion_product_factor _

lemma proposal_log_bound (d : ℕ) : proposalReservation d ≤ 5 + 2 * Nat.clog 2 d := by
  have ha := clog_product_bound 32 (d ^ 2)
  have hb := clog_power_bound d 2
  have h32 : Nat.clog 2 32 = 5 := by decide
  unfold proposalReservation
  omega

lemma reservation_le_three (R T s Cs Ct Rbar Tbar Cbar : ℕ)
    (hR : R ≤ Rbar) (hT : T ≤ Tbar) (hs : s ≤ Cbar) (hCs : Cs ≤ Cbar)
    (hCt : Ct ≤ Cbar) (hTb : 1 ≤ Tbar) :
    R * (T * (s + Cs) + Ct) ≤ 3 * Rbar * Tbar * Cbar := by
  calc
    _ ≤ Rbar * (Tbar * (2 * Cbar) + Cbar) := by
      apply Nat.mul_le_mul hR
      exact Nat.add_le_add (Nat.mul_le_mul hT (by omega)) hCt
    _ ≤ Rbar * (3 * Tbar * Cbar) := by
      apply Nat.mul_le_mul_left
      nlinarith [Nat.mul_le_mul_right Cbar hTb]
    _ = _ := by ring

lemma reservation_product_factor (d H N : ℕ) :
    3 * (4 * d ^ 2 * H) * (480000 * d ^ 18 * N) *
      (2200 * 37 ^ 62 * N ^ 63) = budgetCoefficient * d ^ 20 * H * N ^ 64 := by
  unfold budgetCoefficient
  ring

lemma combined_product_factor (N : ℕ) :
    budgetCoefficient * N ^ 20 * N * N ^ 64 = budgetCoefficient * N ^ 85 := by ring

/-- Explicit separated polynomial allowance for the entire reserved source.
No execution-time or expected-consumption claim is made. -/
theorem totalReservedBits_separated (d p M h : ℕ) (hd : 11 ≤ d) (hp : p ≤ d) :
    totalReservedBits d p M h ≤
      budgetCoefficient * d ^ 20 * (h + 3) * (combinedSize d M h) ^ 64 := by
  let N := combinedSize d M h
  let Cbar := 2200 * 37 ^ 62 * N ^ 63
  have hN : 15 ≤ N := combinedSize_at_least_fifteen d M h hd
  have hR := restart_polynomial d p h (by omega) hp
  have hT := walk_polynomial d p M h hd hp
  have hs : proposalReservation d ≤ Cbar := by
    have hx := proposal_log_bound d
    have hl := clog_two_le_self d
    have hb := binarySize_positive M
    have hsN : proposalReservation d ≤ 3 * N := by
      dsimp [N, combinedSize]
      omega
    have hpN : N ≤ N ^ 63 := Nat.le_self_pow (by decide) N
    have hcoef : 3 ≤ 2200 * 37 ^ 62 := by norm_num
    have hm := Nat.mul_le_mul hcoef hpN
    exact hsN.trans hm
  have hCs : completionReservation d M
      (stepPrecision p d (M + 3 * d ^ 2 + 5 * d ^ 3 + 3) h) ≤ Cbar :=
    completion_reservation_polynomial d M h _ hd (step_precision_polynomial d p M h hd hp)
  have hCt : completionReservation d M (terminalPrecision p h) ≤ Cbar := by
    apply completion_reservation_polynomial d M h _ hd
    exact (terminal_precision_polynomial d p M h hd hp).trans (by omega)
  have hTb : 1 ≤ 480000 * d ^ 18 * N := by
    have hd18 : 1 ≤ d ^ 18 := one_le_pow₀ (by omega : 1 ≤ d)
    nlinarith
  have hbound := reservation_le_three _ _ _ _ _ _ _ _ hR hT hs hCs hCt hTb
  change totalReservedBits d p M h ≤ 3 * (4 * d ^ 2 * (h + 3)) *
    (480000 * d ^ 18 * N) * Cbar at hbound
  calc
    _ ≤ _ := hbound
    _ = _ := reservation_product_factor d (h + 3) N

/-- A compact degree-85 bound in d+h+ceil(log₂(M+2))+3, for reserved fair
bits. The degree is not a machine-time exponent. -/
theorem totalReservedBits_combined (d p M h : ℕ) (hd : 11 ≤ d) (hp : p ≤ d) :
    totalReservedBits d p M h ≤ budgetCoefficient * (combinedSize d M h) ^ 85 := by
  have hbound := totalReservedBits_separated d p M h hd hp
  have hdN : d ≤ combinedSize d M h := by unfold combinedSize; omega
  have hHN : h + 3 ≤ combinedSize d M h := by unfold combinedSize; omega
  calc
    _ ≤ budgetCoefficient * d ^ 20 * (h + 3) * (combinedSize d M h) ^ 64 := hbound
    _ ≤ budgetCoefficient * (combinedSize d M h) ^ 20 *
        (combinedSize d M h) * (combinedSize d M h) ^ 64 := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdN 20)) hHN)
    _ = _ := combined_product_factor _


end Math115.CompletionRandomBudget
