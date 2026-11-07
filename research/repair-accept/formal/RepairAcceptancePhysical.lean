import RepairAcceptanceLaw
import Math115.AllSmallRepairFiber
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Math115.RepairAcceptancePhysical

open OAI.ContingencyTables FirstSuccess ResidualMixture
open Math115.AllSmallRepairFiber Math115.RepairAcceptanceLaw Math115.RepairAcceptanceCoin
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Positive row and column margins make both support projections surjective. -/
theorem support_lower {r : I → ℕ} {c : J → ℕ} (A : Table r c)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) :
    max (Fintype.card I) (Fintype.card J) ≤ Fintype.card (SupportedCell A.val) := by
  apply max_le
  · apply Fintype.card_le_of_surjective (fun v : SupportedCell A.val => v.val.1)
    intro i
    have hp : 0 < ∑ j, A.val i j := by rw [A.property.1]; exact hr i
    obtain ⟨j, _, hj⟩ := Finset.sum_pos_iff.mp hp
    exact ⟨⟨(i,j), hj⟩, rfl⟩
  · apply Fintype.card_le_of_surjective (fun v : SupportedCell A.val => v.val.2)
    intro j
    have hp : 0 < ∑ i, A.val i j := by rw [A.property.2]; exact hc j
    obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hp
    exact ⟨⟨(i,j), hi⟩, rfl⟩

/-- Every supported natural entry contributes at least one to the total. -/
theorem support_upper {r : I → ℕ} {c : J → ℕ} (A : Table r c) :
    Fintype.card (SupportedCell A.val) ≤
      min (Fintype.card I * Fintype.card J) (∑ i, r i) := by
  apply le_min
  · exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_prod I J)
  · have he : Fintype.card (SupportedCell A.val) =
        ∑ v : I × J, if 0 < A.val v.1 v.2 then 1 else 0 := by
      rw [← Finset.sum_filter]
      simp [SupportedCell, Fintype.card_subtype]
    rw [he]
    calc
      _ ≤ ∑ v : I × J, A.val v.1 v.2 := by
        apply Finset.sum_le_sum
        intro v _
        split_ifs with hv
        · exact hv
        · exact Nat.zero_le _
      _ = ∑ i, r i := by rw [Fintype.sum_prod_type]; simp only [A.property.1]

def acceptanceScale : ℕ :=
  1 + (Fintype.card I * Fintype.card J - 1) * max (Fintype.card I) (Fintype.card J)

def fibreAllowance (r : I → ℕ) : ℕ :=
  1 + (Fintype.card I * Fintype.card J - 1) *
    min (Fintype.card I * Fintype.card J) (∑ i, r i)

def repairWeight {r : I → ℕ} {c : J → ℕ} (A : Table r c) : ℕ :=
  1 + (Fintype.card I * Fintype.card J - 1) * Fintype.card (SupportedCell A.val)

theorem actual_fibre_size (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hrU : ∀ i, r i < U) (hcU : ∀ j, c j < U) (A : Table r c) :
    fibreSize (reducedRepairTable r c U L hrU hcU) A = repairWeight A :=
  reduced_repairTable_fiber_card r c U L hrU hcU A

theorem actual_fibre_bounds (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hrU : ∀ i, r i < U) (hcU : ∀ j, c j < U)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (A : Table r c) :
    acceptanceScale (I := I) (J := J) ≤ fibreSize (reducedRepairTable r c U L hrU hcU) A ∧
    fibreSize (reducedRepairTable r c U L hrU hcU) A ≤ fibreAllowance (J := J) r := by
  unfold fibreSize
  rw [reduced_repairTable_fiber_card r c U L hrU hcU A]
  constructor
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (support_lower A hr hc)) 1
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (support_upper A)) 1

variable [Nonempty I] [Nonempty J]

theorem acceptance_ratio_dimension (r : I → ℕ) :
    (1 : ℚ) / ((min (Fintype.card I) (Fintype.card J) : ℕ) : ℚ) ≤
      (acceptanceScale (I := I) (J := J) : ℚ) / fibreAllowance (J := J) r := by
  have hm : 1 ≤ Fintype.card I := Fintype.card_pos
  have hn : 1 ≤ Fintype.card J := Fintype.card_pos
  have hd : (0 : ℚ) < ((min (Fintype.card I) (Fintype.card J) : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < min (Fintype.card I) (Fintype.card J) by omega)
  have hL : (0 : ℚ) < fibreAllowance (J := J) r := by
    unfold fibreAllowance
    positivity
  apply (div_le_div_iff₀ hd hL).mpr
  have he := support_allowance_bound (Fintype.card I) (Fintype.card J) (∑ i, r i) hm hn
  have heq : (fibreAllowance (J := J) r : ℚ) ≤
      ((min (Fintype.card I) (Fintype.card J) : ℕ) : ℚ) * acceptanceScale (I := I) (J := J) := by
    exact_mod_cast he
  simpa only [one_mul, mul_comm] using heq

theorem physical_nonempty (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hrU : ∀ i, r i < U) (hcU : ∀ j, c j < U) (fallback : Table r c) :
    Nonempty (ReducedSmallChain.States r c U L) := by
  have he := reduced_repairTable_fiber_card r c U L hrU hcU fallback
  have hp : 0 < Fintype.card {z : ReducedSmallChain.States r c U L //
      reducedRepairTable r c U L hrU hcU z = fallback} := by omega
  obtain ⟨z⟩ := Fintype.card_pos_iff.mp hp
  exact ⟨z.val⟩

/-- The exact stationary terminal succeeds with probability at least the
reciprocal of the smaller dimension. -/
theorem physical_stationary_success_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hrU : ∀ i, r i < U) (hcU : ∀ j, c j < U)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (fallback : Table r c) :
    (1 : ℚ) / ((min (Fintype.card I) (Fintype.card J) : ℕ) : ℚ) ≤ 1 - failureMass
      (bindLaw (@uniformLaw (ReducedSmallChain.States r c U L) _
        (physical_nonempty r c U L hrU hcU fallback))
        (terminalLaw (reducedRepairTable r c U L hrU hcU)
          (acceptanceScale (I := I) (J := J))
          (fun A => (actual_fibre_bounds r c U L hrU hcU hr hc A).1))) id := by
  letI : Nonempty (Table r c) := ⟨fallback⟩
  letI : Nonempty (ReducedSmallChain.States r c U L) := physical_nonempty r c U L hrU hcU fallback
  exact (acceptance_ratio_dimension r).trans
    (stationary_success_lower (reducedRepairTable r c U L hrU hcU) _ _
      (by unfold acceptanceScale; omega)
      (fun A => (actual_fibre_bounds r c U L hrU hcU hr hc A).1)
      (fun A => (actual_fibre_bounds r c U L hrU hcU hr hc A).2))

/-- The literal physical repair and fixed-bit terminal, with all fibre bounds
derived from the positive all-small margins. Endpoint mixing is the sole error premise. -/
theorem physical_finiteBit_retry_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hrU : ∀ i, r i < U) (hcU : ∀ j, c j < U)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (fallback : Table r c) (p : RationalLaw (ReducedSmallChain.States r c U L))
    (δ : ℚ) (hp : variation p (@uniformLaw (ReducedSmallChain.States r c U L) _
      (physical_nonempty r c U L hrU hcU fallback)) ≤ δ)
    (k R : ℕ) :
    variation (retryLaw (bindLaw p (fun x =>
      finiteBitLaw (reducedRepairTable r c U L hrU hcU x) k
        (acceptanceScale (I := I) (J := J))
        (repairWeight (reducedRepairTable r c U L hrU hcU x)))) id fallback R)
      (@uniformLaw (Table r c) _ ⟨fallback⟩) ≤
      (1 - (acceptanceScale (I := I) (J := J) : ℚ) / fibreAllowance (J := J) r)^R +
        (R : ℚ) * (δ + 1 / (2 : ℚ)^k) := by
  letI : Nonempty (Table r c) := ⟨fallback⟩
  letI : Nonempty (ReducedSmallChain.States r c U L) := physical_nonempty r c U L hrU hcU fallback
  have h := finiteBit_repaired_retry_variation (reducedRepairTable r c U L hrU hcU)
    _ _ k (by unfold acceptanceScale; omega)
    (fun A => (actual_fibre_bounds r c U L hrU hcU hr hc A).1)
    (fun A => (actual_fibre_bounds r c U L hrU hcU hr hc A).2) p δ hp fallback R
  simpa only [actual_fibre_size r c U L hrU hcU] using h

end
end Math115.RepairAcceptancePhysical
