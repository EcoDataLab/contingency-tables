import Research.WeightedIncidence
import Research.CompositionSurvival

namespace Research.ReciprocalZero

open OAI.ContingencyTables Research.WeightedIncidence
open Research.CompositionSurvival
open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Disjoint actual height levels inject into the original Table fiber. -/
theorem level_sum_le_total (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) (n : ℕ) :
    (∑ k ∈ Finset.range n, Fintype.card (Level r c a s k)) ≤ Fintype.card (Table r c) := by
  classical
  let Source := Σ k : Fin n, Level r c a s k.val
  let encode : Source → Table r c := fun z => z.2.val
  have hinj : Function.Injective encode := by
    rintro ⟨k,X⟩ ⟨l,Y⟩ h
    change X.val = Y.val at h
    have hkl : k = l := by
      apply Fin.ext
      have hx := X.property
      have hy := Y.property
      rw [h] at hx
      omega
    subst l
    have hxy : X = Y := Subtype.ext h
    subst Y
    rfl
  have h := Fintype.card_le_of_injective encode hinj
  rw [← Fin.sum_univ_eq_sum_range (fun k => Fintype.card (Level r c a s k)) n]
  simpa only [Source, Fintype.card_sigma] using h

/-- The actual weighted-level recurrence supplies the composition-product
lower bound. No recurrence or zero-entry probability is assumed by the caller. -/
theorem level_product_lower (r : I → ℕ) (c : J → ℕ) (a : I) (s : J)
    (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J) (k : ℕ) :
    (Fintype.card (Level r c a s 0) : ℝ) *
        tail (r a) (Fintype.card J - 2) k * tail (c s) (Fintype.card I - 2) k ≤
      Fintype.card (Level r c a s k) := by
  classical
  induction k with
  | zero => simp only [tail_zero, mul_one, le_refl]
  | succ k ih =>
    by_cases hk : k + 1 ≤ r a ∧ k + 1 ≤ c s
    · have hkr : k < r a := by omega
      have hkc : k < c s := by omega
      have hr := tail_succ_recurrence (r a) (Fintype.card J - 2) k hkr
      have hc := tail_succ_recurrence (c s) (Fintype.card I - 2) k hkc
      have hw := weighted_level_recurrence r c a s k
      have hwR : (Fintype.card (Level r c a s k) : ℝ) *
          (((r a - k) * (c s - k) : ℕ) : ℝ) ≤
        (Fintype.card (Level r c a s (k + 1)) : ℝ) *
          (((r a - (k + 1) + (Fintype.card J - 1)) *
            (c s - (k + 1) + (Fintype.card I - 1)) : ℕ) : ℝ) := by exact_mod_cast hw
      have er : r a - (k + 1) + (Fintype.card J - 1) = r a - k + (Fintype.card J - 2) := by omega
      have ec : c s - (k + 1) + (Fintype.card I - 1) = c s - k + (Fintype.card I - 2) := by omega
      rw [er, ec] at hwR
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hkr),
        Nat.cast_sub (Nat.le_of_lt hkc)] at hwR
      let A : ℝ := ((r a : ℝ) - k) * ((c s : ℝ) - k)
      let B : ℝ := ((r a : ℝ) - k + (Fintype.card J - 2 : ℕ)) *
        ((c s : ℝ) - k + (Fintype.card I - 2 : ℕ))
      have hA : 0 ≤ A := by
        dsimp only [A]
        have hrpos : (k : ℝ) < (r a : ℝ) := by exact_mod_cast hkr
        have hcpos : (k : ℝ) < (c s : ℝ) := by exact_mod_cast hkc
        exact mul_nonneg (by linarith) (by linarith)
      have hB : 0 < B := by
        dsimp only [B]
        have hrpos : (0 : ℝ) < (r a : ℝ) - k := by
          have h : (k : ℝ) < (r a : ℝ) := by exact_mod_cast hkr
          linarith
        have hcpos : (0 : ℝ) < (c s : ℝ) - k := by
          have h : (k : ℝ) < (c s : ℝ) := by exact_mod_cast hkc
          linarith
        have hq : (0 : ℝ) ≤ (Fintype.card J - 2 : ℕ) := Nat.cast_nonneg _
        have hp : (0 : ℝ) ≤ (Fintype.card I - 2 : ℕ) := Nat.cast_nonneg _
        apply mul_pos <;> linarith
      have hid : B * ((Fintype.card (Level r c a s 0) : ℝ) *
          tail (r a) (Fintype.card J - 2) (k + 1) * tail (c s) (Fintype.card I - 2) (k + 1)) =
        A * ((Fintype.card (Level r c a s 0) : ℝ) *
          tail (r a) (Fintype.card J - 2) k * tail (c s) (Fintype.card I - 2) k) := by
        dsimp only [A, B]
        calc
          _ = (Fintype.card (Level r c a s 0) : ℝ) *
            (((r a : ℝ) - k + (Fintype.card J - 2 : ℕ)) * tail (r a) (Fintype.card J - 2) (k + 1)) *
            (((c s : ℝ) - k + (Fintype.card I - 2 : ℕ)) * tail (c s) (Fintype.card I - 2) (k + 1)) := by ring
          _ = _ := by rw [hr, hc]; ring
      apply (mul_le_mul_iff_right₀ hB).mp
      calc
        _ = A * ((Fintype.card (Level r c a s 0) : ℝ) *
          tail (r a) (Fintype.card J - 2) k * tail (c s) (Fintype.card I - 2) k) := by
            simpa only [mul_comm] using hid
        _ ≤ A * (Fintype.card (Level r c a s k) : ℝ) := mul_le_mul_of_nonneg_left ih hA
        _ ≤ _ := by simpa only [A, B, mul_comm] using hwR
    · rcases not_and_or.mp hk with hr | hc
      · rw [tail_vanish (r a) (Fintype.card J - 2) (k + 1) (by omega)]
        simp only [mul_zero, zero_mul]
        exact Nat.cast_nonneg _
      · rw [tail_vanish (c s) (Fintype.card I - 2) (k + 1) (by omega)]
        simp only [mul_zero]
        exact Nat.cast_nonneg _

/-- Natural table count dominates zero-level count times the proved concrete
composition convolution. This also covers empty or unequal-total fibers. -/
theorem zero_count_times_convolution (r : I → ℕ) (c : J → ℕ) (a : I) (s : J)
    (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J) (n : ℕ) :
    (Fintype.card (Level r c a s 0) : ℝ) *
      (∑ k ∈ Finset.range n, tail (r a) (Fintype.card J - 2) k *
        tail (c s) (Fintype.card I - 2) k) ≤ Fintype.card (Table r c) := by
  classical
  have hlevels : (∑ k ∈ Finset.range n, (Fintype.card (Level r c a s k) : ℝ)) ≤
      Fintype.card (Table r c) := by exact_mod_cast level_sum_le_total r c a s n
  calc
    _ = ∑ k ∈ Finset.range n, (Fintype.card (Level r c a s 0) : ℝ) *
      tail (r a) (Fintype.card J - 2) k * tail (c s) (Fintype.card I - 2) k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ _ := (Finset.sum_le_sum (fun k _ => level_product_lower r c a s hI hJ k)).trans hlevels


/-- Sharp simultaneous-row/column zero-entry probability in the unchanged
ordinary table model. Equal total margins discharge the actual positive
uniform denominator; both dimensions are explicitly at least two. -/
theorem zero_entry_probability_reciprocal (r : I → ℕ) (c : J → ℕ) (a : I) (s : J)
    (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J)
    (htotal : (∑ i, r i) = ∑ j, c j) :
    (Fintype.card (Level r c a s 0) : ℝ) / Fintype.card (Table r c) ≤
      (Fintype.card J - 1 : ℕ) / ((r a : ℝ) + (Fintype.card J - 1 : ℕ)) +
      (Fintype.card I - 1 : ℕ) / ((c s : ℝ) + (Fintype.card I - 1 : ℕ)) -
      ((Fintype.card J - 1 : ℕ) * (Fintype.card I - 1 : ℕ) : ℕ) /
        (((r a : ℝ) + (Fintype.card J - 1 : ℕ)) *
         ((c s : ℝ) + (Fintype.card I - 1 : ℕ))) := by
  classical
  let n := r a + c s + 1
  let S : ℝ := ∑ k ∈ Finset.range n, tail (r a) (Fintype.card J - 2) k *
    tail (c s) (Fintype.card I - 2) k
  have hS : 0 < S := by
    have h := Research.SurvivalConvolution.one_le_sum_range
      (fun k => tail (r a) (Fintype.card J - 2) k * tail (c s) (Fintype.card I - 2) k)
      (fun k => mul_nonneg (tail_nonneg _ _ _) (tail_nonneg _ _ _))
      (by simp only [tail_zero, one_mul]) n (by dsimp only [n]; omega)
    change 1 ≤ S at h
    linarith
  have hcard : (0 : ℝ) < Fintype.card (Table r c) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (table_nonempty r c htotal)
  have hcount := zero_count_times_convolution r c a s hI hJ n
  change (Fintype.card (Level r c a s 0) : ℝ) * S ≤ Fintype.card (Table r c) at hcount
  have hprob : (Fintype.card (Level r c a s 0) : ℝ) / Fintype.card (Table r c) ≤ 1 / S := by
    apply (div_le_div_iff₀ hcard hS).mpr
    simpa only [one_mul] using hcount
  have hcomp := composition_reciprocal_bound (r a) (c s)
    (Fintype.card J - 2) (Fintype.card I - 2) n (by dsimp only [n]; omega) (by dsimp only [n]; omega)
  have hjcast : ((Fintype.card J - 2 : ℕ) : ℝ) + 1 = (Fintype.card J - 1 : ℕ) := by
    exact_mod_cast (show Fintype.card J - 2 + 1 = Fintype.card J - 1 by omega)
  have hicast : ((Fintype.card I - 2 : ℕ) : ℝ) + 1 = (Fintype.card I - 1 : ℕ) := by
    exact_mod_cast (show Fintype.card I - 2 + 1 = Fintype.card I - 1 by omega)
  simp only [add_assoc, hjcast, hicast] at hcomp
  exact hprob.trans (by simpa only [S, Nat.cast_mul] using hcomp)

end Research.ReciprocalZero
