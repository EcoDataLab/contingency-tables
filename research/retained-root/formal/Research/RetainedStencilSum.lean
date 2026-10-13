import Math115.RetainedRoot
import Mathlib.Algebra.BigOperators.Intervals

namespace Research.RetainedStencilSum

open scoped BigOperators

noncomputable def prefixMass (z : ℕ → ℝ) (l : ℕ) : ℝ := ∑ i ∈ Finset.range l, z i

noncomputable def stencil (z c : ℕ → ℝ) (l : ℕ) : ℝ :=
  1 / z (l - 1) + 1 / z l + 2 * c l / (z (l - 1) * z l) -
    c (l - 1) / z (l - 1) ^ 2 - c (l + 1) / z l ^ 2

/-- Exact collection of the retained three-point correction stencil. The
unrestricted exterior coefficients are present with their negative signs.
Only P0=0 is needed; no coefficient bound is supplied as a hypothesis. -/
theorem correction_collection (P H G c : ℕ → ℝ) (hP0 : P 0 = 0) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), P (k + 1) *
      (2 * c (k + 1) * H (k + 1) - c k * G k - c (k + 2) * G (k + 1))) =
      -P 1 * c 0 * G 0 +
      (∑ k ∈ Finset.range n, c (k + 1) *
        (2 * P (k + 1) * H (k + 1) - P (k + 2) * G (k + 1) - P k * G k)) +
      c (n + 1) * (2 * P (n + 1) * H (n + 1) - P n * G n) -
      P (n + 1) * c (n + 2) * G (n + 1) := by
  induction n with
  | zero => simp only [Nat.zero_add, Finset.sum_range_one, Finset.sum_range_zero, hP0]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

@[simp] theorem prefixMass_zero (z : ℕ → ℝ) : prefixMass z 0 = 0 := by simp [prefixMass]

@[simp] theorem prefixMass_succ (z : ℕ → ℝ) (l : ℕ) :
    prefixMass z (l + 1) = prefixMass z l + z l := by simp [prefixMass, Finset.sum_range_succ]

theorem prefixMass_nonneg (z : ℕ → ℝ) (m l : ℕ) (hl : l ≤ m + 1)
    (hz : ∀ i, i ≤ m → 0 ≤ z i) : 0 ≤ prefixMass z l := by
  apply Finset.sum_nonneg
  intro i hi
  exact hz i (by have := Finset.mem_range.mp hi; omega)

theorem last_le_prefixMass (z : ℕ → ℝ) (m j : ℕ) (hj : j ≤ m)
    (hz : ∀ i, i ≤ m → 0 ≤ z i) : z j ≤ prefixMass z (j + 1) := by
  rw [prefixMass_succ]
  have h := prefixMass_nonneg z m j (by omega) hz
  linarith

/-- The increasing masses bound every prefixMass by its endpoint times its size. -/
theorem prefixMass_le_last (z : ℕ → ℝ) (m j : ℕ) (hj : j ≤ m)
    (hmono : ∀ i j, i ≤ j → j ≤ m → z i ≤ z j) :
    prefixMass z (j + 1) ≤ (j + 1 : ℕ) * z j := by
  calc
    _ ≤ ∑ _i ∈ Finset.range (j + 1), z j := by
      apply Finset.sum_le_sum
      intro i hi
      exact hmono i j (by have := Finset.mem_range.mp hi; omega) hj
    _ = _ := by simp


/-- The collected interior coefficient is the existing compiled scalar one. -/
theorem collected_interior (z : ℕ → ℝ) (j : ℕ) (ha : 0 < z j) (hb : 0 < z (j + 1)) :
    2 * prefixMass z (j + 1) / (z j * z (j + 1)) -
      prefixMass z (j + 2) / z (j + 1) ^ 2 - prefixMass z j / z j ^ 2 =
    Math115.RetainedRoot.interiorCoefficient (z j) (z (j + 1)) (prefixMass z (j + 1)) := by
  rw [show j + 2 = (j + 1) + 1 by omega]
  simp only [prefixMass_succ]
  unfold Math115.RetainedRoot.interiorCoefficient
  field_simp
  ring

theorem collected_endpoint (z : ℕ → ℝ) (j : ℕ) :
    2 * prefixMass z (j + 1) / (z j * z (j + 1)) - prefixMass z j / z j ^ 2 =
    Math115.RetainedRoot.endpointCoefficient (z j) (z (j + 1)) (prefixMass z (j + 1)) := by
  unfold Math115.RetainedRoot.endpointCoefficient
  rw [prefixMass_succ]
  ring

/-- Actual denominator and prefix instantiation of the finite collection,
including both exterior corrections at their unrestricted actual values. -/
theorem actual_correction_collection (z c : ℕ → ℝ) (n : ℕ)
    (hz : ∀ i, i ≤ n + 1 → 0 < z i) :
    (∑ k ∈ Finset.range (n + 1), prefixMass z (k + 1) *
      (2 * c (k + 1) / (z k * z (k + 1)) - c k / z k ^ 2 - c (k + 2) / z (k + 1) ^ 2)) =
      -prefixMass z 1 * c 0 / z 0 ^ 2 +
      (∑ k ∈ Finset.range n, c (k + 1) *
        Math115.RetainedRoot.interiorCoefficient (z k) (z (k + 1)) (prefixMass z (k + 1))) +
      c (n + 1) * Math115.RetainedRoot.endpointCoefficient (z n) (z (n + 1)) (prefixMass z (n + 1)) -
      prefixMass z (n + 1) * c (n + 2) / z (n + 1) ^ 2 := by
  have h := correction_collection (prefixMass z)
    (fun l => 1 / (z (l - 1) * z l)) (fun l => 1 / z l ^ 2) c (prefixMass_zero z) n
  simp only [Nat.add_sub_cancel] at h
  have hi (k : ℕ) (hk : k < n) :
      2 * prefixMass z (k + 1) / (z k * z (k + 1)) -
        prefixMass z (k + 2) / z (k + 1) ^ 2 - prefixMass z k / z k ^ 2 =
      Math115.RetainedRoot.interiorCoefficient (z k) (z (k + 1)) (prefixMass z (k + 1)) :=
    collected_interior z k (hz k (by omega)) (hz (k + 1) (by omega))
  have hinner :
      (∑ k ∈ Finset.range n, c (k + 1) *
        (2 * prefixMass z (k + 1) * (1 / (z k * z (k + 1))) -
          prefixMass z (k + 2) * (1 / z (k + 1) ^ 2) - prefixMass z k * (1 / z k ^ 2))) =
      (∑ k ∈ Finset.range n, c (k + 1) *
        Math115.RetainedRoot.interiorCoefficient (z k) (z (k + 1)) (prefixMass z (k + 1))) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [← hi k (Finset.mem_range.mp hk)]
    ring
  rw [hinner] at h
  have he := collected_endpoint z n
  simp only [div_eq_mul_inv, one_mul] at h he ⊢
  rw [← he]
  exact h

/-- All correction coefficients are bounded from the actual moment cap,
prefix masses, and the compiled interior/endpoint lemmas. No exterior moment
cap and no assumed global coefficient bound occur. -/
theorem correction_sum_bound (z c : ℕ → ℝ) (K : ℝ) (n : ℕ)
    (hz : ∀ i, i ≤ n + 1 → 0 < z i)
    (hmono : ∀ i j, i ≤ j → j ≤ n + 1 → z i ≤ z j)
    (hc : ∀ i, i ≤ n + 2 → 0 ≤ c i)
    (hcap : ∀ j, 1 ≤ j → j ≤ n + 1 → c j ≤ K * max (z (j - 1)) (z j)) :
    (∑ k ∈ Finset.range (n + 1), prefixMass z (k + 1) *
      (2 * c (k + 1) / (z k * z (k + 1)) - c k / z k ^ 2 - c (k + 2) / z (k + 1) ^ 2)) ≤
      2 * K * (n + 1 : ℕ) := by
  rw [actual_correction_collection z c n hz]
  have hnon : ∀ i, i ≤ n + 1 → 0 ≤ z i := fun i hi => (hz i hi).le
  have hinterior :
      (∑ k ∈ Finset.range n, c (k + 1) *
        Math115.RetainedRoot.interiorCoefficient (z k) (z (k + 1)) (prefixMass z (k + 1))) ≤ (n : ℝ) * K := by
    calc
      _ ≤ ∑ _k ∈ Finset.range n, K := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_range.mp hk
        apply Math115.RetainedRoot.interior_cap _ _ _ _ K
          (hz k (by omega)) (hz (k + 1) (by omega))
          (last_le_prefixMass z (n + 1) k (by omega) hnon) (hc (k + 1) (by omega))
        simpa only [Nat.add_sub_cancel] using hcap (k + 1) (by omega) (by omega)
      _ = _ := by simp
  have hanchor : c (n + 1) * Math115.RetainedRoot.endpointCoefficient
      (z n) (z (n + 1)) (prefixMass z (n + 1)) ≤ K * ((n + 1 : ℕ) + 1 : ℝ) := by
    apply Math115.RetainedRoot.endpoint_cap _ _ _ _ K (n + 1 : ℕ)
      (hz n (by omega)) (hz (n + 1) (by omega))
      (hmono n (n + 1) (by omega) (by omega))
      (last_le_prefixMass z (n + 1) n (by omega) hnon)
      (prefixMass_le_last z (n + 1) n (by omega) hmono) (hc (n + 1) (by omega))
    have h := hcap (n + 1) (by omega) (by omega)
    simpa only [Nat.add_sub_cancel, max_eq_right (hmono n (n + 1) (by omega) (by omega))] using h
  have hleft : 0 ≤ prefixMass z 1 * c 0 / z 0 ^ 2 := by
    have hp := prefixMass_nonneg z (n + 1) 1 (by omega) hnon
    have hc0 := hc 0 (by omega)
    positivity
  have hright : 0 ≤ prefixMass z (n + 1) * c (n + 2) / z (n + 1) ^ 2 := by
    have hp := prefixMass_nonneg z (n + 1) (n + 1) (by omega) hnon
    have hc0 := hc (n + 2) (by omega)
    positivity
  have hleft' : -prefixMass z 1 * c 0 / z 0 ^ 2 ≤ 0 := by
    have hid : -prefixMass z 1 * c 0 / z 0 ^ 2 = -(prefixMass z 1 * c 0 / z 0 ^ 2) := by ring
    rw [hid]
    exact neg_nonpos.mpr hleft
  push_cast at hanchor ⊢
  calc
    _ ≤ (n : ℝ) * K + K * ((n : ℝ) + 1 + 1) := by linarith only [hleft', hinterior, hanchor, hright]
    _ = _ := by ring

lemma twice_successor_sum (m : ℕ) :
    (∑ k ∈ Finset.range m, 2 * ((k : ℝ) + 1)) = (m : ℝ) * ((m : ℝ) + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem base_sum_bound (z : ℕ → ℝ) (m : ℕ)
    (hz : ∀ i, i ≤ m → 0 < z i)
    (hmono : ∀ i j, i ≤ j → j ≤ m → z i ≤ z j) :
    (∑ k ∈ Finset.range m, prefixMass z (k + 1) * (1 / z k + 1 / z (k + 1))) ≤
      (m : ℝ) * ((m : ℝ) + 1) := by
  rw [← twice_successor_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hp := prefixMass_le_last z m k (by omega) hmono
  have hp' : prefixMass z (k + 1) ≤ (k + 1 : ℕ) * z (k + 1) :=
    hp.trans (mul_le_mul_of_nonneg_left (hmono k (k + 1) (by omega) (by omega)) (by positivity))
  have ha := (div_le_iff₀ (hz k (by omega))).mpr hp
  have hb := (div_le_iff₀ (hz (k + 1) (by omega))).mpr hp'
  push_cast at ha hb
  have hid : prefixMass z (k + 1) * (1 / z k + 1 / z (k + 1)) =
      prefixMass z (k + 1) / z k + prefixMass z (k + 1) / z (k + 1) := by ring
  rw [hid]
  linarith

/-- The complete increasing-side retained stencil sum, with arbitrary
nonnegative exterior corrections. The coefficient bound is derived from the
actual finite collection and local moment caps. -/
theorem increasing_stencil_sum_bound_range (z c : ℕ → ℝ) (K : ℝ) (m : ℕ)
    (hz : ∀ i, i ≤ m → 0 < z i)
    (hmono : ∀ i j, i ≤ j → j ≤ m → z i ≤ z j)
    (hc : ∀ i, i ≤ m + 1 → 0 ≤ c i)
    (hcap : ∀ j, 1 ≤ j → j ≤ m → c j ≤ K * max (z (j - 1)) (z j)) :
    (∑ k ∈ Finset.range m, prefixMass z (k + 1) * stencil z c (k + 1)) ≤
      (m : ℝ) * ((m : ℝ) + 1) + 2 * K * (m : ℝ) := by
  cases m with
  | zero => simp
  | succ n =>
    have hb := base_sum_bound z (n + 1) hz hmono
    have hc' := correction_sum_bound z c K n hz hmono hc hcap
    have hsplit : (∑ k ∈ Finset.range (n + 1), prefixMass z (k + 1) * stencil z c (k + 1)) =
        (∑ k ∈ Finset.range (n + 1), prefixMass z (k + 1) * (1 / z k + 1 / z (k + 1))) +
        (∑ k ∈ Finset.range (n + 1), prefixMass z (k + 1) *
          (2 * c (k + 1) / (z k * z (k + 1)) - c k / z k ^ 2 - c (k + 2) / z (k + 1) ^ 2)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp only [stencil, Nat.add_sub_cancel]
      ring
    rw [hsplit]
    exact add_le_add hb hc'


/-- The Icc edge-index API used by the actual mode-anchor path budgets. -/
theorem increasing_stencil_sum_bound (z c : ℕ → ℝ) (K : ℝ) (m : ℕ)
    (hz : ∀ i, i ≤ m → 0 < z i)
    (hmono : ∀ i j, i ≤ j → j ≤ m → z i ≤ z j)
    (hc : ∀ i, i ≤ m + 1 → 0 ≤ c i)
    (hcap : ∀ j, 1 ≤ j → j ≤ m → c j ≤ K * max (z (j - 1)) (z j)) :
    (∑ l ∈ Finset.Icc 1 m, (∑ i ∈ Finset.range l, z i) * stencil z c l) ≤
      (m : ℝ) * ((m : ℝ) + 1) + 2 * K * (m : ℝ) := by
  have h := increasing_stencil_sum_bound_range z c K m hz hmono hc hcap
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simpa only [prefixMass, Nat.add_sub_cancel, Nat.add_comm] using h

end Research.RetainedStencilSum
