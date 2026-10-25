import Research.SpectralPath
import Research.RetainedStencilSum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Research.SpectralPrefix

open Research.SpectralPath
open OAI.ContingencyTables.FiniteExposureVariance
open scoped BigOperators Classical

noncomputable def leftMass (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) : ℝ :=
  ∑ i, if i.val ≤ l.val then z i else 0

noncomputable def rightMass (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) : ℝ :=
  ∑ i, if l.val < i.val then z i else 0

noncomputable def totalMass (N : ℕ) (z : Fin (N + 1) → ℝ) : ℝ := ∑ i, z i

noncomputable def cutMass (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) : ℝ :=
  leftMass N z l * rightMass N z l / totalMass N z

lemma mass_split (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) :
    leftMass N z l + rightMass N z l = totalMass N z := by
  unfold leftMass rightMass totalMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val ≤ l.val
  · simp [hi, show ¬l.val < i.val by omega]
  · simp [hi, show l.val < i.val by omega]

lemma leftMass_nonneg (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ leftMass N z l := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hz i
  · exact le_refl 0

lemma rightMass_nonneg (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ rightMass N z l := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hz i
  · exact le_refl 0

lemma totalMass_pos (N : ℕ) (z : Fin (N + 1) → ℝ) (hz : ∀ i, 0 < z i) :
    0 < totalMass N z := by
  apply Finset.sum_pos'
  · intro i _
    exact (hz i).le
  · exact ⟨0, Finset.mem_univ _, hz 0⟩

lemma weighted_pair_square_le {X : Type*} [Fintype X] (z h q : X → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (weightedPair z h q) ^ 2 ≤ weightedSquare z h * weightedSquare z q := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => mul_nonneg (hz i) (sq_nonneg (h i)))
    (fun i _ => mul_nonneg (hz i) (sq_nonneg (q i)))
  intro i _
  exact le_of_eq (by ring)

lemma indicator_variance (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N)
    (hz : ∀ i, 0 ≤ z i) (hZ : 0 < totalMass N z) :
    variance z (prefixIndicator N l) = cutMass N z l := by
  have hfirst : (∑ i, z i * prefixIndicator N l i) = leftMass N z l := by
    unfold prefixIndicator leftMass
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  have hsecond : (∑ i, z i * (prefixIndicator N l i) ^ 2) = leftMass N z l := by
    unfold prefixIndicator leftMass
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [variance_formula _ _ hz, hfirst, hsecond]
  have hm := mass_split N z l
  change leftMass N z l - (leftMass N z l) ^ 2 / totalMass N z = _
  unfold cutMass
  apply (mul_right_cancel₀ (ne_of_gt hZ))
  field_simp
  rw [← hm]
  ring

/-- Weighted Cauchy--Schwarz with the centered prefix indicator, for the
actual upstream unnormalized variance and an actual mean-zero observable. -/
theorem prefix_covariance_bound (N : ℕ) (z h : Fin (N + 1) → ℝ) (l : Fin N)
    (hz : ∀ i, 0 < z i) (hmean : weightedSum z h = 0) :
    (prefixFlux N z h l) ^ 2 ≤ cutMass N z l * variance z h := by
  have hCS := weighted_pair_square_le z h (centered z (prefixIndicator N l)) (fun i => (hz i).le)
  rw [weightedPair_centered_right z h _ hmean,
    weightedPair_prefixIndicator, weightedSquare_centered,
    indicator_variance N z l (fun i => (hz i).le) (totalMass_pos N z hz)] at hCS
  rw [← variance_meanZero z h hmean] at hCS
  simpa only [mul_comm] using hCS

lemma cutMass_nonneg (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) (hz : ∀ i, 0 < z i) :
    0 ≤ cutMass N z l :=
  div_nonneg (mul_nonneg (leftMass_nonneg N z l (fun i => (hz i).le))
    (rightMass_nonneg N z l (fun i => (hz i).le))) (totalMass_pos N z hz).le

lemma cutMass_le_left (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) (hz : ∀ i, 0 < z i) :
    cutMass N z l ≤ leftMass N z l := by
  apply (div_le_iff₀ (totalMass_pos N z hz)).mpr
  have hm := mass_split N z l
  have hs := sq_nonneg (leftMass N z l)
  rw [← hm]
  nlinarith only [hs]

lemma cutMass_le_right (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) (hz : ∀ i, 0 < z i) :
    cutMass N z l ≤ rightMass N z l := by
  apply (div_le_iff₀ (totalMass_pos N z hz)).mpr
  have hm := mass_split N z l
  have hs := sq_nonneg (rightMass N z l)
  rw [← hm]
  nlinarith only [hs]

lemma cutMass_le_quarter (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) (hz : ∀ i, 0 < z i) :
    cutMass N z l ≤ totalMass N z / 4 := by
  apply (div_le_iff₀ (totalMass_pos N z hz)).mpr
  have hm := mass_split N z l
  have hs := sq_nonneg (leftMass N z l - rightMass N z l)
  rw [← hm]
  nlinarith only [hs]

lemma leftMass_eq_Iic (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) :
    leftMass N z l = ∑ i ∈ Finset.Iic l.castSucc, z i := by
  have he : (Finset.univ : Finset (Fin (N + 1))).filter (fun i => i.val ≤ l.val) =
      Finset.Iic l.castSucc := by
    ext i
    simp [Fin.le_def]
  rw [← he, Finset.sum_filter]
  rfl

lemma rightMass_eq_Ici (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) :
    rightMass N z l = ∑ i ∈ Finset.Ici l.succ, z i := by
  have he : (Finset.univ : Finset (Fin (N + 1))).filter (fun i => l.val < i.val) =
      Finset.Ici l.succ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def, Fin.val_succ]
    omega
  rw [← he, Finset.sum_filter]
  rfl

lemma leftMass_bound (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) (m : ℕ)
    (hl : l.val + 1 ≤ m)
    (hmono : ∀ i j : Fin (N + 1), i.val ≤ j.val → j.val ≤ m → z i ≤ z j) :
    leftMass N z l ≤ ((l.val : ℝ) + 1) * z l.castSucc := by
  rw [leftMass_eq_Iic]
  calc
    _ ≤ ∑ _i ∈ Finset.Iic l.castSucc, z l.castSucc := by
      apply Finset.sum_le_sum
      intro i hi
      exact hmono i l.castSucc (by simpa only [Finset.mem_Iic, Fin.le_def, Fin.val_castSucc] using hi) (by simpa only [Fin.val_castSucc] using (show l.val ≤ m by omega))
    _ = _ := by simp [Fin.card_Iic]

lemma rightMass_bound (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) (m : ℕ)
    (hl : m < l.val + 1)
    (hmono : ∀ i j : Fin (N + 1), m ≤ i.val → i.val ≤ j.val → z j ≤ z i) :
    rightMass N z l ≤ (N - l.val : ℕ) * z l.succ := by
  rw [rightMass_eq_Ici]
  calc
    _ ≤ ∑ _i ∈ Finset.Ici l.succ, z l.succ := by
      apply Finset.sum_le_sum
      intro i hi
      exact hmono l.succ i (by simpa only [Fin.val_succ] using (show m ≤ l.val + 1 by omega))
        (by simpa only [Finset.mem_Ici, Fin.le_def] using hi)
    _ = _ := by simp [Fin.card_Ici, Nat.add_sub_add_right]


lemma variance_nonnegative (N : ℕ) (z h : Fin (N + 1) → ℝ) (hz : ∀ i, 0 < z i) :
    0 ≤ variance z h := Finset.sum_nonneg (fun i _ => mul_nonneg (hz i).le (sq_nonneg _))

lemma cut_base_left (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) (m : ℕ)
    (hz : ∀ i, 0 < z i) (hl : l.val + 1 ≤ m)
    (hmono : ∀ i j : Fin (N + 1), i.val ≤ j.val → j.val ≤ m → z i ≤ z j) :
    cutMass N z l * (1 / z l.castSucc + 1 / z l.succ) ≤ 2 * ((l.val : ℝ) + 1) := by
  have hs := leftMass_bound N z l m hl hmono
  have hab : z l.castSucc ≤ z l.succ := hmono _ _ (by simp) (by simpa only [Fin.val_succ] using hl)
  have hs' := hs.trans (mul_le_mul_of_nonneg_left hab (show 0 ≤ (l.val : ℝ) + 1 by positivity))
  have ha := (div_le_iff₀ (hz l.castSucc)).mpr ((cutMass_le_left N z l hz).trans hs)
  have hb := (div_le_iff₀ (hz l.succ)).mpr ((cutMass_le_left N z l hz).trans hs')
  have hid : cutMass N z l * (1 / z l.castSucc + 1 / z l.succ) =
      cutMass N z l / z l.castSucc + cutMass N z l / z l.succ := by ring
  rw [hid]
  linarith

lemma cut_base_right (N : ℕ) (z : Fin (N + 1) → ℝ) (l : Fin N) (m : ℕ)
    (hz : ∀ i, 0 < z i) (hl : m < l.val + 1)
    (hmono : ∀ i j : Fin (N + 1), m ≤ i.val → i.val ≤ j.val → z j ≤ z i) :
    cutMass N z l * (1 / z l.castSucc + 1 / z l.succ) ≤ 2 * (N - l.val : ℕ) := by
  have hs := rightMass_bound N z l m hl hmono
  have hba : z l.succ ≤ z l.castSucc := hmono _ _
    (by simpa only [Fin.val_castSucc] using (show m ≤ l.val by omega)) (by simp)
  have hs' := hs.trans (mul_le_mul_of_nonneg_left hba (show 0 ≤ ((N - l.val : ℕ) : ℝ) by positivity))
  have ha := (div_le_iff₀ (hz l.castSucc)).mpr ((cutMass_le_right N z l hz).trans hs')
  have hb := (div_le_iff₀ (hz l.succ)).mpr ((cutMass_le_right N z l hz).trans hs)
  have hid : cutMass N z l * (1 / z l.castSucc + 1 / z l.succ) =
      cutMass N z l / z l.castSucc + cutMass N z l / z l.succ := by ring
  rw [hid]
  linarith

noncomputable def edgeWeight (N m k : ℕ) : ℝ :=
  if k < m then 2 * ((k : ℝ) + 1) else 2 * (N - k : ℕ)

lemma reverse_triangle_sum (a : ℕ) :
    (∑ j ∈ Finset.range a, 2 * ((a - j : ℕ) : ℝ)) = (a : ℝ) * ((a : ℝ) + 1) := by
  calc
    _ = ∑ j ∈ Finset.range a, 2 * ((a - (a - 1 - j) : ℕ) : ℝ) :=
      (Finset.sum_range_reflect (fun j => 2 * ((a - j : ℕ) : ℝ)) a).symm
    _ = ∑ j ∈ Finset.range a, 2 * ((j : ℝ) + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [show a - (a - 1 - j) = j + 1 by omega]
      push_cast
      rfl
    _ = _ := Research.RetainedStencilSum.twice_successor_sum a

lemma edgeWeight_sum (N m : ℕ) (hm : m ≤ N) :
    (∑ k ∈ Finset.range N, edgeWeight N m k) =
      (m : ℝ) * ((m : ℝ) + 1) + (N - m : ℕ) * ((N - m : ℕ) + 1 : ℝ) := by
  have hs := Finset.sum_range_add_sum_Ico (edgeWeight N m) hm
  rw [← hs]
  congr 1
  · calc
      _ = ∑ k ∈ Finset.range m, 2 * ((k : ℝ) + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [edgeWeight, Finset.mem_range.mp hk, ite_true]
      _ = _ := Research.RetainedStencilSum.twice_successor_sum m
  · rw [Finset.sum_Ico_eq_sum_range]
    calc
      _ = ∑ j ∈ Finset.range (N - m), 2 * ((N - m - j : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [edgeWeight, ite_eq_right (show ¬ m + j < m by omega)]
        congr 2
        omega
      _ = _ := reverse_triangle_sum (N - m)

lemma edgeWeight_sum_le (N m : ℕ) (hm : m ≤ N) :
    (∑ k ∈ Finset.range N, edgeWeight N m k) ≤ (N : ℝ) * ((N : ℝ) + 1) := by
  rw [edgeWeight_sum N m hm, Nat.cast_sub hm]
  have hmr : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hprod : 0 ≤ (m : ℝ) * ((N : ℝ) - m) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  nlinarith only [hprod]

/-- The actual mean-zero covariance bound and side monotonicity control the
whole base resistance contribution. Its coefficient is derived by the two
finite triangular sums rather than supplied as a Poincare premise. -/
theorem unimodal_base_bound (N : ℕ) (z h : Fin (N + 1) → ℝ) (m : ℕ)
    (hz : ∀ i, 0 < z i) (hmean : weightedSum z h = 0) (hm : m ≤ N)
    (hmonoL : ∀ i j : Fin (N + 1), i.val ≤ j.val → j.val ≤ m → z i ≤ z j)
    (hmonoR : ∀ i j : Fin (N + 1), m ≤ i.val → i.val ≤ j.val → z j ≤ z i) :
    (∑ l : Fin N, (1 / z l.castSucc + 1 / z l.succ) * (prefixFlux N z h l) ^ 2) ≤
      (N : ℝ) * ((N : ℝ) + 1) * variance z h := by
  have hv := variance_nonnegative N z h hz
  have hedge (l : Fin N) :
      (1 / z l.castSucc + 1 / z l.succ) * (prefixFlux N z h l) ^ 2 ≤
        edgeWeight N m l.val * variance z h := by
    have hcov := prefix_covariance_bound N z h l hz hmean
    have hbase : cutMass N z l * (1 / z l.castSucc + 1 / z l.succ) ≤ edgeWeight N m l.val := by
      by_cases hl : l.val < m
      · simpa only [edgeWeight, hl, ite_true] using cut_base_left N z l m hz (by omega) hmonoL
      · simpa only [edgeWeight, hl, ite_false] using cut_base_right N z l m hz (by omega) hmonoR
    calc
      _ ≤ (1 / z l.castSucc + 1 / z l.succ) * (cutMass N z l * variance z h) :=
        mul_le_mul_of_nonneg_left hcov
          (add_nonneg (one_div_nonneg.mpr (hz l.castSucc).le) (one_div_nonneg.mpr (hz l.succ).le))
      _ = (cutMass N z l * (1 / z l.castSucc + 1 / z l.succ)) * variance z h := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbase hv
  calc
    _ ≤ ∑ l : Fin N, edgeWeight N m l.val * variance z h := Finset.sum_le_sum (fun l _ => hedge l)
    _ = (∑ l : Fin N, edgeWeight N m l.val) * variance z h := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by simpa only [Fin.sum_univ_eq_sum_range] using edgeWeight_sum_le N m hm) hv

/-- Uniform prefix-square allowance for the regularization term. The sharper
quarter constant is obtained directly from the centered-indicator covariance. -/
theorem prefix_square_sum_bound (N : ℕ) (z h : Fin (N + 1) → ℝ)
    (hz : ∀ i, 0 < z i) (hmean : weightedSum z h = 0) :
    (∑ l : Fin N, (prefixFlux N z h l) ^ 2) ≤
      ((N : ℝ) * totalMass N z / 4) * variance z h := by
  have hv := variance_nonnegative N z h hz
  calc
    _ ≤ ∑ _l : Fin N, (totalMass N z / 4) * variance z h := by
      apply Finset.sum_le_sum
      intro l _
      exact (prefix_covariance_bound N z h l hz hmean).trans
        (mul_le_mul_of_nonneg_right (cutMass_le_quarter N z l hz) hv)
    _ = _ := by simp; ring

theorem prefix_square_sum_bound_coarse (N : ℕ) (z h : Fin (N + 1) → ℝ)
    (hz : ∀ i, 0 < z i) (hmean : weightedSum z h = 0) :
    (∑ l : Fin N, (prefixFlux N z h l) ^ 2) ≤ (N : ℝ) * totalMass N z * variance z h := by
  have hbound := prefix_square_sum_bound N z h hz hmean
  have hn : 0 ≤ (N : ℝ) * totalMass N z * variance z h :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (totalMass_pos N z hz).le) (variance_nonnegative N z h hz)
  nlinarith only [hbound, hn]

end Research.SpectralPrefix
