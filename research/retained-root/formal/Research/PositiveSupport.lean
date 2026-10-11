import OAI.Combinatorics.ContingencyTables.Transport.FiniteExposureVariance
import Mathlib.Tactic

namespace Research.PositiveSupport
open scoped BigOperators Classical
open OAI.ContingencyTables.FiniteExposureVariance

/-- The finite child sequence has no strict interior valley. -/
def NoValley (z : ℕ → ℝ) (U : ℕ) : Prop :=
  ∀ i j k : ℕ, i ≤ j → j ≤ k → k ≤ U → min (z i) (z k) ≤ z j

/-- Actual positive interval and zero exterior segments inside the child box. -/
structure SupportInterval (z : ℕ → ℝ) (U α β : ℕ) : Prop where
  ordered : α ≤ β
  upper : β ≤ U
  positive : ∀ i, α ≤ i → i ≤ β → 0 < z i
  zeroOutside : ∀ i, i ≤ U → (i < α ∨ β < i) → z i = 0

/-- Finite nonnegative no-valley weights have one exact positive interval. -/
theorem positive_support_interval (z : ℕ → ℝ) (U : ℕ)
    (hz : ∀ i ≤ U, 0 ≤ z i) (hv : NoValley z U)
    (hne : ∃ i ≤ U, 0 < z i) : ∃ α β, SupportInterval z U α β := by
  let S := (Finset.range (U+1)).filter (fun i => 0 < z i)
  have hS : S.Nonempty := by
    obtain ⟨i, hi, hpos⟩ := hne
    exact ⟨i, by simp only [S, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hpos⟩⟩
  obtain ⟨α, hα, hmin⟩ := Finset.exists_min_image S id hS
  obtain ⟨β, hβ, hmax⟩ := Finset.exists_max_image S id hS
  have hαpos : 0 < z α := (Finset.mem_filter.mp hα).2
  have hβpos : 0 < z β := (Finset.mem_filter.mp hβ).2
  have hβU : β ≤ U := by have := Finset.mem_range.mp (Finset.mem_filter.mp hβ).1; omega
  refine ⟨α, β, ⟨hmin β hβ, hβU, ?_, ?_⟩⟩
  · intro i hαi hiβ
    exact lt_of_lt_of_le (lt_min hαpos hβpos) (hv α i β hαi hiβ hβU)
  · intro i hiU hout
    apply le_antisymm _ (hz i hiU)
    by_contra h
    have hipos : 0 < z i := lt_of_not_ge h
    have hiS : i ∈ S := by simp only [S, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hipos⟩
    have hlow := hmin i hiS
    have hupp := hmax i hiS
    dsimp only [id] at hlow hupp
    omega

/-- Restricting and shifting a support interval preserves no-valley. -/
theorem noValley_shift (z : ℕ → ℝ) (U α β : ℕ)
    (hs : SupportInterval z U α β) (hv : NoValley z U) :
    NoValley (fun k => z (α+k)) (β-α) := by
  intro i j k hij hjk hk
  exact hv (α+i) (α+j) (α+k) (by omega) (by omega) (by have := hs.ordered; have := hs.upper; omega)

/-- A finite maximum of no-valley weights gives the actual monotone sides. -/
theorem noValley_has_mode (z : ℕ → ℝ) (N : ℕ) (hv : NoValley z N) :
    ∃ m, m ≤ N ∧
      (∀ i j : ℕ, i ≤ j → j ≤ m → z i ≤ z j) ∧
      (∀ i j : ℕ, m ≤ i → i ≤ j → j ≤ N → z j ≤ z i) := by
  have hne : (Finset.range (N+1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (N+1)) z hne
  have hmN : m ≤ N := by have := Finset.mem_range.mp hm; omega
  refine ⟨m, hmN, ?_, ?_⟩
  · intro i j hij hjm
    have himax : z i ≤ z m := hmax i (by simp only [Finset.mem_range]; omega)
    simpa only [min_eq_left himax] using hv i j m hij hjm hmN
  · intro i j hmi hij hjN
    have hjmax : z j ≤ z m := hmax j (by simp only [Finset.mem_range]; omega)
    simpa only [min_eq_right hjmax] using hv m i j hmi hij hjN

/-- Exact finite sum reindexing; the zero exterior terms vanish literally. -/
theorem support_sum_shift (z F : ℕ → ℝ) (U α β : ℕ)
    (hs : SupportInterval z U α β) :
    (∑ i ∈ Finset.range (U+1), z i*F i) =
      ∑ k ∈ Finset.range (β-α+1), z (α+k)*F (α+k) := by
  have hsub : Finset.Icc α β ⊆ Finset.range (U+1) := by
    intro i hi
    have := Finset.mem_Icc.mp hi
    simp only [Finset.mem_range]
    have := hs.upper
    omega
  have hzero : ∀ i ∈ Finset.range (U+1), i ∉ Finset.Icc α β → z i*F i=0 := by
    intro i hi hout
    have hiU : i ≤ U := by have := Finset.mem_range.mp hi; omega
    have hnot := Finset.mem_Icc.not.mp hout
    have houtside : i < α ∨ β < i := by omega
    rw [hs.zeroOutside i hiU houtside, zero_mul]
  rw [← Finset.sum_subset hsub hzero]
  symm
  apply Finset.sum_bij (fun k _ => α+k)
  · intro k hk
    have hkN := Finset.mem_range.mp hk
    have := hs.ordered
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    omega
  · intro i hi
    have := Finset.mem_Icc.mp hi
    refine ⟨i-α, ?_, by omega⟩
    simp only [Finset.mem_range]
    omega
  · intro k hk
    rfl

/-- Restriction preserves the actual upstream weighted mean, with its literal
mass and first-moment sums, rather than introducing a variance premise. -/
theorem support_mean_shift (z h : ℕ → ℝ) (U α β : ℕ)
    (hs : SupportInterval z U α β) :
    mean (fun i : Fin (U+1) => z i.val) (fun i => h i.val) =
      mean (fun k : Fin (β-α+1) => z (α+k.val)) (fun k => h (α+k.val)) := by
  unfold mean
  rw [Fin.sum_univ_eq_sum_range (fun i => z i*h i) (U+1),
    Fin.sum_univ_eq_sum_range z (U+1),
    Fin.sum_univ_eq_sum_range (fun k => z (α+k)*h (α+k)) (β-α+1),
    Fin.sum_univ_eq_sum_range (fun k => z (α+k)) (β-α+1)]
  rw [support_sum_shift z h U α β hs]
  have hmass := support_sum_shift z (fun _ => 1) U α β hs
  simp only [mul_one] at hmass
  rw [hmass]

/-- The actual unnormalized finite weighted variance is exactly unchanged by
removing zero-mass end segments and shifting the positive interval to zero. -/
theorem support_variance_shift (z h : ℕ → ℝ) (U α β : ℕ)
    (hs : SupportInterval z U α β) :
    variance (fun i : Fin (U+1) => z i.val) (fun i => h i.val) =
      variance (fun k : Fin (β-α+1) => z (α+k.val)) (fun k => h (α+k.val)) := by
  unfold variance
  rw [support_mean_shift z h U α β hs]
  let M := mean (fun k : Fin (β-α+1) => z (α+k.val)) (fun k => h (α+k.val))
  change (∑ i : Fin (U+1), z i.val*(h i.val-M)^2) =
    ∑ k : Fin (β-α+1), z (α+k.val)*(h (α+k.val)-M)^2
  rw [Fin.sum_univ_eq_sum_range (fun i => z i*(h i-M)^2) (U+1),
    Fin.sum_univ_eq_sum_range (fun k => z (α+k)*(h (α+k)-M)^2) (β-α+1)]
  exact support_sum_shift z (fun i => (h i-M)^2) U α β hs

/-- Owned edges of the positive interval are a subset of the original path;
all omitted edge energies remain nonnegative. -/
theorem support_energy_sum_le (E : ℕ → ℝ) (U α β : ℕ)
    (hαβ : α ≤ β) (hβU : β ≤ U) (hE : ∀ l, 1 ≤ l → l ≤ U → 0 ≤ E l) :
    (∑ l ∈ Finset.Icc 1 (β-α), E (α+l)) ≤ ∑ l ∈ Finset.Icc 1 U, E l := by
  have heq : (∑ l ∈ Finset.Icc 1 (β-α), E (α+l)) =
      ∑ l ∈ Finset.Icc (α+1) β, E l := by
    apply Finset.sum_bij (fun l _ => α+l)
    · intro l hl
      have := Finset.mem_Icc.mp hl
      simp only [Finset.mem_Icc]
      omega
    · intro a ha b hb hab
      omega
    · intro l hl
      have := Finset.mem_Icc.mp hl
      refine ⟨l-α, ?_, by omega⟩
      simp only [Finset.mem_Icc]
      omega
    · intro l hl
      rfl
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    have := Finset.mem_Icc.mp hl
    simp only [Finset.mem_Icc]
    omega
  · intro l hl hout
    have := Finset.mem_Icc.mp hl
    exact hE l (by omega) (by omega)

/-- A positive singleton has exactly zero actual weighted variance. -/
lemma singleton_variance (a b : ℝ) (ha : 0 < a) :
    variance (fun _ : Fin 1 => a) (fun _ => b) = 0 := by
  have hm : mean (fun _ : Fin 1 => a) (fun _ => b) = b := by
    simp only [mean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
    field_simp
  simp only [variance, hm, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero,
    Finset.sum_const_zero]

/-- The original variance also vanishes when its actual positive support
consists of one child; this branch needs no positive spectral gap. -/
theorem singleton_support_variance (z h : ℕ → ℝ) (U α : ℕ)
    (hs : SupportInterval z U α α) :
    variance (fun i : Fin (U+1) => z i.val) (fun i => h i.val) = 0 := by
  rw [support_variance_shift z h U α α hs]
  have hα : 0 < z α := hs.positive α le_rfl le_rfl
  have hz' : ∀ k : Fin (α-α+1), 0 ≤ z (α+k.val) := by
    intro k
    have hk : k.val = 0 := by have := k.isLt; omega
    simpa only [hk, Nat.add_zero] using hα.le
  rw [variance_formula _ _ hz',
    Fin.sum_univ_eq_sum_range (fun k => z (α+k)*h (α+k)^2) (α-α+1),
    Fin.sum_univ_eq_sum_range (fun k => z (α+k)*h (α+k)) (α-α+1),
    Fin.sum_univ_eq_sum_range (fun k => z (α+k)) (α-α+1)]
  simp only [Nat.sub_self, zero_add, Finset.sum_range_one, Nat.add_zero]
  field_simp
  ring

/-- The complete positive sequence, mode, and exact variance restriction are
constructed from the original finite weights. A caller can apply a positive
unimodal path theorem directly to these witnesses, or use the singleton branch. -/
theorem positive_support_restriction (z h : ℕ → ℝ) (U : ℕ)
    (hz : ∀ i ≤ U, 0 ≤ z i) (hv : NoValley z U)
    (hne : ∃ i ≤ U, 0 < z i) :
    ∃ α β m, SupportInterval z U α β ∧ m ≤ β-α ∧
      (∀ k ≤ β-α, 0 < z (α+k)) ∧
      (∀ i j : ℕ, i ≤ j → j ≤ m → z (α+i) ≤ z (α+j)) ∧
      (∀ i j : ℕ, m ≤ i → i ≤ j → j ≤ β-α → z (α+j) ≤ z (α+i)) ∧
      variance (fun i : Fin (U+1) => z i.val) (fun i => h i.val) =
        variance (fun k : Fin (β-α+1) => z (α+k.val)) (fun k => h (α+k.val)) := by
  obtain ⟨α, β, hs⟩ := positive_support_interval z U hz hv hne
  obtain ⟨m, hm, hleft, hright⟩ := noValley_has_mode (fun k => z (α+k))
    (β-α) (noValley_shift z U α β hs hv)
  refine ⟨α, β, m, hs, hm, ?_, hleft, hright, support_variance_shift z h U α β hs⟩
  intro k hk
  apply hs.positive
  · omega
  · have := hs.ordered
    omega

end Research.PositiveSupport

#print axioms Research.PositiveSupport.positive_support_interval
#print axioms Research.PositiveSupport.support_variance_shift
#print axioms Research.PositiveSupport.support_energy_sum_le

#print axioms Research.PositiveSupport.singleton_support_variance
#print axioms Research.PositiveSupport.positive_support_restriction
