import RepairAcceptanceThreshold
import Math115.CompletionRetryBudget
import OAI.Combinatorics.ContingencyTables.Transport.RationalWalkApproximation

/-! Exact finite repair correction and bounded outer retries.  The fibre count
is computed from the actual repair map; geometric formulae are separate lemmas.
The endpoint distribution and its approximation error are explicit hypotheses. -/
namespace Math115.RepairAcceptanceLaw

open OAI.ContingencyTables FirstSuccess ResidualMixture
open Math115.RepairAcceptanceCoin Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]

def fibreSize (repair : S → A) (a : A) : ℕ :=
  Fintype.card {x : S // repair x = a}

omit [Fintype A] [Nonempty S] [Nonempty A] in
lemma fibreSize_pos_at (repair : S → A) (x : S) : 0 < fibreSize repair (repair x) := by
  exact Fintype.card_pos_iff.mpr ⟨⟨x, rfl⟩⟩

omit [Nonempty A] in
lemma repair_mass (repair : S → A) (a : A) :
    (mapLaw (uniformLaw (α := S)) repair).mass a =
      (fibreSize repair a : ℚ) / (Fintype.card S : ℚ) := by
  change (∑ x : S, if repair x = a then uniformMass (α := S) else 0) = _
  rw [← Finset.sum_filter, Finset.sum_const, ← Fintype.card_subtype]
  simp [fibreSize, uniformMass, nsmul_eq_mul, div_eq_mul_inv]

def terminalLaw (repair : S → A) (c : ℕ)
    (hc : ∀ a, c ≤ fibreSize repair a) (x : S) : RationalLaw (Option A) :=
  coinLaw (repair x) ((c : ℚ) / fibreSize repair (repair x))
    (div_nonneg (Nat.cast_nonneg c) (Nat.cast_nonneg _)) (by
      have hn : (0 : ℚ) < fibreSize repair (repair x) := by
        exact_mod_cast fibreSize_pos_at repair x
      apply (div_le_iff₀ hn).mpr
      simpa only [one_mul] using (show (c : ℚ) ≤ fibreSize repair (repair x) by exact_mod_cast hc (repair x)))

omit [Nonempty S] [Nonempty A] in
lemma terminal_some (repair : S → A) (c : ℕ)
    (hc : ∀ a, c ≤ fibreSize repair a) (x : S) (a : A) :
    (terminalLaw repair c hc x).mass (some a) =
      if repair x = a then (c : ℚ) / fibreSize repair a else 0 := by
  by_cases h : repair x = a
  · subst a
    simp [terminalLaw, coinLaw_mass_some]
  · simp [terminalLaw, coinLaw_mass_some, h, Ne.symm h]

omit [Nonempty A] in
/-- Uniform auxiliary states, repaired and thinned by reciprocal fibre size,
give the same successful mass to every output. -/
theorem stationary_success (repair : S → A) (c : ℕ) (hc0 : 0 < c)
    (hc : ∀ a, c ≤ fibreSize repair a) (a : A) :
    (bindLaw (uniformLaw (α := S)) (terminalLaw repair c hc)).mass (some a) =
      (c : ℚ) / (Fintype.card S : ℚ) := by
  have hf : (fibreSize repair a : ℚ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le hc0 (hc a)).ne'
  change (∑ x : S, uniformMass (α := S) *
    (terminalLaw repair c hc x).mass (some a)) = _
  simp_rw [terminal_some]
  have he : (∑ x : S, uniformMass (α := S) *
      (if repair x = a then (c : ℚ) / fibreSize repair a else 0)) =
      (∑ x : S, if repair x = a then uniformMass (α := S) else 0) *
        ((c : ℚ) / fibreSize repair a) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [he]
  change (mapLaw (uniformLaw (α := S)) repair).mass a *
    ((c : ℚ) / fibreSize repair a) = _
  rw [repair_mass]
  field_simp

omit [Nonempty A] in
lemma success_id (p : RationalLaw (Option A)) (a : A) :
    successMass p id a = p.mass (some a) := by
  simp [successMass]

omit [Nonempty A] in
lemma failure_id (p : RationalLaw (Option A)) :
    failureMass p id = p.mass none := by
  simp [failureMass]

omit [Nonempty A] in
/-- Exact ideal success probability, with no unknown normalizer in the rule. -/
theorem stationary_success_probability (repair : S → A) (c : ℕ) (hc0 : 0 < c)
    (hc : ∀ a, c ≤ fibreSize repair a) :
    1 - failureMass (bindLaw (uniformLaw (α := S)) (terminalLaw repair c hc)) id =
      (Fintype.card A : ℚ) * c / Fintype.card S := by
  have h := success_failure_total
    (bindLaw (uniformLaw (α := S)) (terminalLaw repair c hc)) id
  simp only [success_id, stationary_success repair c hc0 hc,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [← mul_div_assoc] at h
  linarith

omit [Nonempty S] [Nonempty A] in
lemma card_eq_sum_fibres (repair : S → A) :
    Fintype.card S = ∑ a : A, fibreSize repair a := by
  have h := Fintype.card_sigma (α := fun a : A => {x : S // repair x = a})
  let e : S ≃ (Σ a : A, {x : S // repair x = a}) :=
    { toFun := fun x => ⟨repair x, x, rfl⟩
      invFun := fun z => z.2.val
      left_inv := fun _ => rfl
      right_inv := fun z => by
        rcases z with ⟨a, x, hx⟩
        subst a
        rfl }
  exact (Fintype.card_congr e).trans h

theorem stationary_success_lower (repair : S → A) (c L : ℕ) (hc0 : 0 < c)
    (hc : ∀ a, c ≤ fibreSize repair a) (hL : ∀ a, fibreSize repair a ≤ L) :
    (c : ℚ) / L ≤
      1 - failureMass (bindLaw (uniformLaw (α := S)) (terminalLaw repair c hc)) id := by
  have hcard : (0 : ℚ) < Fintype.card S := by
    exact_mod_cast Fintype.card_pos (α := S)
  have hL0 : 0 < L :=
    lt_of_lt_of_le (lt_of_lt_of_le hc0 (hc (Classical.arbitrary A)))
      (hL (Classical.arbitrary A))
  have hLR : (0 : ℚ) < L := by exact_mod_cast hL0
  have hsize : Fintype.card S ≤ Fintype.card A * L := by
    rw [card_eq_sum_fibres repair]
    calc
      ∑ a : A, fibreSize repair a ≤ ∑ _ : A, L :=
        Finset.sum_le_sum (fun a _ => hL a)
      _ = _ := by simp
  rw [stationary_success_probability repair c hc0 hc]
  apply (div_le_div_iff₀ hLR hcard).mpr
  have hs : (Fintype.card S : ℚ) ≤ (Fintype.card A : ℚ) * L := by
    exact_mod_cast hsize
  nlinarith [mul_le_mul_of_nonneg_left hs (show (0 : ℚ) ≤ c by positivity)]

/-- Bounded first-success sampling from approximate endpoints and approximate
terminal coins. Errors are charged before rejection, with a feasible fallback. -/
theorem repaired_retry_variation (repair : S → A) (c L : ℕ) (hc0 : 0 < c)
    (hc : ∀ a, c ≤ fibreSize repair a) (hL : ∀ a, fibreSize repair a ≤ L)
    (p : RationalLaw S) (terminal : S → RationalLaw (Option A))
    (δ η : ℚ) (hp : variation p (uniformLaw (α := S)) ≤ δ)
    (ht : ∀ x, variation (terminal x) (terminalLaw repair c hc x) ≤ η)
    (fallback : A) (R : ℕ) :
    variation (retryLaw (bindLaw p terminal) id fallback R) (uniformLaw (α := A)) ≤
      (1 - (c : ℚ) / L)^R + (R : ℚ) * (δ + η) := by
  have hequal : ∀ a, successMass
      (bindLaw (uniformLaw (α := S)) (terminalLaw repair c hc)) id a =
      (c : ℚ) / Fintype.card S := by
    intro a
    rw [success_id]
    exact stationary_success repair c hc0 hc a
  have happ : variation (bindLaw p terminal)
      (bindLaw (uniformLaw (α := S)) (terminalLaw repair c hc)) ≤ δ + η :=
    (variation_bind_uniform _ _ _ _ η ht).trans (add_le_add hp le_rfl)
  exact approximate_retry_variation_of_success _ _ id _ hequal fallback R _ _ happ
    (stationary_success_lower repair c L hc0 hc hL)

/-- The implemented fixed-bit terminal closes the terminal approximation
premise. The remaining error input is the endpoint's distance from stationarity. -/
theorem finiteBit_repaired_retry_variation (repair : S → A) (c L k : ℕ) (hc0 : 0 < c)
    (hc : ∀ a, c ≤ fibreSize repair a) (hL : ∀ a, fibreSize repair a ≤ L)
    (p : RationalLaw S) (δ : ℚ) (hp : variation p (uniformLaw (α := S)) ≤ δ)
    (fallback : A) (R : ℕ) :
    variation (retryLaw (bindLaw p (fun x =>
      finiteBitLaw (repair x) k c (fibreSize repair (repair x)))) id fallback R)
      (uniformLaw (α := A)) ≤
      (1 - (c : ℚ) / L)^R + (R : ℚ) * (δ + 1 / (2 : ℚ)^k) := by
  apply repaired_retry_variation repair c L hc0 hc hL p _ δ _ hp _ fallback R
  intro x
  exact finiteBitLaw_variation_le (repair x) k c _ (fibreSize_pos_at repair x) (hc (repair x))

/-- The explicit support bounds give at most the smaller dimension as an
inverse-success allowance, including one-row and one-column shapes. -/
theorem support_allowance_bound (m n M : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    1 + (m * n - 1) * min (m * n) M ≤
      min m n * (1 + (m * n - 1) * max m n) := by
  calc
    _ ≤ 1 + (m * n - 1) * (m * n) := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (min_le_left _ _)) 1
    _ ≤ _ := by
      rcases le_total m n with h | h
      · rw [min_eq_left h, max_eq_right h]
        nlinarith only [hm]
      · rw [min_eq_right h, max_eq_left h]
        nlinarith only [hn]

end
end Math115.RepairAcceptanceLaw
