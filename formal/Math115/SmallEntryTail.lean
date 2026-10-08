/-
SPDX-License-Identifier: Apache-2.0
-/
import Math115.SmallEntrySwitching
import Math115.SurvivalAlgebra

namespace Math115.SmallEntryTail

open OAI.ContingencyTables Finset
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Subtract a fixed amount from one margin. -/
def lowerMargin {K : Type*} [DecidableEq K] (r : K → ℕ) (a : K) (k : ℕ) : K → ℕ :=
  Function.update r a (r a - k)

/-- Add a fixed amount in the marked cell of a table with lowered margins. -/
def shiftUp {r : I → ℕ} {c : J → ℕ} (a : I) (s : J) (k : ℕ)
    (hr : k ≤ r a) (hc : k ≤ c s)
    (Y : Table (lowerMargin r a k) (lowerMargin c s k)) : Table r c :=
  ⟨fun i j => Y.val i j + if i = a ∧ j = s then k else 0, by
    constructor
    · intro i
      rw [sum_add_distrib, Y.property.1 i]
      by_cases hi : i = a
      · subst i
        simp only [true_and, sum_ite_eq', mem_univ, ite_true, lowerMargin,
          Function.update_self]
        exact Nat.sub_add_cancel hr
      · simp [hi, lowerMargin]
    · intro j
      rw [sum_add_distrib, Y.property.2 j]
      by_cases hj : j = s
      · subst j
        simp only [and_true, sum_ite_eq', mem_univ, ite_true, lowerMargin,
          Function.update_self]
        exact Nat.sub_add_cancel hc
      · simp [hj, lowerMargin]⟩

/-- Remove the conditioned amount from the marked cell. -/
def shiftDown {r : I → ℕ} {c : J → ℕ} (a : I) (s : J) (k : ℕ)
    (X : Table r c) (hX : k ≤ X.val a s) :
    Table (lowerMargin r a k) (lowerMargin c s k) := by
  let P := fun i j => if i = a ∧ j = s then k else 0
  have hP : ∀ i j, P i j ≤ X.val i j := by
    intro i j
    by_cases hi : i = a <;> by_cases hj : j = s <;> simp_all [P]
  refine ⟨fun i j => X.val i j - P i j, ?_, ?_⟩
  · intro i
    have hsum := sum_congr (s₁ := (univ : Finset J)) (f := fun j => X.val i j)
      (g := fun j => (X.val i j - P i j) + P i j) rfl
      (fun j _ => (Nat.sub_add_cancel (hP i j)).symm)
    rw [X.property.1 i, sum_add_distrib] at hsum
    by_cases hi : i = a
    · subst i
      simp only [P, true_and, sum_ite_eq', mem_univ, ite_true] at hsum ⊢
      simp only [lowerMargin, Function.update_self]
      omega
    · simpa [P, lowerMargin, hi] using hsum.symm
  · intro j
    have hsum := sum_congr (s₁ := (univ : Finset I)) (f := fun i => X.val i j)
      (g := fun i => (X.val i j - P i j) + P i j) rfl
      (fun i _ => (Nat.sub_add_cancel (hP i j)).symm)
    rw [X.property.2 j, sum_add_distrib] at hsum
    by_cases hj : j = s
    · subst j
      simp only [P, and_true, sum_ite_eq', mem_univ, ite_true] at hsum ⊢
      simp only [lowerMargin, Function.update_self]
      omega
    · simpa [P, lowerMargin, hj] using hsum.symm

/-- Conditioning an ordinary table on a lower bound in one cell gives
exactly the ordinary fiber with its two incident margins lowered. -/
def shiftEquiv {r : I → ℕ} {c : J → ℕ} (a : I) (s : J) (k : ℕ)
    (hr : k ≤ r a) (hc : k ≤ c s) :
    Table (lowerMargin r a k) (lowerMargin c s k) ≃
      {X : Table r c // k ≤ X.val a s} where
  toFun := fun Y => ⟨shiftUp a s k hr hc Y, by simp [shiftUp]⟩
  invFun := fun X => shiftDown a s k X.val X.property
  left_inv := by
    intro Y
    apply Subtype.ext
    funext i j
    simp [shiftDown, shiftUp]
  right_inv := by
    intro X
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    by_cases hi : i = a <;> by_cases hj : j = s
    · subst i; subst j
      simpa [shiftDown, shiftUp] using Nat.sub_add_cancel X.property
    · simp [shiftDown, shiftUp, hi, hj]
    · simp [shiftDown, shiftUp, hi, hj]
    · simp [shiftDown, shiftUp, hi, hj]

@[simp]
theorem shiftEquiv_marked {r : I → ℕ} {c : J → ℕ} (a : I) (s : J) (k : ℕ)
    (hr : k ≤ r a) (hc : k ≤ c s)
    (Y : Table (lowerMargin r a k) (lowerMargin c s k)) :
    (shiftEquiv a s k hr hc Y).val.val a s = Y.val a s + k := by
  simp [shiftEquiv, shiftUp]

noncomputable def survivalCount (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) (k : ℕ) : ℕ :=
  Fintype.card {X : Table r c // k ≤ X.val a s}

omit [DecidableEq I] [DecidableEq J] in
@[simp]
theorem survivalCount_zero (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) :
    survivalCount r c a s 0 = Fintype.card (Table r c) := by
  simp [survivalCount]

theorem shifted_card {r : I → ℕ} {c : J → ℕ} (a : I) (s : J) (k : ℕ)
    (hr : k ≤ r a) (hc : k ≤ c s) :
    Fintype.card (Table (lowerMargin r a k) (lowerMargin c s k)) =
      survivalCount r c a s k :=
  Fintype.card_congr (shiftEquiv a s k hr hc)

/-- The one-step positive part of a shifted fiber is the next survival set. -/
def shiftPositiveEquiv {r : I → ℕ} {c : J → ℕ} (a : I) (s : J) (k : ℕ)
    (hr : k ≤ r a) (hc : k ≤ c s) :
    {Y : Table (lowerMargin r a k) (lowerMargin c s k) // 1 ≤ Y.val a s} ≃
      {X : Table r c // k + 1 ≤ X.val a s} :=
  ((shiftEquiv a s k hr hc).subtypeEquiv (p := fun Y => 1 ≤ Y.val a s)
    (q := fun X => k + 1 ≤ X.val.val a s) (by intro Y; simp only [shiftEquiv_marked]; omega)).trans
    (Equiv.subtypeSubtypeEquivSubtype (p := fun X : Table r c => k ≤ X.val a s)
      (q := fun X : Table r c => k + 1 ≤ X.val a s) (by intro X h; omega))

/-- The zero-entry switching estimate, transported by the actual shift
bijection, supplies the survival recurrence without conditional division. -/
theorem survival_step {r : I → ℕ} {c : J → ℕ} (a : I) (s : J) (a₀ k : ℕ)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) (hk : k < a₀) :
    survivalCount r c a s k * (a₀ - k) ≤
      survivalCount r c a s (k + 1) *
        (a₀ - k + (Fintype.card I - 1) * (Fintype.card J - 1)) := by
  classical
  let R := lowerMargin r a k
  let C := lowerMargin c s k
  let T := Table R C
  let e := (Fintype.card I - 1) * (Fintype.card J - 1)
  have hr : k ≤ r a := (Nat.le_of_lt hk).trans hrow
  have hc : k ≤ c s := (Nat.le_of_lt hk).trans hcol
  have hbound := SmallEntrySwitching.all_donor_small_entry_count_refined
    (r := R) (c := C) a s (a₀ - k) 1
    (by simpa [R, lowerMargin] using Nat.sub_le_sub_right hrow k)
    (by simpa [C, lowerMargin] using Nat.sub_le_sub_right hcol k)
    (by omega)
  have hsplit : Fintype.card {Y : T // Y.val a s < 1} +
      Fintype.card {Y : T // 1 ≤ Y.val a s} = Fintype.card T := by
    have heq := Fintype.card_subtype_compl (fun Y : T => Y.val a s < 1)
    simp only [not_lt] at heq
    have hle := Fintype.card_subtype_le (fun Y : T => Y.val a s < 1)
    omega
  have hT : Fintype.card T = survivalCount r c a s k := shifted_card a s k hr hc
  have hpositive : Fintype.card {Y : T // 1 ≤ Y.val a s} =
      survivalCount r c a s (k + 1) :=
    Fintype.card_congr (shiftPositiveEquiv a s k hr hc)
  have hsub : a₀ - k - 1 + 1 = a₀ - k := by omega
  simp only [hsub, one_mul] at hbound
  change Fintype.card {Y : T // Y.val a s < 1} * (a₀ - k + e) ≤
    Fintype.card T * e at hbound
  rw [← hT, ← hpositive]
  change Fintype.card T * (a₀ - k) ≤
    Fintype.card {Y : T // 1 ≤ Y.val a s} * (a₀ - k + e)
  rw [← hsplit] at hbound ⊢
  nlinarith only [hbound]

/-- Real-cast form of the actual count recurrence. -/
theorem survival_step_real {r : I → ℕ} {c : J → ℕ} (a : I) (s : J) (a₀ k : ℕ)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) (hk : k < a₀) :
    (survivalCount r c a s k : ℝ) * ((a₀ : ℝ) - k) ≤
      (survivalCount r c a s (k + 1) : ℝ) *
        ((a₀ : ℝ) - k + ((Fintype.card I - 1) * (Fintype.card J - 1) : ℕ)) := by
  have h := survival_step a s a₀ k hrow hcol hk
  have hR : (survivalCount r c a s k : ℝ) * (a₀ - k : ℕ) ≤
      (survivalCount r c a s (k + 1) : ℝ) *
        (a₀ - k + (Fintype.card I - 1) * (Fintype.card J - 1) : ℕ) := by
    exact_mod_cast h
  simpa only [Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hk)] using hR

omit [DecidableEq I] [DecidableEq J] in
/-- Small and surviving entries partition the original fiber. -/
theorem small_card_add_survival (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) (t : ℕ) :
    Fintype.card {X : Table r c // X.val a s < t} + survivalCount r c a s t =
      Fintype.card (Table r c) := by
  classical
  have h := Fintype.card_subtype_compl (fun X : Table r c => X.val a s < t)
  simp only [not_lt] at h
  have hle := Fintype.card_subtype_le (fun X : Table r c => X.val a s < t)
  dsimp only [survivalCount]
  omega

omit [DecidableEq I] [DecidableEq J] in
/-- Conditioning successively on the marked entry strengthens the denominator
to `a₀+e`, uniformly over all thresholds `t≤a₀`. -/
theorem all_donor_small_entry_count_strong {r : I → ℕ} {c : J → ℕ}
    (a : I) (s : J) (a₀ t : ℕ)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) (ht : t ≤ a₀) :
    Fintype.card {X : Table r c // X.val a s < t} *
        (a₀ + (Fintype.card I - 1) * (Fintype.card J - 1)) ≤
      Fintype.card (Table r c) *
        (t * ((Fintype.card I - 1) * (Fintype.card J - 1))) := by
  classical
  let e := (Fintype.card I - 1) * (Fintype.card J - 1)
  change Fintype.card {X : Table r c // X.val a s < t} * (a₀ + e) ≤
    Fintype.card (Table r c) * (t * e)
  by_cases he : e = 0
  · have hbase := SmallEntrySwitching.all_donor_small_entry_count a s a₀ t hrow hcol ht
    change Fintype.card {X : Table r c // X.val a s < t} * (a₀ - t + 1) ≤
      Fintype.card (Table r c) * (t * e) at hbase
    rw [he] at hbase
    have hbad : Fintype.card {X : Table r c // X.val a s < t} = 0 := by nlinarith
    simp [hbad, he]
  · have hepos : 1 ≤ e := by omega
    have hlin := SurvivalAlgebra.nat_lower_tail_linear_bound a₀ e t hepos ht
      (fun k => (survivalCount r c a s k : ℝ)) (Nat.cast_nonneg _)
      (fun k hk => survival_step_real a s a₀ k hrow hcol hk)
    simp only [survivalCount_zero] at hlin
    have hsplit := small_card_add_survival r c a s t
    have hsplitR : (Fintype.card {X : Table r c // X.val a s < t} : ℝ) +
        (survivalCount r c a s t : ℝ) = Fintype.card (Table r c) := by exact_mod_cast hsplit
    have hdiff : (Fintype.card (Table r c) : ℝ) - survivalCount r c a s t =
        (Fintype.card {X : Table r c // X.val a s < t} : ℝ) := by linarith
    rw [hdiff] at hlin
    have hnat : Fintype.card {X : Table r c // X.val a s < t} * (a₀ + e) ≤
        Fintype.card (Table r c) * t * e := by exact_mod_cast hlin
    simpa only [mul_assoc] using hnat

omit [DecidableEq I] [DecidableEq J] in
/-- The stronger uniform ordinary-table probability estimate. Its proof
includes zero thresholds and zero donor-pair counts. -/
theorem all_donor_small_entry_probability_strong {r : I → ℕ} {c : J → ℕ}
    (htotal : ∑ i, r i = ∑ j, c j)
    (a : I) (s : J) (a₀ t : ℕ)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) (ht : t ≤ a₀) :
    let e := (Fintype.card I - 1) * (Fintype.card J - 1)
    (Fintype.card {X : Table r c // X.val a s < t} : ℝ) /
        Fintype.card (Table r c) ≤ (t : ℝ) * e / ((a₀ : ℝ) + e) := by
  classical
  dsimp only
  let e := (Fintype.card I - 1) * (Fintype.card J - 1)
  change (Fintype.card {X : Table r c // X.val a s < t} : ℝ) /
    Fintype.card (Table r c) ≤ (t : ℝ) * e / ((a₀ : ℝ) + e)
  by_cases hz : a₀ + e = 0
  · have htzero : t = 0 := by omega
    simp [htzero]
  · have hden : (0 : ℝ) < (a₀ : ℝ) + e := by exact_mod_cast Nat.pos_of_ne_zero hz
    have hcard : 0 < Fintype.card (Table r c) :=
      Fintype.card_pos_iff.mpr (table_nonempty r c htotal)
    have hcardR : (0 : ℝ) < Fintype.card (Table r c) := by exact_mod_cast hcard
    have hcount := all_donor_small_entry_count_strong a s a₀ t hrow hcol ht
    have hcountR : (Fintype.card {X : Table r c // X.val a s < t} : ℝ) *
        ((a₀ : ℝ) + e) ≤ Fintype.card (Table r c) * ((t : ℝ) * e) := by
      exact_mod_cast hcount
    apply (div_le_div_iff₀ hcardR hden).mpr
    simpa only [mul_comm] using hcountR

omit [DecidableEq I] [DecidableEq J] in
/-- The exact finite-product survival comparison obtained by multiplying
the conditional zero-entry estimates. -/
theorem all_donor_survival_product_count {r : I → ℕ} {c : J → ℕ}
    (a : I) (s : J) (a₀ t : ℕ)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) (ht : t ≤ a₀) :
    let e := (Fintype.card I - 1) * (Fintype.card J - 1)
    (Fintype.card (Table r c) : ℝ) *
        (∏ k ∈ Finset.range t, (((a₀ : ℝ) - k) / ((a₀ : ℝ) - k + e))) ≤
      (survivalCount r c a s t : ℝ) := by
  classical
  dsimp only
  have h := SurvivalAlgebra.nat_survival_product_bound a₀
    ((Fintype.card I - 1) * (Fintype.card J - 1)) t ht
    (fun k => (survivalCount r c a s k : ℝ))
    (fun k hk => survival_step_real a s a₀ k hrow hcol hk)
  simpa only [survivalCount_zero] using h

omit [DecidableEq I] [DecidableEq J] in
/-- The finite-product lower-tail probability bound for the original ordinary
fiber. All product denominators are positive when the index is below `t≤a₀`. -/
theorem all_donor_small_entry_probability_product {r : I → ℕ} {c : J → ℕ}
    (htotal : ∑ i, r i = ∑ j, c j)
    (a : I) (s : J) (a₀ t : ℕ)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) (ht : t ≤ a₀) :
    let e := (Fintype.card I - 1) * (Fintype.card J - 1)
    (Fintype.card {X : Table r c // X.val a s < t} : ℝ) /
        Fintype.card (Table r c) ≤
      1 - ∏ k ∈ Finset.range t, (((a₀ : ℝ) - k) / ((a₀ : ℝ) - k + e)) := by
  classical
  dsimp only
  have hprod := all_donor_survival_product_count a s a₀ t hrow hcol ht
  dsimp only at hprod
  have hsplit := small_card_add_survival r c a s t
  have hsplitR : (Fintype.card {X : Table r c // X.val a s < t} : ℝ) +
      (survivalCount r c a s t : ℝ) = Fintype.card (Table r c) := by exact_mod_cast hsplit
  have hcard : 0 < Fintype.card (Table r c) :=
    Fintype.card_pos_iff.mpr (table_nonempty r c htotal)
  have hcardR : (0 : ℝ) < Fintype.card (Table r c) := by exact_mod_cast hcard
  apply (div_le_iff₀ hcardR).mpr
  nlinarith only [hprod, hsplitR]

omit [DecidableEq I] [DecidableEq J] in
/-- Each counted survival level injects into one unit of its marked entry. -/
theorem survival_sum_le_entry_sum (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) (a₀ : ℕ) :
    (∑ k ∈ Finset.range a₀, survivalCount r c a s (k + 1)) ≤
      ∑ X : Table r c, X.val a s := by
  classical
  let Slots := Σ k : Fin a₀, {X : Table r c // k.val + 1 ≤ X.val a s}
  let Units := Σ X : Table r c, Fin (X.val a s)
  let encode : Slots → Units := fun z =>
    ⟨z.2.val, ⟨z.1.val, Nat.lt_of_succ_le z.2.property⟩⟩
  have hinj : Function.Injective encode := by
    rintro ⟨k, X⟩ ⟨l, Y⟩ heq
    have hX : X.val = Y.val := congrArg Sigma.fst heq
    have hk : k.val = l.val := congrArg (fun z : Units => z.2.val) heq
    have hkl : k = l := Fin.ext hk
    subst l
    have hXY : X = Y := Subtype.ext hX
    subst Y
    rfl
  have hcard := Fintype.card_le_of_injective encode hinj
  rw [← Fin.sum_univ_eq_sum_range (fun k => survivalCount r c a s (k + 1)) a₀]
  simpa only [Slots, Units, Fintype.card_sigma, Fintype.card_fin, survivalCount] using hcard

omit [DecidableEq I] [DecidableEq J] in
/-- Telescoping the actual hazard recurrence gives a first-moment bound. -/
theorem all_donor_entry_sum_lower {r : I → ℕ} {c : J → ℕ}
    (a : I) (s : J) (a₀ : ℕ) (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) :
    Fintype.card (Table r c) * a₀ ≤
      ((Fintype.card I - 1) * (Fintype.card J - 1) + 1) *
        ∑ X : Table r c, X.val a s := by
  classical
  let e := (Fintype.card I - 1) * (Fintype.card J - 1)
  have hmean := SurvivalAlgebra.nat_mean_tail_sum_bound a₀ e
    (fun k => (survivalCount r c a s k : ℝ))
    (fun k hk => survival_step_real a s a₀ k hrow hcol hk)
  simp only [survivalCount_zero] at hmean
  have hnat : Fintype.card (Table r c) * a₀ ≤
      (e + 1) * ∑ k ∈ Finset.range a₀, survivalCount r c a s (k + 1) := by
    exact_mod_cast hmean
  exact hnat.trans (Nat.mul_le_mul_left (e + 1) (survival_sum_le_entry_sum r c a s a₀))

omit [DecidableEq I] [DecidableEq J] in
/-- The uniform mean of the marked entry is at least `a₀/(e+1)`. -/
theorem all_donor_entry_mean_lower {r : I → ℕ} {c : J → ℕ}
    (htotal : ∑ i, r i = ∑ j, c j)
    (a : I) (s : J) (a₀ : ℕ) (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) :
    let e := (Fintype.card I - 1) * (Fintype.card J - 1)
    (a₀ : ℝ) / (e + 1) ≤
      (∑ X : Table r c, (X.val a s : ℝ)) / Fintype.card (Table r c) := by
  classical
  dsimp only
  let e := (Fintype.card I - 1) * (Fintype.card J - 1)
  have hden : (0 : ℝ) < (e : ℝ) + 1 := by positivity
  have hcard : 0 < Fintype.card (Table r c) :=
    Fintype.card_pos_iff.mpr (table_nonempty r c htotal)
  have hcardR : (0 : ℝ) < Fintype.card (Table r c) := by exact_mod_cast hcard
  have h := all_donor_entry_sum_lower a s a₀ hrow hcol
  have hR : (Fintype.card (Table r c) : ℝ) * a₀ ≤
      ((e : ℝ) + 1) * ∑ X : Table r c, (X.val a s : ℝ) := by exact_mod_cast h
  apply (div_le_div_iff₀ hden hcardR).mpr
  simpa only [mul_comm] using hR

end Math115.SmallEntryTail
