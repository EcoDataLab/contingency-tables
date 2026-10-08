/-
SPDX-License-Identifier: Apache-2.0
Uses the unchanged Table and fourCycle definitions from OpenAI's #115 source
at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The all-donor incidence count and
its refined small-entry estimate are additive refinements of SmallEntries.lean.
-/
import OAI.Combinatorics.ContingencyTables.Sampling.SmallEntries
import Mathlib.Tactic
import Mathlib.Data.Fintype.Sum
import Math115.SwitchingFiniteSums

namespace Math115.SmallEntrySwitching

open OAI.ContingencyTables Finset
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

abbrev DonorLabels (a : I) (s : J) := {b : I // b ≠ a} × {u : J // u ≠ s}

def donorCapacity {r : I → ℕ} {c : J → ℕ} (X : Table r c)
    (a : I) (s : J) (p : DonorLabels a s) : ℕ :=
  min (X.val a p.2.val) (X.val p.1.val s)

lemma card_donorLabels (a : I) (s : J) :
    Fintype.card (DonorLabels a s) =
      (Fintype.card I - 1) * (Fintype.card J - 1) := by
  simp only [DonorLabels, Fintype.card_prod]
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
  simp only [Fintype.card_subtype_eq]

/-- Every allowable positive amount is counted, for every pair of distinct
donor indices. Reverse labels retain the source height, which is strictly
less than the target height. -/
theorem all_donor_incidence_bound {r : I → ℕ} {c : J → ℕ}
    (a : I) (s : J) (t : ℕ) :
    (∑ X : {X : Table r c // X.val a s < t},
      ∑ p : DonorLabels a s, donorCapacity X.val a s p) ≤
      ((Fintype.card I - 1) * (Fintype.card J - 1)) *
        ∑ Y : Table r c, min t (Y.val a s) := by
  classical
  let Bad := {X : Table r c // X.val a s < t}
  let Moves := Σ X : Bad, Σ p : DonorLabels a s, Fin (donorCapacity X.val a s p)
  let Incoming := Σ Y : Table r c, DonorLabels a s × Fin (min t (Y.val a s))
  let next (X : Bad) (p : DonorLabels a s) (v : Fin (donorCapacity X.val a s p)) :
      Table r c :=
    fourCycle X.val a p.1.val s p.2.val (v.val + 1)
      (Ne.symm p.1.property) (Ne.symm p.2.property)
      ((Nat.succ_le_of_lt v.isLt).trans (min_le_left _ _))
      ((Nat.succ_le_of_lt v.isLt).trans (min_le_right _ _))
  have next_marked (X : Bad) (p : DonorLabels a s)
      (v : Fin (donorCapacity X.val a s p)) :
      (next X p v).val a s = X.val.val a s + (v.val + 1) := by
    simp only [next, fourCycle_marked]
  let encode : Moves → Incoming := fun z =>
    ⟨next z.1 z.2.1 z.2.2, z.2.1,
      ⟨z.1.val.val a s, lt_min z.1.property (by rw [next_marked]; omega)⟩⟩
  have hinj : Function.Injective encode := by
    rintro ⟨X, p, v⟩ ⟨Y, q, w⟩ heq
    have hout : next X p v = next Y q w := congrArg Sigma.fst heq
    have hd : p = q := congrArg (fun z : Incoming => z.2.1) heq
    have hh : X.val.val a s = Y.val.val a s :=
      congrArg (fun z : Incoming => z.2.2.val) heq
    subst q
    have hmarked := congrArg (fun Z : Table r c => Z.val a s) hout
    rw [next_marked, next_marked] at hmarked
    have hv : v.val = w.val := by omega
    have hXY : X.val = Y.val := by
      apply Subtype.ext
      funext i j
      have h := congrArg (fun Z : Table r c => (Z.val i j : ℤ)) hout
      dsimp only [next] at h
      simp only [fourCycle_cast, fourCycleInt] at h
      rw [hv] at h
      exact Int.natCast_inj.mp (add_right_cancel h)
    have hXY' : X = Y := Subtype.ext hXY
    subst Y
    have hv' : v = w := Fin.ext hv
    subst w
    rfl
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa only [Moves, Incoming, Bad, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    ← Finset.mul_sum] using hcard

/-- The table's margin equations supply the full donor mass, even when
individual donors or other margins vanish. -/
theorem donor_capacity_sum_lower {r : I → ℕ} {c : J → ℕ}
    (X : Table r c) (a : I) (s : J) :
    min (r a - X.val a s) (c s - X.val a s) ≤
      ∑ p : DonorLabels a s, donorCapacity X a s p := by
  have hr : (∑ u : {u : J // u ≠ s}, X.val a u.val) = r a - X.val a s := by
    have h := Fintype.sum_eq_add_sum_subtype_ne (X.val a) s
    rw [X.property.1 a] at h
    omega
  have hc : (∑ b : {b : I // b ≠ a}, X.val b.val s) = c s - X.val a s := by
    have h := Fintype.sum_eq_add_sum_subtype_ne (fun b => X.val b s) a
    rw [X.property.2 s] at h
    omega
  have h := SwitchingFiniteSums.min_fintype_sums_le_sum_pairwise_min
    (fun b : {b : I // b ≠ a} => X.val b.val s)
    (fun u : {u : J // u ≠ s} => X.val a u.val)
  simpa only [hr, hc, DonorLabels, Fintype.sum_prod_type, donorCapacity,
    min_comm] using h

theorem donor_capacity_sum_lower_of_margins {r : I → ℕ} {c : J → ℕ}
    (X : Table r c) (a : I) (s : J) (a₀ : ℕ)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) :
    a₀ - X.val a s ≤ ∑ p : DonorLabels a s, donorCapacity X a s p :=
  (le_min (Nat.sub_le_sub_right hrow _) (Nat.sub_le_sub_right hcol _)).trans
    (donor_capacity_sum_lower X a s)

omit [DecidableEq I] [DecidableEq J] in
/-- Counting every ordinary-table four-cycle gives the target-dependent
refinement. No donor lower-bound premise is assumed: it is derived above
from the original table's two incident margins. -/
theorem all_donor_small_entry_count_refined {r : I → ℕ} {c : J → ℕ}
    (a : I) (s : J) (a₀ t : ℕ)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) (ht : t ≤ a₀) :
    Fintype.card {X : Table r c // X.val a s < t} *
        (a₀ - t + 1 + (Fintype.card I - 1) * (Fintype.card J - 1)) ≤
      Fintype.card (Table r c) *
        (t * ((Fintype.card I - 1) * (Fintype.card J - 1))) := by
  classical
  let Bad := {X : Table r c // X.val a s < t}
  let e := (Fintype.card I - 1) * (Fintype.card J - 1)
  have hdegree : (∑ X : Bad, (a₀ - X.val.val a s)) ≤
      e * ∑ Y : Table r c, min t (Y.val a s) := by
    apply le_trans _ (all_donor_incidence_bound a s t)
    apply Finset.sum_le_sum
    intro X _
    exact donor_capacity_sum_lower_of_margins X.val a s a₀ hrow hcol
  have hdeficit : (∑ Y : Table r c, min t (Y.val a s)) +
      (∑ X : Bad, (t - X.val.val a s)) = t * Fintype.card (Table r c) := by
    have h := SwitchingFiniteSums.fintype_sum_min_add_sum_deficit
      (fun X : Table r c => X.val a s) t
    have hsub := Finset.sum_subtype (p := fun X : Table r c => X.val a s < t)
      (F := inferInstance)
      (Finset.univ.filter (fun X : Table r c => X.val a s < t))
      (fun X => by simp) (fun X : Table r c => t - X.val a s)
    rw [hsub] at h
    exact h
  have hpoint : Fintype.card Bad * (a₀ - t + 1 + e) ≤
      (∑ X : Bad, (a₀ - X.val.val a s)) +
        e * (∑ X : Bad, (t - X.val.val a s)) := by
    calc
      _ = ∑ _X : Bad, (a₀ - t + 1 + e) := by simp [Nat.mul_comm]
      _ ≤ ∑ X : Bad, ((a₀ - X.val.val a s) + e * (t - X.val.val a s)) := by
        apply Finset.sum_le_sum
        intro X _
        have hX := X.property
        have hpos : 1 ≤ t - X.val.val a s := by omega
        have he := Nat.mul_le_mul_left e hpos
        simp only [Nat.mul_one] at he
        omega
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  calc
    _ ≤ (∑ X : Bad, (a₀ - X.val.val a s)) +
        e * (∑ X : Bad, (t - X.val.val a s)) := hpoint
    _ ≤ e * (∑ Y : Table r c, min t (Y.val a s)) +
        e * (∑ X : Bad, (t - X.val.val a s)) := Nat.add_le_add_right hdegree _
    _ = e * ((∑ Y : Table r c, min t (Y.val a s)) +
        (∑ X : Bad, (t - X.val.val a s))) := by ring
    _ = _ := by rw [hdeficit]; dsimp only [e]; ring

omit [DecidableEq I] [DecidableEq J] in
/-- The simpler all-donor bound used by the reduced scale certificate. -/
theorem all_donor_small_entry_count {r : I → ℕ} {c : J → ℕ}
    (a : I) (s : J) (a₀ t : ℕ)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) (ht : t ≤ a₀) :
    Fintype.card {X : Table r c // X.val a s < t} * (a₀ - t + 1) ≤
      Fintype.card (Table r c) *
        (t * ((Fintype.card I - 1) * (Fintype.card J - 1))) := by
  apply le_trans _ (all_donor_small_entry_count_refined a s a₀ t hrow hcol ht)
  exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

omit [DecidableEq I] [DecidableEq J] in
/-- The refined probability under the uniform distribution on the upstream
ordinary-table fiber. Equal totals ensure that the denominator counts a
nonempty fiber. The threshold may be zero, when the event is empty. -/
theorem all_donor_small_entry_probability_refined {r : I → ℕ} {c : J → ℕ}
    (htotal : ∑ i, r i = ∑ j, c j)
    (a : I) (s : J) (a₀ t : ℕ)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) (ht : t ≤ a₀) :
    let e := (Fintype.card I - 1) * (Fintype.card J - 1)
    (Fintype.card {X : Table r c // X.val a s < t} : ℝ) /
        Fintype.card (Table r c) ≤
      (t : ℝ) * e / ((a₀ : ℝ) - t + 1 + e) := by
  classical
  dsimp only
  let e := (Fintype.card I - 1) * (Fintype.card J - 1)
  have hcard : 0 < Fintype.card (Table r c) :=
    Fintype.card_pos_iff.mpr (table_nonempty r c htotal)
  have hcardR : (0 : ℝ) < Fintype.card (Table r c) := by exact_mod_cast hcard
  have htR : (t : ℝ) ≤ a₀ := by exact_mod_cast ht
  have hden : (0 : ℝ) < (a₀ : ℝ) - t + 1 + e := by
    have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    linarith
  have hc := all_donor_small_entry_count_refined a s a₀ t hrow hcol ht
  have hcR : (Fintype.card {X : Table r c // X.val a s < t} : ℝ) *
      ((a₀ : ℝ) - t + 1 + e) ≤
      Fintype.card (Table r c) * ((t : ℝ) * e) := by
    have hcast : ((Fintype.card {X : Table r c // X.val a s < t} *
        (a₀ - t + 1 + e) : ℕ) : ℝ) ≤
        ((Fintype.card (Table r c) * (t * e) : ℕ) : ℝ) := by exact_mod_cast hc
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub ht] using hcast
  apply (div_le_div_iff₀ hcardR hden).mpr
  simpa only [mul_comm] using hcR

omit [DecidableEq I] [DecidableEq J] in
/-- The simpler uniform probability estimate with denominator `a₀-t+1`. -/
theorem all_donor_small_entry_probability {r : I → ℕ} {c : J → ℕ}
    (htotal : ∑ i, r i = ∑ j, c j)
    (a : I) (s : J) (a₀ t : ℕ)
    (hrow : a₀ ≤ r a) (hcol : a₀ ≤ c s) (ht : t ≤ a₀) :
    let e := (Fintype.card I - 1) * (Fintype.card J - 1)
    (Fintype.card {X : Table r c // X.val a s < t} : ℝ) /
        Fintype.card (Table r c) ≤
      (t : ℝ) * e / ((a₀ : ℝ) - t + 1) := by
  classical
  dsimp only
  let e := (Fintype.card I - 1) * (Fintype.card J - 1)
  have hcard : 0 < Fintype.card (Table r c) :=
    Fintype.card_pos_iff.mpr (table_nonempty r c htotal)
  have hcardR : (0 : ℝ) < Fintype.card (Table r c) := by exact_mod_cast hcard
  have htR : (t : ℝ) ≤ a₀ := by exact_mod_cast ht
  have hden : (0 : ℝ) < (a₀ : ℝ) - t + 1 := by linarith
  have hc := all_donor_small_entry_count a s a₀ t hrow hcol ht
  have hcR : (Fintype.card {X : Table r c // X.val a s < t} : ℝ) *
      ((a₀ : ℝ) - t + 1) ≤ Fintype.card (Table r c) * ((t : ℝ) * e) := by
    have hcast : ((Fintype.card {X : Table r c // X.val a s < t} *
        (a₀ - t + 1) : ℕ) : ℝ) ≤
        ((Fintype.card (Table r c) * (t * e) : ℕ) : ℝ) := by exact_mod_cast hc
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub ht] using hcast
  apply (div_le_div_iff₀ hcardR hden).mpr
  simpa only [mul_comm] using hcR

end Math115.SmallEntrySwitching
