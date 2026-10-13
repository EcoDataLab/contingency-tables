import Math115.SmallEntrySwitching

namespace Research.WeightedIncidence

open OAI.ContingencyTables Math115.SmallEntrySwitching Finset
open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

abbrev Level (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) (k : ℕ) :=
  {X : Table r c // X.val a s = k}

/-- Product weights count pairs of distinguishable units in the two donor
legs. The source is an actual ordinary table at height k; the output is its
literal unit four-cycle at height k+1. -/
theorem product_weighted_incidence {r : I → ℕ} {c : J → ℕ}
    (a : I) (s : J) (k : ℕ) :
    (∑ X : Level r c a s k,
      ∑ p : DonorLabels a s, X.val.val a p.2.val * X.val.val p.1.val s) ≤
    (∑ Y : Level r c a s (k + 1),
      ∑ p : DonorLabels a s, (Y.val.val a p.2.val + 1) * (Y.val.val p.1.val s + 1)) := by
  classical
  let Source := Σ X : Level r c a s k, Σ p : DonorLabels a s,
    Fin (X.val.val a p.2.val) × Fin (X.val.val p.1.val s)
  let Target := Σ Y : Level r c a s (k + 1), Σ p : DonorLabels a s,
    Fin (Y.val.val a p.2.val + 1) × Fin (Y.val.val p.1.val s + 1)
  let next (X : Level r c a s k) (p : DonorLabels a s)
      (v : Fin (X.val.val a p.2.val) × Fin (X.val.val p.1.val s)) : Table r c :=
    fourCycle X.val a p.1.val s p.2.val 1 (Ne.symm p.1.property) (Ne.symm p.2.property)
      (by have h := v.1.isLt; omega) (by have h := v.2.isLt; omega)
  have marked (X : Level r c a s k) (p : DonorLabels a s)
      (v : Fin (X.val.val a p.2.val) × Fin (X.val.val p.1.val s)) :
      (next X p v).val a s = k + 1 := by
    simp only [next, fourCycle_marked, X.property]
  have rowleg (X : Level r c a s k) (p : DonorLabels a s)
      (v : Fin (X.val.val a p.2.val) × Fin (X.val.val p.1.val s)) :
      (next X p v).val a p.2.val + 1 = X.val.val a p.2.val := by
    have h : ((next X p v).val a p.2.val : ℤ) = (X.val.val a p.2.val : ℤ) - 1 := by
      dsimp only [next]
      rw [fourCycle_cast]
      simp [fourCycleInt, Ne.symm p.1.property, p.2.property, sub_eq_add_neg]
    omega
  have colleg (X : Level r c a s k) (p : DonorLabels a s)
      (v : Fin (X.val.val a p.2.val) × Fin (X.val.val p.1.val s)) :
      (next X p v).val p.1.val s + 1 = X.val.val p.1.val s := by
    have h : ((next X p v).val p.1.val s : ℤ) = (X.val.val p.1.val s : ℤ) - 1 := by
      dsimp only [next]
      rw [fourCycle_cast]
      simp [fourCycleInt, p.1.property, Ne.symm p.2.property, sub_eq_add_neg]
    omega
  let encode : Source → Target := fun z =>
    ⟨⟨next z.1 z.2.1 z.2.2, marked z.1 z.2.1 z.2.2⟩, z.2.1,
      ⟨⟨z.2.2.1.val, by rw [rowleg z.1 z.2.1 z.2.2]; exact z.2.2.1.isLt⟩,
       ⟨z.2.2.2.val, by rw [colleg z.1 z.2.1 z.2.2]; exact z.2.2.2.isLt⟩⟩⟩
  have hinj : Function.Injective encode := by
    rintro ⟨X,p,v⟩ ⟨Y,q,w⟩ heq
    have hout : next X p v = next Y q w := congrArg (fun z : Target => z.1.val) heq
    have hd : p = q := congrArg (fun z : Target => z.2.1) heq
    have hv : v.1.val = w.1.val := congrArg (fun z : Target => z.2.2.1.val) heq
    have hw : v.2.val = w.2.val := congrArg (fun z : Target => z.2.2.2.val) heq
    subst q
    have hXY : X.val = Y.val := by
      apply Subtype.ext
      funext i j
      have h := congrArg (fun Z : Table r c => (Z.val i j : ℤ)) hout
      dsimp only [next] at h
      simp only [fourCycle_cast, fourCycleInt] at h
      exact Int.natCast_inj.mp (add_right_cancel h)
    have hXY' : X = Y := Subtype.ext hXY
    subst Y
    have hvw : v = w := Prod.ext (Fin.ext hv) (Fin.ext hw)
    subst w
    rfl
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa only [Source, Target, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] using hcard

/-- Margin equations factor the donor-weight sum exactly. -/
theorem source_weight {r : I → ℕ} {c : J → ℕ} (a : I) (s : J) (k : ℕ)
    (X : Level r c a s k) :
    (∑ p : DonorLabels a s, X.val.val a p.2.val * X.val.val p.1.val s) =
      (r a - k) * (c s - k) := by
  have hr : (∑ u : {u : J // u ≠ s}, X.val.val a u.val) = r a - k := by
    have h := Fintype.sum_eq_add_sum_subtype_ne (X.val.val a) s
    rw [X.val.property.1 a, X.property] at h
    omega
  have hc : (∑ b : {b : I // b ≠ a}, X.val.val b.val s) = c s - k := by
    have h := Fintype.sum_eq_add_sum_subtype_ne (fun b => X.val.val b s) a
    rw [X.val.property.2 s, X.property] at h
    omega
  dsimp only [DonorLabels]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul]
  rw [← Finset.mul_sum, hr, hc]

/-- The upper reverse weight ignores the opposite-corner positivity guard;
this only enlarges the codomain. Both full row and full column constraints
are used, rather than their minimum or a donor-count scalar assumption. -/
theorem target_weight {r : I → ℕ} {c : J → ℕ} (a : I) (s : J) (k : ℕ)
    (Y : Level r c a s (k + 1)) :
    (∑ p : DonorLabels a s, (Y.val.val a p.2.val + 1) * (Y.val.val p.1.val s + 1)) =
      (r a - (k + 1) + (Fintype.card J - 1)) *
      (c s - (k + 1) + (Fintype.card I - 1)) := by
  have hr := Fintype.sum_eq_add_sum_subtype_ne (Y.val.val a) s
  have hc := Fintype.sum_eq_add_sum_subtype_ne (fun b => Y.val.val b s) a
  rw [Y.val.property.1 a, Y.property] at hr
  rw [Y.val.property.2 s, Y.property] at hc
  have hri : (∑ u : {u : J // u ≠ s}, (Y.val.val a u.val + 1)) =
      r a - (k + 1) + (Fintype.card J - 1) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    omega
  have hci : (∑ b : {b : I // b ≠ a}, (Y.val.val b.val s + 1)) =
      c s - (k + 1) + (Fintype.card I - 1) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    omega
  dsimp only [DonorLabels]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul]
  rw [← Finset.mul_sum, hri, hci]

/-- Unconditional natural-count weighted recurrence in the actual Table model.
Zero or empty levels are covered; no equal-total or nonempty-fiber premise is
required. These shifted natural factors avoid invalid negative subtractions. -/
theorem weighted_level_recurrence (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) (k : ℕ) :
    Fintype.card (Level r c a s k) * ((r a - k) * (c s - k)) ≤
      Fintype.card (Level r c a s (k + 1)) *
        ((r a - (k + 1) + (Fintype.card J - 1)) *
         (c s - (k + 1) + (Fintype.card I - 1))) := by
  have h := product_weighted_incidence (r := r) (c := c) a s k
  simp_rw [source_weight, target_weight] at h
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using h

end Research.WeightedIncidence
