import Research.RetainedPhysicalCap

namespace Math115.RetainedPhysicalSupport
open OAI.ContingencyTables
open scoped BigOperators Classical
open PaddedCompletions SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open FirstPaperProfiles FirstPaperContextTransport LargePairEnumeration BalancedFamily
open ExcessContextProfiles IntegerWeightedTransport

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [LinearOrder I] [LinearOrder J] in
/-- Padded full margins do not loosen the original small-row/column constraints. -/
theorem residual_small_entry_le_original
    (small : I → J → Bool) (r rbar : I → ℕ) (c cbar : J → ℕ)
    (T : ResidualTables small r c rbar cbar) (s : I×J) (hs : small s.1 s.2=true) :
    T.val.val s.1 s.2 ≤ min (r s.1) (c s.2) := by
  apply le_min
  · apply le_trans _ (T.property.1 s.1)
    unfold smallRow
    have h := Finset.single_le_sum
      (f := fun j => if small s.1 j then T.val.val s.1 j else 0)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ s.2)
    simpa only [hs, ↓reduceIte] using h
  · apply le_trans _ (T.property.2 s.2)
    unfold smallColumnView
    have h := Finset.single_le_sum
      (f := fun i => if small i s.2 then T.val.val i s.2 else 0)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ s.1)
    simpa only [hs, ↓reduceIte] using h

/-- Positive actual balanced child mass entails a literal residual table and
therefore bounds its current child coordinate by the original margins. -/
theorem positive_physical_child_le_original
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) (k : Fin (U+1))
    {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j)
    (hpos : 0 < eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U k.val)) : k.val ≤ min (r s.1) (c s.2) := by
  rw [eliminate_context_eq_child_card small B r c L s hs σ U hB hσ k e hcap] at hpos
  have hcard : 0 < Fintype.card (SmallResidualChild small r
      (fun i => r i+rowLargeCount small i*L) c
      (fun j => c j+columnLargeCount small j*L) s σ k.val) := by exact_mod_cast hpos
  obtain ⟨T⟩ := Fintype.card_pos_iff.mp hcard
  rw [← T.property.2]
  exact residual_small_entry_le_original small r _ c _ T.val s hs

/-- Uniform pair width chosen from the largest actual small-cell margin. -/
noncomputable def effectiveWidth (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ) : ℕ :=
  max 2 (1 + Finset.univ.sup (fun s : Cells small => min (r s.val.1) (c s.val.2)))

omit [LinearOrder I] [LinearOrder J] in
lemma small_margin_le_effectiveWidth_pred
    (small : I → J → Bool) (r : I → ℕ) (c : J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) :
    min (r s.1) (c s.2) ≤ effectiveWidth small r c - 1 := by
  have hsup := Finset.le_sup (f := fun s : Cells small => min (r s.val.1) (c s.val.2))
    (Finset.mem_univ (⟨s, hs⟩ : Cells small))
  dsimp only at hsup
  have hmax := le_max_right 2 (1 + Finset.univ.sup
    (fun s : Cells small => min (r s.val.1) (c s.val.2)))
  unfold effectiveWidth
  omega

/-- The diameter from any nonnegative starting level to a positive actual
child is at most V-1 for V=max(2,1+max_small min(original margins)). -/
theorem positive_physical_support_diameter
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) (β : Fin (U+1)) (α : ℕ)
    {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j)
    (hpos : 0 < eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U β.val)) : β.val - α ≤ effectiveWidth small r c - 1 := by
  have hchild := positive_physical_child_le_original small B r c L s hs σ U hB hσ β e hcap hpos
  exact (Nat.sub_le β.val α).trans
    (hchild.trans (small_margin_le_effectiveWidth_pred small r c s hs))

end Math115.RetainedPhysicalSupport

#print axioms Math115.RetainedPhysicalSupport.positive_physical_child_le_original
#print axioms Math115.RetainedPhysicalSupport.small_margin_le_effectiveWidth_pred

#print axioms Math115.RetainedPhysicalSupport.positive_physical_support_diameter
