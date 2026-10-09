/-
SPDX-License-Identifier: Apache-2.0
Ordinary equal-total margins supply a positive physical state at free scales.
-/
import Math115.ReducedAllSmallChain

namespace Math115.PhysicalStateNonempty

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open ReducedSmallChain ReducedAllSmallChain
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallContextEnumeration RowMajorEnumeration SmallGraphProfiles

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The literal source padding, with free `L`, also handles empty types. -/
noncomputable def paddedTable (small : I → J → Bool) (L : ℕ)
    {r : I → ℕ} {c : J → ℕ} (X : Table r c) :
    Table (fun i => r i + rowLargeCount small i * L)
      (fun j => c j + columnLargeCount small j * L) :=
  ⟨fun i j => X.val i j + if small i j then 0 else L, by
    constructor
    · intro i
      rw [Finset.sum_add_distrib, X.property.1]
      dsimp only
      unfold rowLargeCount
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      cases small i j <;> simp
    · intro j
      rw [Finset.sum_add_distrib, X.property.2]
      dsimp only
      unfold columnLargeCount
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      cases small i j <;> simp⟩

omit [LinearOrder I] [LinearOrder J] in
lemma small_entry_le (r : I → ℕ) (c : J → ℕ) (U : ℕ) (X : Table r c)
    (i : I) (j : J) (hs : firstPaperSmall r c U i j = true) : X.val i j ≤ U := by
  have hh : r i < U ∨ c j < U := by
    simpa only [firstPaperSmall, decide_eq_true_eq] using hs
  rcases hh with hr | hc
  · exact (entry_le_row X.property i j).trans (Nat.le_of_lt hr)
  · have hcol : X.val i j ≤ c j := by
      rw [← X.property.2 j]
      exact Finset.single_le_sum (f := fun i => X.val i j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact hcol.trans (Nat.le_of_lt hc)

/-- An ordinary table supplies an actual positive-weight physical state.
No positivity of the margins or lower bound on `U,L` is needed. -/
theorem states_nonempty_of_table (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (X : Table r c) :
    Nonempty (States r c U L) := by
  let small := firstPaperSmall r c U
  let B := capacity r c U L
  let Y := paddedTable small L X
  have hB : ∀ i j, small i j = true → B i j = U := capacity_small r c U L
  have hR : ∀ i, smallRow small Y.val i ≤ r i := by
    intro i
    calc
      _ = ∑ j, if small i j then X.val i j else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        cases hs : small i j <;> simp [Y, paddedTable, hs]
      _ ≤ ∑ j, X.val i j := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
      _ = _ := X.property.1 i
  have hC : ∀ j, smallColumnView small Y.val j ≤ c j := by
    intro j
    calc
      _ = ∑ i, if small i j then X.val i j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        cases hs : small i j <;> simp [Y, paddedTable, hs]
      _ ≤ ∑ i, X.val i j := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
      _ = _ := X.property.2 j
  have hY : ∀ i j, small i j = true → Y.val i j ≤ U := by
    intro i j hs
    change X.val i j + (if small i j then 0 else L) ≤ U
    simpa only [hs, ite_true, Nat.add_zero] using small_entry_le r c U X i j hs
  let x : Cells small → Fin (U + 1) :=
    fun a => ⟨Y.val a.val.1 a.val.2, Nat.lt_succ_of_le (hY _ _ a.property)⟩
  let p : Profiles small B :=
    ⟨choiceProfile small B U hB x, Or.inl (choiceProfile_balanced small B U hB x)⟩
  let Z : CompletionFibre small B r (fun i => r i + rowLargeCount small i * L)
      c (fun j => c j + columnLargeCount small j * L) (naturalProfile p.val) := by
    refine ⟨⟨(Y.val, Y.val), Y.property⟩, hR, hC, ?_, ?_, ?_⟩
    · intro i j hs
      constructor
      · rfl
      · change Y.val i j = B i j - (U - Y.val i j)
        rw [hB i j hs, Nat.sub_sub_self (hY i j hs)]
    · intro _ _ _
      rfl
    · intro i j _
      exact paper_residual_capacity r c (dimensionAllowance (I := I) (J := J)) L U
        dimension_le_allowance ⟨Y, hR, hC⟩ i j
  have hp : 0 < hardMarginal small B r c L (naturalProfile p.val) := by
    rw [hardMarginal_eq_fibre_card small B r c L _ (naturalProfile_bounded p.val)]
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty (CompletionFibre small B r
      (fun i => r i + rowLargeCount small i * L) c
      (fun j => c j + columnLargeCount small j * L) (naturalProfile p.val)) from ⟨Z⟩)
  exact ⟨⟨p, hp⟩⟩

/-- Equal ordinary total margins discharge the chain's state-nonemptiness
premise, including empty row or column types. -/
theorem states_nonempty (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) : Nonempty (States r c U L) := by
  obtain ⟨X⟩ := table_nonempty r c htotal
  exact states_nonempty_of_table r c U L X

/-- The actual automatically selected ideal chain from equal total margins. -/
noncomputable def feasibleReducedChain (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) : FiniteChain (ReducedStates r c) := by
  letI := states_nonempty r c (reducedU (I := I) (J := J))
    (reducedL (I := I) (J := J)) htotal
  exact reducedSelectedChain r c

/-- The feasible chain keeps the actual completion-weight stationary law. -/
theorem feasibleReducedChain_pi (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (z : ReducedStates r c) :
    (feasibleReducedChain r c htotal).π z =
      weight r c (reducedU (I := I) (J := J)) (reducedL (I := I) (J := J)) z /
        (∑ y, weight r c (reducedU (I := I) (J := J)) (reducedL (I := I) (J := J)) y) := by
  letI := states_nonempty r c (reducedU (I := I) (J := J))
    (reducedL (I := I) (J := J)) htotal
  exact selectedChain_pi r c _ _ z

/-- No reference or nonempty-state assumption remains for ordinary margins. -/
theorem feasibleReducedChain_poincare_d25 (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (H : ReducedStates r c → ℝ) :
    (feasibleReducedChain r c htotal).variance H ≤
      ((1024 * 47^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^25) *
        (feasibleReducedChain r c htotal).energy H := by
  letI := states_nonempty r c (reducedU (I := I) (J := J))
    (reducedL (I := I) (J := J)) htotal
  exact reducedSelectedChain_poincare_d25 r c H

end Math115.PhysicalStateNonempty
