import Math115.ReducedSmallChain

namespace Research.ResidualSelectedBudget
open OAI.ContingencyTables
open PaddedCompletions CompletionCounts SmallContextCoordinates
open scoped BigOperators Classical

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [DecidableEq J]
noncomputable section

/-- Count ordinary lines below the cutoff, never padded margins. -/
def smallLineCount {K : Type*} [Fintype K] (v : K → ℕ) (U : ℕ) : ℕ :=
  Fintype.card {k // v k < U}

lemma small_line_sum_le {K : Type*} [Fintype K] (v : K → ℕ) (U : ℕ) :
    (∑ k, if v k < U then v k else 0) ≤ smallLineCount v U * (U-1) := by
  calc
    _ ≤ ∑ k, if v k < U then U-1 else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : v k < U
      · simp only [hk,ite_true]
        omega
      · simp [hk]
    _ = _ := by
      rw [←Finset.sum_filter]
      simp [smallLineCount,Fintype.card_subtype]

omit [DecidableEq J] in
lemma selected_sum_eq (r : I → ℕ) (c : J → ℕ) (U : ℕ) (A : I → J → ℕ) :
    (∑ t : Cells (firstPaperSmall r c U), A t.val.1 t.val.2) =
      ∑ i, ∑ j, if firstPaperSmall r c U i j then A i j else 0 := by
  calc
    _ = ∑ t ∈ Finset.univ.filter (fun t : I×J => firstPaperSmall r c U t.1 t.2=true),
        A t.1 t.2 := (Finset.sum_subtype _ (by simp) _).symm
    _ = _ := by rw [Finset.sum_filter,Fintype.sum_prod_type]

omit [DecidableEq J] in
/-- A literal source residual table retains its original partial constraints.
The full margins may be padded or arbitrary; they do not enter this budget. -/
theorem residual_selected_mass_le (r : I → ℕ) (c : J → ℕ) (rbar : I → ℕ) (cbar : J → ℕ)
    (U : ℕ) (A : ResidualTables (firstPaperSmall r c U) r c rbar cbar) :
    (∑ t : Cells (firstPaperSmall r c U), A.val.val t.val.1 t.val.2) ≤
      (smallLineCount r U + smallLineCount c U)*(U-1) := by
  have hr (i : I) : (if r i<U then ∑ j,A.val.val i j else 0) ≤
      (if r i<U then r i else 0) := by
    by_cases hi : r i<U
    · simpa [smallRow,firstPaperSmall,hi] using A.property.1 i
    · simp [hi]
  have hc (j : J) : (if c j<U then ∑ i,A.val.val i j else 0) ≤
      (if c j<U then c j else 0) := by
    by_cases hj : c j<U
    · simpa [smallColumnView,firstPaperSmall,hj] using A.property.2 j
    · simp [hj]
  have charge (i : I) (j : J) :
      (if firstPaperSmall r c U i j then A.val.val i j else 0) ≤
      (if r i<U then A.val.val i j else 0)+(if c j<U then A.val.val i j else 0) := by
    by_cases hi : r i<U <;> by_cases hj : c j<U <;> simp [firstPaperSmall,hi,hj]
  have hsplit :
      (∑ i,∑ j,if firstPaperSmall r c U i j then A.val.val i j else 0) ≤
      (∑ i,if r i<U then ∑ j,A.val.val i j else 0)+
        ∑ j,if c j<U then ∑ i,A.val.val i j else 0 := by
    calc
      _ ≤ ∑ i,∑ j,((if r i<U then A.val.val i j else 0)+(if c j<U then A.val.val i j else 0)) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => charge i j))
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          by_cases hi : r i<U <;> simp [hi]
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : c j<U <;> simp [hj]
  rw [selected_sum_eq]
  calc
    _ ≤ _ := hsplit
    _ ≤ (∑ i,if r i<U then r i else 0)+∑ j,if c j<U then c j else 0 :=
      Nat.add_le_add (Finset.sum_le_sum (fun i _ => hr i)) (Finset.sum_le_sum (fun j _ => hc j))
    _ ≤ smallLineCount r U*(U-1)+smallLineCount c U*(U-1) :=
      Nat.add_le_add (small_line_sum_le r U) (small_line_sum_le c U)
    _ = _ := by ring

/-- Any same-column donor subset uses no more than the total selected mass. -/
theorem residual_same_column_mass_le (r : I → ℕ) (c : J → ℕ) (rbar : I → ℕ) (cbar : J → ℕ)
    (U : ℕ) (A : ResidualTables (firstPaperSmall r c U) r c rbar cbar) (s : I×J) :
    (∑ t : Cells (firstPaperSmall r c U),
      if t.val.2=s.2 ∧ t.val.1≠s.1 then A.val.val t.val.1 t.val.2 else 0) ≤
      (smallLineCount r U+smallLineCount c U)*(U-1) := by
  apply le_trans _ (residual_selected_mass_le r c rbar cbar U A)
  apply Finset.sum_le_sum
  intro t _
  split_ifs <;> omega

/-- The exact donor recovered from the repaired full table at fixed labels. -/
def recoveredDonor (A : I → J → ℕ) (s : I×J) (t : I×J) : ℕ :=
  A t.1 t.2 + if t.2=s.2 then 0 else 1

omit [Fintype I] [Fintype J] in
lemma recovered_moment_le (A : I → J → ℕ) (U : ℕ) (s t : I×J) :
    recoveredDonor A s t*(U+1-recoveredDonor A s t) ≤ (U+1)*A t.1 t.2+U := by
  unfold recoveredDonor
  by_cases hc : t.2=s.2
  · simp only [hc,ite_true,Nat.add_zero]
    have h := Nat.mul_le_mul_left (A t.1 t.2) (Nat.sub_le (U+1) (A t.1 t.2))
    simp only [hc] at h
    nlinarith
  · simp only [hc,ite_false]
    have he : U+1-(A t.1 t.2+1)=U-A t.1 t.2 := by omega
    rw [he]
    have h := Nat.mul_le_mul_left (A t.1 t.2+1) (Nat.sub_le U (A t.1 t.2))
    nlinarith

/-- Pointwise aggregate of the literal recovered moments, including all cells.
Any feasible different-row donor image is a nonnegative subset of this sum. -/
theorem residual_recovered_moment_sum_le (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (U : ℕ)
    (A : ResidualTables (firstPaperSmall r c U) r c rbar cbar) (s : I×J) :
    (∑ t : Cells (firstPaperSmall r c U),
      recoveredDonor A.val.val s t.val*(U+1-recoveredDonor A.val.val s t.val)) ≤
      (smallLineCount r U+smallLineCount c U)*U^2+
        Fintype.card (Cells (firstPaperSmall r c U))*U := by
  have hs := residual_selected_mass_le r c rbar cbar U A
  have hU : (U+1)*(U-1) ≤ U^2 := by
    by_cases h : U=0
    · simp [h]
    · have hu : U-1+1=U := by omega
      nlinarith
  calc
    _ ≤ ∑ t : Cells (firstPaperSmall r c U), ((U+1)*A.val.val t.val.1 t.val.2+U) :=
      Finset.sum_le_sum (fun t _ => recovered_moment_le A.val.val U s t.val)
    _ = (U+1)*(∑ t : Cells (firstPaperSmall r c U),A.val.val t.val.1 t.val.2)+
        Fintype.card (Cells (firstPaperSmall r c U))*U := by
      simp [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ (U+1)*((smallLineCount r U+smallLineCount c U)*(U-1))+
        Fintype.card (Cells (firstPaperSmall r c U))*U :=
      Nat.add_le_add_right (Nat.mul_le_mul_left (U+1) hs) _
    _ = (smallLineCount r U+smallLineCount c U)*((U+1)*(U-1))+
        Fintype.card (Cells (firstPaperSmall r c U))*U := by ring
    _ ≤ _ := Nat.add_le_add_right
      (Nat.mul_le_mul_left (smallLineCount r U+smallLineCount c U) hU) _

omit [DecidableEq J] in
/-- Each selected residual entry is below the ORIGINAL incident small margin. -/
theorem residual_selected_entry_lt (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (U : ℕ)
    (A : ResidualTables (firstPaperSmall r c U) r c rbar cbar)
    (t : Cells (firstPaperSmall r c U)) : A.val.val t.val.1 t.val.2 < U := by
  have hr : A.val.val t.val.1 t.val.2 ≤ r t.val.1 := by
    apply le_trans _ (A.property.1 t.val.1)
    have h := Finset.single_le_sum
      (f := fun j => if firstPaperSmall r c U t.val.1 j then A.val.val t.val.1 j else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t.val.2)
    simpa [smallRow,t.property] using h
  have hc : A.val.val t.val.1 t.val.2 ≤ c t.val.2 := by
    apply le_trans _ (A.property.2 t.val.2)
    have h := Finset.single_le_sum
      (f := fun i => if firstPaperSmall r c U i t.val.2 then A.val.val i t.val.2 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t.val.1)
    simpa [smallColumnView,t.property] using h
  have hs : r t.val.1 < U ∨ c t.val.2 < U := by
    simpa only [firstPaperSmall,decide_eq_true_eq] using t.property
  rcases hs with hs | hs
  · exact hr.trans_lt hs
  · exact hc.trans_lt hs

lemma residual_recovered_donor_le (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (U : ℕ)
    (A : ResidualTables (firstPaperSmall r c U) r c rbar cbar)
    (s : I×J) (t : Cells (firstPaperSmall r c U)) : recoveredDonor A.val.val s t.val ≤ U := by
  have h := residual_selected_entry_lt r c rbar cbar U A t
  unfold recoveredDonor
  split_ifs <;> omega

/-- Natural truncation equals the literal real moment on an actual table. -/
lemma residual_recovered_moment_cast (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (U : ℕ)
    (A : ResidualTables (firstPaperSmall r c U) r c rbar cbar)
    (s : I×J) (t : Cells (firstPaperSmall r c U)) :
    ((recoveredDonor A.val.val s t.val*(U+1-recoveredDonor A.val.val s t.val) : ℕ) : ℝ) =
      (recoveredDonor A.val.val s t.val : ℝ)*((U : ℝ)+1-(recoveredDonor A.val.val s t.val : ℝ)) := by
  have h := residual_recovered_donor_le r c rbar cbar U A s t
  rw [Nat.cast_mul,Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]

/-- Exact real moments on ANY donor subset, including the different-row
feasible repair image. No padded-row budget or image-weight ratio is assumed. -/
theorem residual_recovered_moment_subset_le (r : I → ℕ) (c : J → ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (U : ℕ)
    (A : ResidualTables (firstPaperSmall r c U) r c rbar cbar)
    (s : I×J) (D : Finset (Cells (firstPaperSmall r c U))) :
    (∑ t ∈ D, (recoveredDonor A.val.val s t.val : ℝ)*
      ((U : ℝ)+1-(recoveredDonor A.val.val s t.val : ℝ))) ≤
      (((smallLineCount r U+smallLineCount c U)*U^2+
        Fintype.card (Cells (firstPaperSmall r c U))*U : ℕ) : ℝ) := by
  have hsub : (∑ t ∈ D, recoveredDonor A.val.val s t.val*(U+1-recoveredDonor A.val.val s t.val)) ≤
      ∑ t : Cells (firstPaperSmall r c U),
        recoveredDonor A.val.val s t.val*(U+1-recoveredDonor A.val.val s t.val) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D) (by intros; omega)
  have hnat := hsub.trans (residual_recovered_moment_sum_le r c rbar cbar U A s)
  calc
    _ = ∑ t ∈ D, ((recoveredDonor A.val.val s t.val*(U+1-recoveredDonor A.val.val s t.val) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (residual_recovered_moment_cast r c rbar cbar U A s t).symm
    _ ≤ _ := by exact_mod_cast hnat

end
end Research.ResidualSelectedBudget
