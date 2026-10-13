import Research.RetainedRootShifts
import Math115.RetainedRoot

namespace OAI.ContingencyTables.IntegerWeightedTransport
open scoped BigOperators Classical
open BalancedFamily BalancedEnumeration IntegerMarginal BalancedBox IntegerBoxTruncation

/-- The literal natural multiplier at the unique excess suffix pair. -/
def excessMoment : (Ms : List ℕ) → ExcessAssignments Ms → ℕ
  | [], a => Empty.elim a
  | U :: _, .inl a => a.2.val * (U + 1 - a.2.val)
  | _ :: Ms, .inr a => excessMoment Ms a.1

/-- Exact expansion of the actual correction kernel, with one distinguished
excess suffix pair and all other suffix pairs ordinary. -/
theorem correctionKernel_eq_excess_moment_sum {I : Type*} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) :
    correctionKernel Ms F z =
      ∑ a : ExcessAssignments Ms, (excessMoment Ms a : ℝ) * F (excessEmbedding Ms z a) := by
  induction Ms with
  | nil => simp only [correctionKernel, ExcessAssignments, Finset.univ_eq_empty, Finset.sum_empty]
  | cons U Ms ih =>
    change weightedFuture (exposedFamily Ms F) (U+1) z +
      correctionKernel Ms (marginal F U) z =
      ∑ a : (Assignments Ms × Fin (U+2)) ⊕ (ExcessAssignments Ms × Fin (U+1)),
        (excessMoment (U::Ms) a : ℝ) * F (excessEmbedding (U::Ms) z a)
    rw [Fintype.sum_sum_type]
    congr 1
    · unfold weightedFuture exposedFamily
      simp_rw [eliminate_eq_sum, expose_embedding, Finset.mul_sum]
      rw [Finset.sum_comm, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Fin.sum_univ_eq_sum_range _ (U+2)]
      apply Finset.sum_congr rfl
      intro j _
      have hj : j.val ≤ U+1 := by omega
      simp only [excessMoment, excessEmbedding, Nat.cast_mul, Nat.cast_sub hj,
        Nat.cast_add, Nat.cast_one]
    · rw [ih, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      unfold marginal
      rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range _ (U+1)]
      rfl

lemma excessMoment_eq_zero_of_not_valid (Ms : List ℕ) (a : ExcessAssignments Ms)
    (ha : ¬ ValidExcess Ms a) : excessMoment Ms a = 0 := by
  induction Ms with
  | nil => exact Empty.elim a
  | cons U Ms ih =>
    cases a with
    | inl a =>
      change ¬ (0 < a.2.val ∧ a.2.val ≤ U) at ha
      have hbound := a.2.isLt
      have hj : a.2.val = 0 ∨ a.2.val = U+1 := by omega
      rcases hj with hj | hj <;> simp [excessMoment, hj]
    | inr a => exact ih a.1 ha

/-- Box truncation discards only zero-moment exceptional endpoints. -/
theorem correctionKernel_truncate_eq_valid_moment_sum {I : Type*} [Fintype I]
    (Ms : List ℕ) (F : (Coordinates I Ms → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ)
    (hz : InBox m z) (htotal : (∑ i, z i)+1=R) :
    correctionKernel Ms (truncate F (bounds m Ms) (R+Ms.sum)) z =
      ∑ a ∈ Finset.univ.filter (ValidExcess Ms),
        (excessMoment Ms a : ℝ) * F (excessEmbedding Ms z a) := by
  rw [correctionKernel_eq_excess_moment_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  have ht : (∑ i, excessEmbedding Ms z a i)=R+Ms.sum := by
    rw [excessEmbedding_total]
    omega
  simp only [truncate, ht, excessEmbedding_inBox_iff Ms m z hz a, and_true]
  by_cases ha : ValidExcess Ms a <;> simp [ha]

/-- Exact integer maximum, including both zero-moment endpoints. -/
lemma pair_product_nat_le_quarter (M a : ℕ) (ha : a ≤ M) :
    a * (M-a) ≤ M^2/4 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr
  have h := Math115.pair_product_le_quarter_square (a : ℝ) (M : ℝ)
  have hc : ((a * (M-a) * 4 : ℕ) : ℝ) ≤ ((M^2 : ℕ) : ℝ) := by
    push_cast
    rw [Nat.cast_sub ha]
    nlinarith
  exact_mod_cast hc

lemma excessMoment_le_quarter (Ms : List ℕ) (W : ℕ)
    (hwidth : ∀ U ∈ Ms, U ≤ W) (a : ExcessAssignments Ms) :
    excessMoment Ms a ≤ Math115.RetainedRoot.quarterProduct W := by
  induction Ms with
  | nil => exact Empty.elim a
  | cons U Ms ih =>
    cases a with
    | inl a =>
      apply (pair_product_nat_le_quarter (U+1) a.2.val (by have := a.2.isLt; omega)).trans
      apply Nat.div_le_div_right
      have hU : U ≤ W := hwidth U (by simp)
      nlinarith
    | inr a => exact ih (fun V hV => hwidth V (by simp [hV])) a.1

/-- Actual-kernel domination follows term by term from its exact moment sum;
this theorem never replaces the kernel in a retained negative stencil entry. -/
theorem correctionKernel_le_quarter_auxiliary {I : Type*} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (W : ℕ)
    (hwidth : ∀ U ∈ Ms, U ≤ W) (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) :
    correctionKernel Ms F z ≤ (Math115.RetainedRoot.quarterProduct W : ℝ) *
      auxiliaryKernel Ms F z := by
  rw [correctionKernel_eq_excess_moment_sum, auxiliaryKernel_eq_excess_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_right _ (hF _)
  exact_mod_cast excessMoment_le_quarter Ms W hwidth a


end OAI.ContingencyTables.IntegerWeightedTransport

namespace Math115.RetainedPhysicalCap
open OAI.ContingencyTables
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles
open ExcessContextProfiles FirstPaperPhysicalMarginal FirstPaperContextTransport
open PaddedCompletions CompletionCounts IntegerBoxTruncation

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Exact same-box physical moment sum. The deficient root and excess suffix
have total U+Ms.sum, and removed exceptional endpoints have multiplier zero. -/
theorem physical_correction_eq_moment_sum
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    {n : ℕ} (e : Fin n ≃ Later small s) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let g := truncate f (bounds (fun _ : Bool => U) Ms) (U+Ms.sum)
    correctionKernel Ms g (auxRoot U l) =
      ∑ a : ExcessAssignments Ms,
        (excessMoment Ms a : ℝ) * f (excessEmbedding Ms (auxRoot U l) a) := by
  dsimp only
  rw [correctionKernel_truncate_eq_valid_moment_sum _ _ _ _ _
    (auxRoot_inBox U l hlU) (by
      simp only [auxRoot, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
      omega), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : ValidExcess _ a
  · simp [ha]
  · simp [ha, excessMoment_eq_zero_of_not_valid _ a ha]

/-- Every value of one fixed boxed correction kernel is nonnegative, including
exterior positive-support stencil entries; no repair cap is assumed there. -/
theorem physical_correction_nonnegative
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) (z : Bool → ℕ) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let g := truncate f (bounds (fun _ : Bool => U) Ms) (U+Ms.sum)
    0 ≤ correctionKernel Ms g z := by
  dsimp only
  apply correctionKernel_nonnegative
  exact truncate_nonnegative _ _ _ (contextHard_nonnegative small B r c L _ _ _)

/-- The actual fixed boxed correction has the integer quarter-product cap,
conditional only on the existing uniform-capacity and ordinary-completion
repair premises. No desired correction-cap hypothesis is introduced. -/
theorem physical_correction_le_adjacent
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let g := truncate f (bounds (fun _ : Bool => U) Ms) (U+Ms.sum)
    correctionKernel Ms g (auxRoot U l) ≤
      (n : ℝ)*(Math115.RetainedRoot.quarterProduct U : ℝ)*
      max (eliminate Ms f (childProfile U (l-1))) (eliminate Ms f (childProfile U l)) := by
  dsimp only
  let Ms := widths (fun _ : Fin n => U)
  let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
  let g := truncate f (bounds (fun _ : Bool => U) Ms) (U+Ms.sum)
  have hg : ∀ x, 0 ≤ g x :=
    truncate_nonnegative f (bounds (fun _ : Bool => U) Ms) (U+Ms.sum)
      (contextHard_nonnegative small B r c L Ms (contextEquiv small s hs e U)
        (prefixRaw small s σ U))
  have hcor := correctionKernel_le_quarter_auxiliary Ms g U
    (fun w hw => le_of_eq (widths_constant_mem U w hw)) hg (auxRoot U l)
  have haux := auxiliary_mass_le_adjacent small B r c L s hs σ U l hl0 hlU hB hσ e hcap
  dsimp only at haux
  apply hcor.trans
  calc
    _ ≤ (Math115.RetainedRoot.quarterProduct U : ℝ)*
      ((n : ℝ)*max (eliminate _ _ (childProfile U (l-1)))
        (eliminate _ _ (childProfile U l))) :=
      mul_le_mul_of_nonneg_left haux (Nat.cast_nonneg _)
    _ = _ := by ring

end Math115.RetainedPhysicalCap

#print axioms OAI.ContingencyTables.IntegerWeightedTransport.correctionKernel_eq_excess_moment_sum
#print axioms OAI.ContingencyTables.IntegerWeightedTransport.correctionKernel_truncate_eq_valid_moment_sum
#print axioms Math115.RetainedPhysicalCap.physical_correction_eq_moment_sum
#print axioms Math115.RetainedPhysicalCap.physical_correction_nonnegative
#print axioms Math115.RetainedPhysicalCap.physical_correction_le_adjacent
