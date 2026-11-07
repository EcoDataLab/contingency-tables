import Research.CompletedRepairMoment
import Research.RetainedPhysicalCap

namespace Math115.AggregateCorrectionCap
open OAI.ContingencyTables
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles
open ExcessContextProfiles FirstPaperPhysicalMarginal FirstPaperContextTransport
open PaddedCompletions CompletionCounts IntegerBoxTruncation
open Math115.CompletedRepairInjection Math115.RetainedPhysicalCap
open Research.ResidualSelectedBudget

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

lemma excessMoment_eq_index_moment (U : ℕ) {n : ℕ} (z : Bool → ℕ)
    (q : ExcessAssignments (widths (fun _ : Fin n => U))) :
    let x := excessEmbedding (widths (fun _ : Fin n => U)) z q
      ((coordinateEquiv Bool (fun _ : Fin n => U)).symm
        (.inr (excessIndex (fun _ : Fin n => U) q,false)))
    excessMoment (widths (fun _ : Fin n => U)) q=x*(U+1-x) := by
  induction n with
  | zero => exact Empty.elim q
  | succ n ih =>
    cases q with
    | inl q => rfl
    | inr q => exact ih q.1

omit [Fintype I] [Fintype J] in
lemma excessMoment_eq_physical_donor
    (small : I → J → Bool) (B : I → J → ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl0 : 1≤l) (hlU : l≤U)
    (hB : ∀ i j,small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s,σ a.val.val≤U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U))) (hq : ValidExcess _ q) :
    (excessMoment (widths (fun _ : Fin n => U)) q:ℝ)=
      donorMoment U (smallView small (naturalProfile
        (excessDefectProfile small B s hs σ U l hl0 hlU hB hσ e q hq).val) false
        (e (excessIndex (fun _ : Fin n => U) q)).val.val.1
        (e (excessIndex (fun _ : Fin n => U) q)).val.val.2) := by
  let t := e (excessIndex (fun _ : Fin n => U) q)
  have hd : smallView small (naturalProfile
      (excessDefectProfile small B s hs σ U l hl0 hlU hB hσ e q hq).val) false
      t.val.val.1 t.val.val.2 =
      excessEmbedding (widths (fun _ : Fin n => U)) (auxRoot U l) q
        ((coordinateEquiv Bool (fun _ : Fin n => U)).symm
          (.inr (excessIndex (fun _ : Fin n => U) q,false))) := by
    simp only [excessDefectProfile,naturalProfile_boundedExcess,smallView,t.val.property,dite_eq_left]
    exact assemble_later small s hs σ U e _ (excessIndex (fun _ : Fin n => U) q) false
  have hb := rawExcess_bounded small s hs σ U l hlU hσ e q hq (t.val,false)
  have hraw : rawExcess small s hs σ U l e q (t.val,false)=
      smallView small (naturalProfile
        (excessDefectProfile small B s hs σ U l hl0 hlU hB hσ e q hq).val) false
        t.val.val.1 t.val.val.2 := by
    simp only [excessDefectProfile,naturalProfile_boundedExcess,smallView,t.val.property,dite_eq_left]
  rw [hraw,hd] at hb
  rw [excessMoment_eq_index_moment U (auxRoot U l) q, Nat.cast_mul,Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]
  dsimp only [donorMoment]
  rw [hd]


lemma donorMoment_nonnegative {U x : ℕ} (hx : x≤U) : 0≤donorMoment U x := by
  have hc : (x:ℝ)≤(U:ℝ) := by exact_mod_cast hx
  unfold donorMoment
  exact mul_nonneg (Nat.cast_nonneg _) (by linarith)

/-- The actual correction kernel is bounded by all literal fixed-label
physical donor moments. Its unique suffix excess label is retained. -/
theorem physical_correction_le_defect_moment_sum
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl0 : 1≤l) (hlU : l≤U)
    (hB : ∀ i j,small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s,σ a.val.val≤U) {n : ℕ} (e : Fin n ≃ Later small s) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    correctionKernel Ms (truncate f (bounds (fun _ : Bool => U) Ms) (U+Ms.sum)) (auxRoot U l) ≤
      ∑ t : Later small s, ∑ z : DefectProfiles small B s t.val.val σ l,
        donorMoment U (smallView small (naturalProfile z.val) false t.val.val.1 t.val.val.2)*
          hardMarginal small B r c L (naturalProfile z.val) := by
  dsimp only
  rw [correctionKernel_truncate_eq_valid_moment_sum _ _ _ _ _ (auxRoot_inBox U l hlU) (by
    simp only [auxRoot,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
    omega)]
  rw [Finset.sum_subtype (p:=ValidExcess (widths (fun _ : Fin n => U))) _ (by simp)]
  let j : ValidAssignments U n → (t : Later small s) × DefectProfiles small B s t.val.val σ l :=
    fun q => ⟨e (excessIndex (fun _ : Fin n => U) q.val),
      excessDefectProfile small B s hs σ U l hl0 hlU hB hσ e q.val q.property⟩
  have hj : Function.Injective j := by
    intro q q' he
    apply Subtype.ext
    apply rawExcess_injective small s hs σ U l e
    exact congrArg (fun a : (t : Later small s) × DefectProfiles small B s t.val.val σ l =>
      naturalProfile a.2.val) he
  let g : ((t : Later small s) × DefectProfiles small B s t.val.val σ l) → ℝ :=
    fun a => donorMoment U (smallView small (naturalProfile a.2.val) false a.1.val.val.1 a.1.val.val.2)*
      hardMarginal small B r c L (naturalProfile a.2.val)
  have hg (a : (t : Later small s) × DefectProfiles small B s t.val.val σ l) : 0≤g a := by
    have hw : 0≤hardMarginal small B r c L (naturalProfile a.2.val) := by
      rw [hardMarginal_eq_fibre_card small B r c L _ (naturalProfile_bounded a.2.val)]
      positivity
    apply mul_nonneg _ hw
    apply donorMoment_nonnegative
    have h := naturalProfile_bounded a.2.val (a.1.val,false)
    rw [hB _ _ a.1.val.property] at h
    simpa only [smallView,a.1.val.property,dite_eq_left] using h
  have hh := finite_injective_sum_le j hj g hg
  rw [Fintype.sum_sigma] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro q _
  rw [excessMoment_eq_physical_donor small B s hs σ U l hl0 hlU hB hσ e q.val q.property]
  rfl

lemma split_partition_sum {T R L : Type*} [Fintype T] [Fintype R] [Fintype L]
    (P : T → Prop) [DecidablePred P] (FR : R → T → ℝ) (FL : L → T → ℝ) :
    (∑ t,if P t then ∑ A,FR A t else ∑ A,FL A t)=
      (∑ A,∑ t,if P t then FR A t else 0)+(∑ A,∑ t,if P t then 0 else FL A t) := by
  calc
    _ = ∑ t,((∑ A,if P t then FR A t else 0)+(∑ A,if P t then 0 else FL A t)) := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : P t <;> simp [ht]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1 <;> rw [Finset.sum_comm]

lemma later_moment_sum_le (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (rbar : I → ℕ) (cbar : J → ℕ) (s : I×J)
    (A : ResidualTables (firstPaperSmall r c U) r c rbar cbar) :
    (∑ t : Later (firstPaperSmall r c U) s,
      donorMoment U (recoveredDonor A.val.val s t.val.val))≤
      (((smallLineCount r U+smallLineCount c U)*U^2+
        Fintype.card (Cells (firstPaperSmall r c U))*U:ℕ):ℝ) := by
  calc
    _ ≤ ∑ t : Cells (firstPaperSmall r c U),donorMoment U (recoveredDonor A.val.val s t.val) := by
      apply finite_injective_sum_le (fun t : Later (firstPaperSmall r c U) s => t.val)
        (fun _ _ he => Subtype.ext he)
        (fun t => donorMoment U (recoveredDonor A.val.val s t.val))
      intro t
      exact donorMoment_nonnegative (residual_recovered_donor_le r c rbar cbar U A s t)
    _ ≤ _ := by
      simpa only [donorMoment] using
        residual_recovered_moment_subset_le r c rbar cbar U A s Finset.univ

set_option maxHeartbeats 800000 in
/-- All fixed-label repaired images are grouped by their actual full table.
Both child groups use the same original-margin donor budget. -/
theorem physical_defect_moment_sum_le_two_children
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (l : ℕ) (hl0 : 1≤l)
    (hs : firstPaperSmall r c U s.1 s.2=true) :
    let small := firstPaperSmall r c U
    let rbar := fun i => r i+rowLargeCount small i*L
    let cbar := fun j => c j+columnLargeCount small j*L
    let K : ℝ := (((smallLineCount r U+smallLineCount c U)*U^2+Fintype.card (Cells small)*U:ℕ):ℝ)
    (∑ t : Later small s,∑ z : DefectProfiles small B s t.val.val σ l,
      donorMoment U (smallView small (naturalProfile z.val) false t.val.val.1 t.val.val.2)*
        hardMarginal small B r c L (naturalProfile z.val))≤
      K*((Fintype.card (SmallResidualChild small r rbar c cbar s σ (l-1)):ℝ)+
        (Fintype.card (SmallResidualChild small r rbar c cbar s σ l):ℝ)) := by
  dsimp only
  let small := firstPaperSmall r c U
  let rbar := fun i => r i+rowLargeCount small i*L
  let cbar := fun j => c j+columnLargeCount small j*L
  let ChildL := SmallResidualChild small r rbar c cbar s σ (l-1)
  let ChildR := SmallResidualChild small r rbar c cbar s σ l
  let K : ℝ := (((smallLineCount r U+smallLineCount c U)*U^2+Fintype.card (Cells small)*U:ℕ):ℝ)
  let μ (A : ResidualTables small r c rbar cbar) (t : Later small s) :=
    donorMoment U (recoveredDonor A.val.val s t.val.val)
  have hμ (A : ResidualTables small r c rbar cbar) (t : Later small s) : 0≤μ A t :=
    donorMoment_nonnegative (residual_recovered_donor_le r c rbar cbar U A s t.val)
  have hbudget (A : ResidualTables small r c rbar cbar) : (∑ t : Later small s,μ A t)≤K :=
    later_moment_sum_le r c U rbar cbar s A
  have ht (t : Later small s) :
      (∑ z : DefectProfiles small B s t.val.val σ l,
        donorMoment U (smallView small (naturalProfile z.val) false t.val.val.1 t.val.val.2)*
          hardMarginal small B r c L (naturalProfile z.val))≤
      if t.val.val.1=s.1 then (∑ A : ChildR,μ A.val t) else (∑ A : ChildL,μ A.val t) := by
    have hb := physical_hard_donor_moment_le_child r c U L B s t.val.val σ l hs
      t.val.property t.property
    by_cases hr : t.val.val.1=s.1
    · have hk : l-1+(if t.val.val.1=s.1 then 1 else 0)=l := by simp only [hr,ite_true]; omega
      rw [hk] at hb
      simpa only [hr,ite_true,μ,recoveredDonor] using hb
    · have hk : l-1+(if t.val.val.1=s.1 then 1 else 0)=l-1 := by simp only [hr,ite_false,Nat.add_zero]
      rw [hk] at hb
      simpa only [hr,ite_false,μ,recoveredDonor] using hb
  calc
    _ ≤ ∑ t : Later small s,
      if t.val.val.1=s.1 then (∑ A : ChildR,μ A.val t) else (∑ A : ChildL,μ A.val t) :=
      Finset.sum_le_sum (fun t _ => ht t)
    _ = (∑ A : ChildR,∑ t : Later small s,if t.val.val.1=s.1 then μ A.val t else 0)+
        (∑ A : ChildL,∑ t : Later small s,if t.val.val.1=s.1 then 0 else μ A.val t) :=
      split_partition_sum (T:=Later small s) (R:=ChildR) (L:=ChildL)
        (fun t => t.val.val.1=s.1) (fun A t => μ A.val t) (fun A t => μ A.val t)
    _ ≤ (∑ _A : ChildR,K)+(∑ _A : ChildL,K) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro A _
        apply le_trans _ (hbudget A.val)
        apply Finset.sum_le_sum
        intro t _
        split_ifs <;> first | exact le_rfl | exact hμ A.val t
      · apply Finset.sum_le_sum
        intro A _
        apply le_trans _ (hbudget A.val)
        apply Finset.sum_le_sum
        intro t _
        split_ifs <;> first | exact le_rfl | exact hμ A.val t
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

/-- Genuine same-box aggregate correction cap at ANY actual selected root.
The source original partial-margin constraints, full completion multiplicities,
and large crossings are all retained. No desired kernel cap is a premise. -/
theorem physical_correction_le_aggregate_adjacent
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (s : I×J) (hs : firstPaperSmall r c U s.1 s.2=true) (σ : I×J → ℕ)
    (l : ℕ) (hl0 : 1≤l) (hlU : l≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hσ : ∀ a : Earlier (firstPaperSmall r c U) s,σ a.val.val≤U)
    {n : ℕ} (e : Fin n ≃ Later (firstPaperSmall r c U) s)
    (hcap : ∀ A : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),
      ∀ i j,A.val.val i j≤B i j) :
    let small := firstPaperSmall r c U
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let K : ℝ := (((smallLineCount r U+smallLineCount c U)*U^2+Fintype.card (Cells small)*U:ℕ):ℝ)
    correctionKernel Ms (truncate f (bounds (fun _ : Bool => U) Ms) (U+Ms.sum)) (auxRoot U l) ≤
      (2*K)*max (eliminate Ms f (childProfile U (l-1))) (eliminate Ms f (childProfile U l)) := by
  dsimp only
  let small := firstPaperSmall r c U
  let K : ℝ := (((smallLineCount r U+smallLineCount c U)*U^2+Fintype.card (Cells small)*U:ℕ):ℝ)
  let f := contextHard small B r c L (widths (fun _ : Fin n => U))
    (contextEquiv small s hs e U) (prefixRaw small s σ U)
  have hkernel := physical_correction_le_defect_moment_sum small B r c L s hs σ U l hl0 hlU hB hσ e
  have htwo := physical_defect_moment_sum_le_two_children r c U L B s σ l hl0 hs
  dsimp only at hkernel htwo
  have hcardL := (eliminate_context_eq_balanced_mass small B r c L s hs σ U hB hσ
    ⟨l-1,Nat.lt_succ_of_le (show l-1≤U by omega)⟩ e).trans
      (balanced_mass_eq_child_card small B r c L s σ (l-1) hs hcap)
  have hcardR := (eliminate_context_eq_balanced_mass small B r c L s hs σ U hB hσ
    ⟨l,Nat.lt_succ_of_le hlU⟩ e).trans
      (balanced_mass_eq_child_card small B r c L s σ l hs hcap)
  dsimp only at hcardL hcardR
  rw [←hcardL,←hcardR] at htwo
  apply (hkernel.trans htwo).trans
  have hK : 0≤K := Nat.cast_nonneg _
  calc
    K*(eliminate _ f (childProfile U (l-1))+eliminate _ f (childProfile U l)) ≤
        K*(max (eliminate _ f (childProfile U (l-1))) (eliminate _ f (childProfile U l))+
          max (eliminate _ f (childProfile U (l-1))) (eliminate _ f (childProfile U l))) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_max_left _ _) (le_max_right _ _)) hK
    _ = _ := by ring

end
end Math115.AggregateCorrectionCap
