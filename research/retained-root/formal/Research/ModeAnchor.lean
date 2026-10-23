import Math115.PathVariance
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Research.ModeAnchor

open scoped BigOperators Classical
open OAI.ContingencyTables.FiniteExposureVariance


lemma telescope (h : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ l ∈ Finset.Icc (a+1) b, (h l-h (l-1)))=h b-h a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Icc_succ_top (by omega : a+1 ≤ b+1)]
    rw [ih]
    simp only [Nat.add_sub_cancel]
    ring

lemma path_resistance_bound (h Xi E : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hXi : ∀ l ∈ Finset.Icc (a+1) b, 0 ≤ Xi l)
    (hE : ∀ l ∈ Finset.Icc (a+1) b, 0 ≤ E l)
    (hedge : ∀ l ∈ Finset.Icc (a+1) b, (h l-h (l-1))^2 ≤ Xi l*E l) :
    (h b-h a)^2 ≤ (∑ l ∈ Finset.Icc (a+1) b, Xi l)*
      (∑ l ∈ Finset.Icc (a+1) b, E l) := by
  rw [← telescope h a b hab]
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ hXi hE hedge


noncomputable def leftBudget (z Xi : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 m, (∑ i ∈ Finset.range l, z i)*Xi l

noncomputable def rightBudget (z Xi : ℕ → ℝ) (m N : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc (m+1) N, (∑ i ∈ Finset.Icc l N, z i)*Xi l

lemma left_resistance_sum_eq_prefix (z Xi : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, z i*(∑ l ∈ Finset.Icc (i+1) m, Xi l))=
      leftBudget z Xi m := by
  have hinterval (i : ℕ) (hi : i ∈ Finset.range m) :
      Finset.Icc (i+1) m=(Finset.Icc 1 m).filter (fun l => i < l) := by
    ext l
    simp only [Finset.mem_Icc,Finset.mem_filter]
    omega
  have hprefix (l : ℕ) (hl : l ∈ Finset.Icc 1 m) :
      Finset.range l=(Finset.range m).filter (fun i => i < l) := by
    ext i
    simp only [Finset.mem_range,Finset.mem_filter]
    have := Finset.mem_Icc.mp hl
    omega
  unfold leftBudget
  have he : (∑ i ∈ Finset.range m, z i*(∑ l ∈ Finset.Icc (i+1) m, Xi l)) =
      ∑ i ∈ Finset.range m, ∑ l ∈ Finset.Icc 1 m, if i < l then z i*Xi l else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,hinterval i hi,Finset.sum_filter]
  rw [he,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [hprefix l hl,Finset.sum_filter,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma right_resistance_sum_eq_suffix (z Xi : ℕ → ℝ) (m N : ℕ) :
    (∑ i ∈ Finset.Icc (m+1) N, z i*(∑ l ∈ Finset.Icc (m+1) i, Xi l))=
      rightBudget z Xi m N := by
  have hinterval (i : ℕ) (hi : i ∈ Finset.Icc (m+1) N) :
      Finset.Icc (m+1) i=(Finset.Icc (m+1) N).filter (fun l => l ≤ i) := by
    ext l
    simp only [Finset.mem_Icc,Finset.mem_filter]
    have := Finset.mem_Icc.mp hi
    omega
  have hsuffix (l : ℕ) (hl : l ∈ Finset.Icc (m+1) N) :
      Finset.Icc l N=(Finset.Icc (m+1) N).filter (fun i => l ≤ i) := by
    ext i
    simp only [Finset.mem_Icc,Finset.mem_filter]
    have := Finset.mem_Icc.mp hl
    omega
  unfold rightBudget
  have he : (∑ i ∈ Finset.Icc (m+1) N, z i*(∑ l ∈ Finset.Icc (m+1) i, Xi l)) =
      ∑ i ∈ Finset.Icc (m+1) N, ∑ l ∈ Finset.Icc (m+1) N, if l ≤ i then z i*Xi l else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,hinterval i hi,Finset.sum_filter]
  rw [he,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [hsuffix l hl,Finset.sum_filter,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma left_centered_bound (z h Xi E : ℕ → ℝ) (N m : ℕ) (hm : m ≤ N)
    (hz : ∀ i ≤ N, 0 ≤ z i)
    (hXi : ∀ l ∈ Finset.Icc 1 N, 0 ≤ Xi l)
    (hE : ∀ l ∈ Finset.Icc 1 N, 0 ≤ E l)
    (hedge : ∀ l ∈ Finset.Icc 1 N, (h l-h (l-1))^2 ≤ Xi l*E l) :
    (∑ i ∈ Finset.range m, z i*(h i-h m)^2) ≤
      leftBudget z Xi m*(∑ l ∈ Finset.Icc 1 m, E l) := by
  have hsub : Finset.Icc 1 m ⊆ Finset.Icc 1 N := by
    intro l hl
    obtain ⟨hl1,hlm⟩ := Finset.mem_Icc.mp hl
    exact Finset.mem_Icc.mpr ⟨hl1,hlm.trans hm⟩
  have hpoint (i : ℕ) (hi : i ∈ Finset.range m) :
      z i*(h i-h m)^2 ≤
        (z i*(∑ l ∈ Finset.Icc (i+1) m, Xi l))*(∑ l ∈ Finset.Icc 1 m, E l) := by
    have him := Finset.mem_range.mp hi
    have hs : Finset.Icc (i+1) m ⊆ Finset.Icc 1 m := by
      intro l hl
      obtain ⟨hl1,hlm⟩ := Finset.mem_Icc.mp hl
      exact Finset.mem_Icc.mpr ⟨by omega,hlm⟩
    have hp := path_resistance_bound h Xi E i m (by omega)
      (fun l hl => hXi l (hsub (hs hl))) (fun l hl => hE l (hsub (hs hl)))
      (fun l hl => hedge l (hsub (hs hl)))
    have he : (∑ l ∈ Finset.Icc (i+1) m, E l) ≤ ∑ l ∈ Finset.Icc 1 m, E l :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun l hl _ => hE l (hsub hl))
    have hx : 0 ≤ ∑ l ∈ Finset.Icc (i+1) m, Xi l :=
      Finset.sum_nonneg (fun l hl => hXi l (hsub (hs hl)))
    have hswap : (h i-h m)^2=(h m-h i)^2 := by ring
    rw [hswap]
    calc
      _ ≤ z i*((∑ l ∈ Finset.Icc (i+1) m, Xi l)*
          (∑ l ∈ Finset.Icc (i+1) m, E l)) :=
        mul_le_mul_of_nonneg_left hp (hz i (by omega))
      _ ≤ z i*((∑ l ∈ Finset.Icc (i+1) m, Xi l)*
          (∑ l ∈ Finset.Icc 1 m, E l)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hx) (hz i (by omega))
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ Finset.range m, (z i*(∑ l ∈ Finset.Icc (i+1) m, Xi l))*
        (∑ l ∈ Finset.Icc 1 m, E l) := Finset.sum_le_sum hpoint
    _ = _ := by rw [← Finset.sum_mul,left_resistance_sum_eq_prefix]

lemma right_centered_bound (z h Xi E : ℕ → ℝ) (N m : ℕ) (_hm : m ≤ N)
    (hz : ∀ i ≤ N, 0 ≤ z i)
    (hXi : ∀ l ∈ Finset.Icc 1 N, 0 ≤ Xi l)
    (hE : ∀ l ∈ Finset.Icc 1 N, 0 ≤ E l)
    (hedge : ∀ l ∈ Finset.Icc 1 N, (h l-h (l-1))^2 ≤ Xi l*E l) :
    (∑ i ∈ Finset.Icc (m+1) N, z i*(h i-h m)^2) ≤
      rightBudget z Xi m N*(∑ l ∈ Finset.Icc (m+1) N, E l) := by
  have hsub : Finset.Icc (m+1) N ⊆ Finset.Icc 1 N := by
    intro l hl
    obtain ⟨hl1,hlN⟩ := Finset.mem_Icc.mp hl
    exact Finset.mem_Icc.mpr ⟨by omega,hlN⟩
  have hpoint (i : ℕ) (hi : i ∈ Finset.Icc (m+1) N) :
      z i*(h i-h m)^2 ≤
        (z i*(∑ l ∈ Finset.Icc (m+1) i, Xi l))*(∑ l ∈ Finset.Icc (m+1) N, E l) := by
    obtain ⟨hmi,hiN⟩ := Finset.mem_Icc.mp hi
    have hs : Finset.Icc (m+1) i ⊆ Finset.Icc (m+1) N := by
      intro l hl
      obtain ⟨hl1,hli⟩ := Finset.mem_Icc.mp hl
      exact Finset.mem_Icc.mpr ⟨hl1,hli.trans hiN⟩
    have hp := path_resistance_bound h Xi E m i (by omega)
      (fun l hl => hXi l (hsub (hs hl))) (fun l hl => hE l (hsub (hs hl)))
      (fun l hl => hedge l (hsub (hs hl)))
    have he : (∑ l ∈ Finset.Icc (m+1) i, E l) ≤ ∑ l ∈ Finset.Icc (m+1) N, E l :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun l hl _ => hE l (hsub hl))
    have hx : 0 ≤ ∑ l ∈ Finset.Icc (m+1) i, Xi l :=
      Finset.sum_nonneg (fun l hl => hXi l (hsub (hs hl)))
    calc
      _ ≤ z i*((∑ l ∈ Finset.Icc (m+1) i, Xi l)*
          (∑ l ∈ Finset.Icc (m+1) i, E l)) := mul_le_mul_of_nonneg_left hp (hz i hiN)
      _ ≤ z i*((∑ l ∈ Finset.Icc (m+1) i, Xi l)*
          (∑ l ∈ Finset.Icc (m+1) N, E l)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hx) (hz i hiN)
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ Finset.Icc (m+1) N, (z i*(∑ l ∈ Finset.Icc (m+1) i, Xi l))*
        (∑ l ∈ Finset.Icc (m+1) N, E l) := Finset.sum_le_sum hpoint
    _ = _ := by rw [← Finset.sum_mul,right_resistance_sum_eq_suffix]


/-- An arbitrary anchor divides the edge energy into disjoint left and right
parts. Nonnegative weights suffice once the two prefix-resistance caps are
known. In particular, positive unimodal weights can use a mode as anchor. -/
theorem mode_anchor_variance_bound (z h Xi E : ℕ → ℝ) (N m : ℕ) (ΓL ΓR : ℝ)
    (hm : m ≤ N) (hz : ∀ i ≤ N, 0 ≤ z i)
    (hXi : ∀ l ∈ Finset.Icc 1 N, 0 ≤ Xi l)
    (hE : ∀ l ∈ Finset.Icc 1 N, 0 ≤ E l)
    (hedge : ∀ l ∈ Finset.Icc 1 N, (h l-h (l-1))^2 ≤ Xi l*E l)
    (hleft : leftBudget z Xi m ≤ ΓL) (hright : rightBudget z Xi m N ≤ ΓR) :
    variance (fun i : Fin (N+1) => z i.val) (fun i => h i.val) ≤
      max ΓL ΓR*(∑ l ∈ Finset.Icc 1 N, E l) := by
  have hcenter := variance_le_center (fun i : Fin (N+1) => z i.val) (fun i => h i.val)
    (fun i => hz i.val (by omega)) (h m)
  rw [Fin.sum_univ_eq_sum_range (fun i => z i*(h i-h m)^2) (N+1)] at hcenter
  have hvertices : Finset.range (N+1)=Finset.range (m+1) ∪ Finset.Icc (m+1) N := by
    ext i
    simp only [Finset.mem_range,Finset.mem_union,Finset.mem_Icc]
    omega
  have hdv : Disjoint (Finset.range (m+1)) (Finset.Icc (m+1) N) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have := Finset.mem_range.mp hi
    have := Finset.mem_Icc.mp hj
    omega
  rw [hvertices,Finset.sum_union hdv,Finset.sum_range_succ] at hcenter
  simp only [sub_self,zero_pow (by norm_num : 2 ≠ 0),mul_zero,add_zero] at hcenter
  have hL := left_centered_bound z h Xi E N m hm hz hXi hE hedge
  have hR := right_centered_bound z h Xi E N m hm hz hXi hE hedge
  have hEL : 0 ≤ ∑ l ∈ Finset.Icc 1 m, E l := by
    apply Finset.sum_nonneg
    intro l hl
    obtain ⟨hl1,hlm⟩ := Finset.mem_Icc.mp hl
    exact hE l (Finset.mem_Icc.mpr ⟨hl1,hlm.trans hm⟩)
  have hER : 0 ≤ ∑ l ∈ Finset.Icc (m+1) N, E l := by
    apply Finset.sum_nonneg
    intro l hl
    obtain ⟨hl1,hlN⟩ := Finset.mem_Icc.mp hl
    exact hE l (Finset.mem_Icc.mpr ⟨by omega,hlN⟩)
  have hedges : Finset.Icc 1 N=Finset.Icc 1 m ∪ Finset.Icc (m+1) N := by
    ext l
    simp only [Finset.mem_Icc,Finset.mem_union]
    omega
  have hde : Disjoint (Finset.Icc 1 m) (Finset.Icc (m+1) N) := by
    apply Finset.disjoint_left.mpr
    intro l hl hj
    have := Finset.mem_Icc.mp hl
    have := Finset.mem_Icc.mp hj
    omega
  calc
    _ ≤ leftBudget z Xi m*(∑ l ∈ Finset.Icc 1 m, E l)+
        rightBudget z Xi m N*(∑ l ∈ Finset.Icc (m+1) N, E l) :=
      hcenter.trans (add_le_add hL hR)
    _ ≤ max ΓL ΓR*(∑ l ∈ Finset.Icc 1 m, E l)+
        max ΓL ΓR*(∑ l ∈ Finset.Icc (m+1) N, E l) :=
      add_le_add (mul_le_mul_of_nonneg_right (hleft.trans (le_max_left _ _)) hEL)
        (mul_le_mul_of_nonneg_right (hright.trans (le_max_right _ _)) hER)
    _ = _ := by rw [hedges,Finset.sum_union hde,mul_add]

/-- The explicit prefix-resistance coefficient, without assuming a variance
bound or a Poincare inequality. Zero resistances and endpoint anchors work. -/
theorem mode_anchor_variance_exact (z h Xi E : ℕ → ℝ) (N m : ℕ)
    (hm : m ≤ N) (hz : ∀ i ≤ N, 0 ≤ z i)
    (hXi : ∀ l ∈ Finset.Icc 1 N, 0 ≤ Xi l)
    (hE : ∀ l ∈ Finset.Icc 1 N, 0 ≤ E l)
    (hedge : ∀ l ∈ Finset.Icc 1 N, (h l-h (l-1))^2 ≤ Xi l*E l) :
    variance (fun i : Fin (N+1) => z i.val) (fun i => h i.val) ≤
      max (leftBudget z Xi m) (rightBudget z Xi m N)*
        (∑ l ∈ Finset.Icc 1 N, E l) :=
  mode_anchor_variance_bound z h Xi E N m _ _ hm hz hXi hE hedge le_rfl le_rfl


/-- Reversing the finite vertex interval maps a suffix to a prefix exactly. -/
lemma reverse_prefix_sum (z : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N+1) :
    (∑ i ∈ Finset.range k, z (N-i))=∑ i ∈ Finset.Icc (N+1-k) N, z i := by
  apply Finset.sum_bij (fun i _ => N-i)
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    apply Finset.mem_Icc.mpr
    omega
  · intro i hi j hj he
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    omega
  · intro i hi
    obtain ⟨hi0,hiN⟩ := Finset.mem_Icc.mp hi
    refine ⟨N-i,Finset.mem_range.mpr (by omega),?_⟩
    omega
  · intro i hi
    rfl

/-- Exact reversal of the right prefix-resistance budget, preserving its edge
indices, endpoint terms, and fixed weights. -/
lemma rightBudget_eq_reversed_left (z Xi : ℕ → ℝ) (N m : ℕ) (hm : m ≤ N) :
    rightBudget z Xi m N=
      leftBudget (fun i => z (N-i)) (fun l => Xi (N-l+1)) (N-m) := by
  unfold rightBudget leftBudget
  apply Finset.sum_bij (fun l _ => N+1-l)
  · intro l hl
    obtain ⟨hml,hlN⟩ := Finset.mem_Icc.mp hl
    apply Finset.mem_Icc.mpr
    omega
  · intro l hl k hk he
    have hl' := Finset.mem_Icc.mp hl
    have hk' := Finset.mem_Icc.mp hk
    omega
  · intro k hk
    obtain ⟨hk1,hkN⟩ := Finset.mem_Icc.mp hk
    refine ⟨N+1-k,Finset.mem_Icc.mpr ?_,?_⟩ <;> omega
  · intro l hl
    obtain ⟨hml,hlN⟩ := Finset.mem_Icc.mp hl
    rw [reverse_prefix_sum z N (N+1-l) (by omega)]
    rw [show N+1-(N+1-l)=l by omega]
    dsimp only
    rw [show N-(N+1-l)+1=l by omega]

end Research.ModeAnchor

#print axioms Research.ModeAnchor.mode_anchor_variance_bound
#check Research.ModeAnchor.mode_anchor_variance_bound
