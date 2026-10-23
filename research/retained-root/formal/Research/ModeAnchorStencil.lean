import Research.ModeAnchor
import Research.RetainedStencilSum

namespace Research.ModeAnchorStencil

open scoped BigOperators Classical
open OAI.ContingencyTables.FiniteExposureVariance
open Research.ModeAnchor Research.RetainedStencilSum

/-- The full retained stencil reverses with both exterior corrections present.
There is no vanishing-boundary premise. -/
lemma stencil_reverse (z c : ℕ → ℝ) (N l : ℕ) (hl1 : 1 ≤ l) (hlN : l ≤ N) :
    stencil (fun i => z (N-i)) (fun j => c (N+1-j)) l =
      stencil z c (N+1-l) := by
  unfold stencil
  dsimp only
  rw [show N-(l-1)=N+1-l by omega,
    show N-l=(N+1-l)-1 by omega,
    show N+1-(l-1)=(N+1-l)+1 by omega,
    show N+1-(l+1)=(N+1-l)-1 by omega]
  rw [mul_comm (z (N+1-l)) (z (N+1-l-1))]
  ring

/-- Increasing-side prefix cap for the actual five-term retained stencil. -/
lemma left_stencil_budget_bound (z c : ℕ → ℝ) (K : ℝ) (N m : ℕ) (hm : m ≤ N)
    (hz : ∀ i ≤ N, 0 < z i)
    (hmono : ∀ i j, i ≤ j → j ≤ m → z i ≤ z j)
    (hc : ∀ i ≤ N+1, 0 ≤ c i)
    (hcap : ∀ j, 1 ≤ j → j ≤ N → c j ≤ K*max (z (j-1)) (z j)) :
    leftBudget z (stencil z c) m ≤ (m:ℝ)*((m:ℝ)+1)+2*K*(m:ℝ) := by
  exact increasing_stencil_sum_bound z c K m
    (fun i hi => hz i (hi.trans hm)) hmono
    (fun i hi => hc i (by omega)) (fun j hj1 hjm => hcap j hj1 (hjm.trans hm))

/-- The right cap is proved by exact reversal of the same fixed stencil. -/
lemma right_stencil_budget_bound (z c : ℕ → ℝ) (K : ℝ) (N m : ℕ) (hm : m ≤ N)
    (hz : ∀ i ≤ N, 0 < z i)
    (hmono : ∀ i j, m ≤ i → i ≤ j → j ≤ N → z j ≤ z i)
    (hc : ∀ i ≤ N+1, 0 ≤ c i)
    (hcap : ∀ j, 1 ≤ j → j ≤ N → c j ≤ K*max (z (j-1)) (z j)) :
    rightBudget z (stencil z c) m N ≤
      ((N-m:ℕ):ℝ)*(((N-m:ℕ):ℝ)+1)+2*K*((N-m:ℕ):ℝ) := by
  rw [rightBudget_eq_reversed_left z (stencil z c) N m hm]
  have hrev : leftBudget (fun i => z (N-i)) (fun l => stencil z c (N-l+1)) (N-m)=
      leftBudget (fun i => z (N-i))
        (stencil (fun i => z (N-i)) (fun j => c (N+1-j))) (N-m) := by
    unfold leftBudget
    apply Finset.sum_congr rfl
    intro l hl
    obtain ⟨hl1,hlN⟩ := Finset.mem_Icc.mp hl
    dsimp only
    rw [stencil_reverse z c N l hl1 (by omega),show N-l+1=N+1-l by omega]
  rw [hrev]
  apply increasing_stencil_sum_bound
  · intro i hi
    exact hz (N-i) (Nat.sub_le _ _)
  · intro i j hij hj
    apply hmono (N-j) (N-i) <;> omega
  · intro i hi
    exact hc (N+1-i) (Nat.sub_le _ _)
  · intro j hj1 hjN
    have h := hcap (N+1-j) (by omega) (by omega)
    rw [show N-(j-1)=N+1-j by omega,show N-j=(N+1-j)-1 by omega,max_comm]
    exact h

lemma pathCoefficient_mono (K : ℝ) (a N : ℕ) (hK : 0 ≤ K) (ha : a ≤ N) :
    (a:ℝ)*((a:ℝ)+1)+2*K*(a:ℝ) ≤ (N:ℝ)*((N:ℝ)+1)+2*K*(N:ℝ) := by
  have han : (a:ℝ) ≤ (N:ℝ) := by exact_mod_cast ha
  have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg _
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith [mul_nonneg hK (sub_nonneg.mpr han)]

/-- Abstract retained-correction path inequality with a concrete coefficient.
The only transport premises are local adjacent squared-increment inequalities;
the finite Cauchy-Schwarz and variance estimates occur in the compiled proof.
Positive unimodal weights are supplied by their two mode-anchored monotonicity
conditions. The exterior correction values need only be nonnegative. -/
theorem retained_mode_variance_bound (z h c E : ℕ → ℝ) (K : ℝ) (N m : ℕ)
    (hm : m ≤ N) (hK : 0 ≤ K) (hz : ∀ i ≤ N, 0 < z i)
    (hleftmono : ∀ i j, i ≤ j → j ≤ m → z i ≤ z j)
    (hrightmono : ∀ i j, m ≤ i → i ≤ j → j ≤ N → z j ≤ z i)
    (hc : ∀ i ≤ N+1, 0 ≤ c i)
    (hcap : ∀ j, 1 ≤ j → j ≤ N → c j ≤ K*max (z (j-1)) (z j))
    (hXi : ∀ l ∈ Finset.Icc 1 N, 0 ≤ stencil z c l)
    (hE : ∀ l ∈ Finset.Icc 1 N, 0 ≤ E l)
    (hedge : ∀ l ∈ Finset.Icc 1 N, (h l-h (l-1))^2 ≤ stencil z c l*E l) :
    variance (fun i : Fin (N+1) => z i.val) (fun i => h i.val) ≤
      ((N:ℝ)*((N:ℝ)+1)+2*K*(N:ℝ))*(∑ l ∈ Finset.Icc 1 N, E l) := by
  have hL := (left_stencil_budget_bound z c K N m hm hz hleftmono hc hcap).trans
    (pathCoefficient_mono K m N hK hm)
  have hR := (right_stencil_budget_bound z c K N m hm hz hrightmono hc hcap).trans
    (pathCoefficient_mono K (N-m) N hK (Nat.sub_le _ _))
  have h := mode_anchor_variance_bound z h (stencil z c) E N m
    ((N:ℝ)*((N:ℝ)+1)+2*K*(N:ℝ)) ((N:ℝ)*((N:ℝ)+1)+2*K*(N:ℝ)) hm
    (fun i hi => (hz i hi).le) hXi hE hedge hL hR
  simpa only [max_self] using h

end Research.ModeAnchorStencil

#print axioms Research.ModeAnchorStencil.retained_mode_variance_bound
#check Research.ModeAnchorStencil.retained_mode_variance_bound
