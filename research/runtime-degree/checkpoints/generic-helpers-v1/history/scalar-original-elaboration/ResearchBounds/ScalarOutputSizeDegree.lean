/-
Private source-only quantitative obligation. Not compiled by this author.
The fixed-power program is imported from the exact existing schedule module;
no arithmetic or fixed-power implementation is replaced.
-/
import ResearchBounds.TreeArithmeticDegree
import Math115.LatticeScheduleProgram

namespace Math115.ScalarOutputDegree
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open Math115.DegreeBounds Polynomial

noncomputable section

lemma weight_mul_output (a b : ℕ) :
    weight (a*b) ≤ 4*(weight a + weight b)+1 := by
  have hw := weight_nat_le (a*b)
  have hs := nat_size_mul a b
  have ha := size_le_weight a
  have hb := size_le_weight b
  omega

lemma size_fixed_power_output (a k : ℕ) :
    (a^k).size ≤ k*a.size+1 := by
  induction k with
  | zero =>
    simpa only [pow_zero, Nat.zero_mul, Nat.zero_add] using
      (by decide : Nat.size 1 ≤ 1)
  | succ k ih =>
    rw [pow_succ]
    calc
      (a^k*a).size ≤ (a^k).size+a.size := nat_size_mul _ _
      _ ≤ (k*a.size+1)+a.size := Nat.add_le_add_right ih _
      _ = (k+1)*a.size+1 := by ring

lemma weight_fixed_power_output (a k : ℕ) :
    weight (a^k) ≤ 4*k*weight a+5 := by
  calc
    weight (a^k) ≤ 4*(a^k).size+1 := weight_nat_le _
    _ ≤ 4*(k*a.size+1)+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 4 (size_fixed_power_output a k)) 1
    _ = 4*k*a.size+5 := by ring
    _ ≤ 4*k*weight a+5 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left (4*k) (size_le_weight a)) 5

variable {A B D : Type} [Codec A] [Codec B] [Codec D]

/-- Keep the output-size polynomial independent of the charged-work witness. -/
lemma typed_composition_from_output_size
    {f : A→B} {g : B→D} {F : Realizer f} {G : Realizer g}
    {e t s : ℕ} (hF : Typed F e) (hG : Typed G t)
    (Pout : Polynomial ℕ) (hdeg : Pout.natDegree ≤ s)
    (hout : ∀ x, weight (f x) ≤ Pout.eval (weight x)) :
    Typed (composition F G) (max e (t*s)) := by
  obtain ⟨p,hp,hpb⟩ := hF
  obtain ⟨q,hq,hqb⟩ := hG
  refine ⟨p+q.comp Pout, degree_add hp (degree_comp hq hdeg), ?_⟩
  intro x
  have h1 := hpb x
  have h2 := hqb (f x)
  have h3 := polynomial_eval_monotone q (hout x)
  simp only [eval_add,eval_comp]
  change F.cost x+G.cost (f x)+weight (g (f x)) ≤ _
  dsimp only at h3
  omega

/-- Actual fixed-power realizer: coefficients may depend on fixed program k,
but charged cost plus encoded output weight has degree at most six. -/
theorem typed_actual_fixedPower (k : ℕ) :
    Typed (Math115.LatticeScheduleProgram.fixedPowerRealizer k) 6 := by
  induction k with
  | zero =>
    change Typed (constant (A:=ℕ) (1:ℕ)) 6
    obtain ⟨p,hp,hpb⟩ := typed_constant (A:=ℕ) (1:ℕ)
    exact ⟨p, hp.trans (by decide : 1≤6), hpb⟩
  | succ k ih =>
    let Prep : Realizer (fun a : ℕ => (a^k,a)) :=
      pair (Math115.LatticeScheduleProgram.fixedPowerRealizer k) identity
    have hPrep : Typed Prep 6 := by
      simpa only [Prep] using typed_pair (e:=6) (t:=1) ih typed_identity
    let Pout : Polynomial ℕ := C (4*k+1)*X+C 6
    have hdeg : Pout.natDegree ≤ 1 := degree_affine (4*k+1) 6
    have hout : ∀ a : ℕ, weight (a^k,a) ≤ Pout.eval (weight a) := by
      intro a
      have hp := weight_fixed_power_output a k
      simp only [Pout,weight_prod,eval_add,eval_mul,eval_C,eval_X]
      nlinarith
    have hComp : Typed (composition Prep multiply) 6 := by
      simpa only [Nat.mul_one, max_self] using
        typed_composition_from_output_size (e:=6) (t:=6) (s:=1)
          hPrep typed_multiply Pout hdeg hout
    unfold Math115.LatticeScheduleProgram.fixedPowerRealizer
    apply typed_congr
    exact hComp

end
end Math115.ScalarOutputDegree
