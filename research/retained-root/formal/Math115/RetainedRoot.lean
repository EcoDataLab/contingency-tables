import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Log
import Math115.ShapeDegreeBound

/-! Scalar consequences of the full correction stencil. This module does not
prove the physical summation-by-parts or retained-matrix transport interface. -/
namespace Math115.RetainedRoot

noncomputable def interiorCoefficient (a b S : ℝ) : ℝ :=
  -(S*(a-b)^2)/(a^2*b^2)+(b-a)/(a*b)

noncomputable def endpointCoefficient (a b S : ℝ) : ℝ :=
  2*S/(a*b)-(S-a)/a^2

lemma cap_constant_nonnegative (a b c K : ℝ) (ha : 0 < a) (_hb : 0 < b)
    (hc : 0 ≤ c) (hcap : c ≤ K*max a b) : 0 ≤ K := by
  have hmax : 0 < max a b := ha.trans_le (le_max_left _ _)
  have hprod : 0 ≤ K*max a b := hc.trans hcap
  exact (mul_nonneg_iff_of_pos_right hmax).mp hprod

/-- Full interior stencil coefficient, without requiring monotonicity of the
two child masses. Reversed masses give a nonpositive coefficient. -/
theorem interior_cap (a b S c K : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hS : a ≤ S) (hc : 0 ≤ c) (hcap : c ≤ K*max a b) :
    c*interiorCoefficient a b S ≤ K := by
  have hK := cap_constant_nonnegative a b c K ha hb hc hcap
  have hS0 : 0 ≤ S := ha.le.trans hS
  by_cases hab : a ≤ b
  · rw [max_eq_right hab] at hcap
    have hid : interiorCoefficient a b S = (b-a)/b^2 -
        (S-a)*(a-b)^2/(a^2*b^2) := by
      unfold interiorCoefficient
      field_simp
      ring
    have hD : interiorCoefficient a b S ≤ (b-a)/b^2 := by
      rw [hid]
      have hnon : 0 ≤ (S-a)*(a-b)^2/(a^2*b^2) := by positivity
      linarith only [hnon]
    have hfrac : 0 ≤ (b-a)/b^2 := by positivity
    calc
      _ ≤ c*((b-a)/b^2) := mul_le_mul_of_nonneg_left hD hc
      _ ≤ (K*b)*((b-a)/b^2) := mul_le_mul_of_nonneg_right hcap hfrac
      _ = K*(1-a/b) := by field_simp <;> ring
      _ ≤ K := by
        have hratio : 0 ≤ a/b := by positivity
        nlinarith only [mul_nonneg hK hratio]
  · have hba : b ≤ a := le_of_not_ge hab
    have hD : interiorCoefficient a b S ≤ 0 := by
      unfold interiorCoefficient
      have hneg : -(S*(a-b)^2)/(a^2*b^2) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith [sq_nonneg (a-b)]
      have hneg' : (b-a)/(a*b) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      linarith only [hneg,hneg']
    exact (mul_nonpos_of_nonneg_of_nonpos hc hD).trans hK

/-- The uncanceled anchor endpoint costs at most K(M+1), using that the
endpoint is at a mode and the preceding cumulative mass is at most M*a. -/
theorem endpoint_cap (a b S c K M : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (hS : a ≤ S) (hSM : S ≤ M*a)
    (hc : 0 ≤ c) (hcap : c ≤ K*b) :
    c*endpointCoefficient a b S ≤ K*(M+1) := by
  have hK : 0 ≤ K := (mul_nonneg_iff_of_pos_right hb).mp (hc.trans hcap)
  have hS0 : 0 ≤ S := ha.le.trans hS
  have hid : endpointCoefficient a b S = (S+a)/(a*b) -
      (b-a)*(S-a)/(a^2*b) := by
    unfold endpointCoefficient
    field_simp
    ring
  have hD : endpointCoefficient a b S ≤ (S+a)/(a*b) := by
    rw [hid]
    have hnon : 0 ≤ (b-a)*(S-a)/(a^2*b) := by positivity
    linarith only [hnon]
  have hfrac : 0 ≤ (S+a)/(a*b) := by positivity
  calc
    _ ≤ c*((S+a)/(a*b)) := mul_le_mul_of_nonneg_left hD hc
    _ ≤ (K*b)*((S+a)/(a*b)) := mul_le_mul_of_nonneg_right hcap hfrac
    _ = K*(S/a+1) := by field_simp <;> ring
    _ ≤ K*(M+1) := mul_le_mul_of_nonneg_left
      (by have h := (div_le_iff₀ ha).mpr hSM; linarith only [h]) hK

def quarterProduct (V : ℕ) : ℕ := (V+1)^2/4

noncomputable def transversalCoefficient (p V : ℕ) : ℝ :=
  (V:ℝ)*((V:ℝ)+1)+2*((p-1:ℕ):ℝ)*(V:ℝ)*(quarterProduct V:ℝ)

noncomputable def fullCoefficient (p V : ℕ) : ℝ :=
  transversalCoefficient p V + (Real.sqrt ((p:ℝ)^2*transversalCoefficient p V)+1)^2

theorem quarterProduct_bound (V : ℕ) (hV : 2 ≤ V) :
    (quarterProduct V:ℝ) ≤ (V:ℝ)^2/2 := by
  by_cases hV2 : V=2
  · subst V; norm_num [quarterProduct]
  · have hV3 : (3:ℝ) ≤ V := by exact_mod_cast (show 3 ≤ V by omega)
    have hmulN : 4*quarterProduct V ≤ (V+1)^2 := by
      unfold quarterProduct
      exact Nat.mul_div_le _ _
    have hmul : (4:ℝ)*(quarterProduct V:ℝ) ≤ ((V:ℝ)+1)^2 := by exact_mod_cast hmulN
    have hpoly : 0 ≤ ((V:ℝ)-3)*((V:ℝ)+1) := by positivity
    nlinarith only [hmul, hpoly, hV3]

theorem transversal_bounds (p V : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V) :
    6 ≤ transversalCoefficient p V ∧ transversalCoefficient p V ≤ (p:ℝ)*(V:ℝ)^3 := by
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : 0 ≤ (p:ℝ)-1 := by linarith only [hpR]
  have hVR : (2:ℝ) ≤ V := by exact_mod_cast hV
  have hq := quarterProduct_bound V hV
  have hcast : ((p-1:ℕ):ℝ) = (p:ℝ)-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hm := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2*((p:ℝ)-1)*(V:ℝ) by positivity)
  have hbase : (V:ℝ)*((V:ℝ)+1) ≤ (V:ℝ)^3 := by
    have hpoly : 0 ≤ ((V:ℝ)-2)*(V:ℝ)*((V:ℝ)+1) := by positivity
    nlinarith only [hpoly, hVR]
  unfold transversalCoefficient
  rw [hcast]
  constructor
  · have hnon : 0 ≤ 2*((p:ℝ)-1)*(V:ℝ)*(quarterProduct V:ℝ) := by positivity
    nlinarith only [hVR, hnon, sq_nonneg ((V:ℝ)-2)]
  · nlinarith only [hm, hbase]

theorem repair_coefficient_bound (p : ℕ) (T : ℝ) (hp : 2 ≤ p) (hT : 6 ≤ T) :
    T+(Real.sqrt ((p:ℝ)^2*T)+1)^2 ≤ 2*(p:ℝ)^2*T := by
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  rw [Real.sqrt_mul (sq_nonneg (p:ℝ)), Real.sqrt_sq (Nat.cast_nonneg p)]
  have hsq := Real.sq_sqrt (show 0 ≤ T by linarith)
  have hroot : Real.sqrt T ≤ T/2 := by
    have hn := Real.sqrt_nonneg T
    nlinarith only [hsq, hn, hT, sq_nonneg (T-4)]
  have hcross := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 2*(p:ℝ) by positivity)
  have hpoly : (p:ℝ)^2-(p:ℝ)-1 ≥ 1 := by
    have ht : 0 ≤ ((p:ℝ)-2)*((p:ℝ)+1) := by positivity
    nlinarith only [ht]
  have hslack := mul_le_mul_of_nonneg_right hpoly (show 0 ≤ T by linarith)
  nlinarith only [hsq,hcross,hslack,hT]

theorem fullCoefficient_bound (p V : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V) :
    fullCoefficient p V ≤ 2*(p:ℝ)^3*(V:ℝ)^3 := by
  have ht := transversal_bounds p V hp hV
  unfold fullCoefficient
  calc
    _ ≤ 2*(p:ℝ)^2*transversalCoefficient p V := repair_coefficient_bound p _ hp ht.1
    _ ≤ 2*(p:ℝ)^2*((p:ℝ)*(V:ℝ)^3) := mul_le_mul_of_nonneg_left ht.2 (by positivity)
    _ = _ := by ring

/-- Scalar trace composition only: the physical summation-by-parts transport
and trace identities must separately justify using this new T coefficient. -/
theorem rational_trace_coefficient_bound (p V Q : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQ : Q ≤ 4*p-3) :
    4*(Q:ℝ)*fullCoefficient p V ≤ 32*(p:ℝ)^4*(V:ℝ)^3 := by
  have hqN : Q ≤ 4*p := hQ.trans (Nat.sub_le _ _)
  have hq : (Q:ℝ) ≤ 4*(p:ℝ) := by exact_mod_cast hqN
  calc
    _ ≤ 4*(Q:ℝ)*(2*(p:ℝ)^3*(V:ℝ)^3) :=
      mul_le_mul_of_nonneg_left (fullCoefficient_bound p V hp hV) (by positivity)
    _ ≤ 4*(4*(p:ℝ))*(2*(p:ℝ)^3*(V:ℝ)^3) := by gcongr
    _ = _ := by ring

theorem rational_uniform_d13 (p V Q d : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQ : Q ≤ 4*p-3) (hpd : p ≤ d) (hVd : V ≤ 5*d^3) :
    4*(Q:ℝ)*fullCoefficient p V ≤ 4000*(d:ℝ)^13 := by
  have hpR : (p:ℝ) ≤ d := by exact_mod_cast hpd
  have hVR : (V:ℝ) ≤ 5*(d:ℝ)^3 := by exact_mod_cast hVd
  calc
    _ ≤ 32*(p:ℝ)^4*(V:ℝ)^3 := rational_trace_coefficient_bound p V Q hp hV hQ
    _ ≤ 32*(d:ℝ)^4*(5*(d:ℝ)^3)^3 := by gcongr
    _ = _ := by ring

def dyadicDenominator (Q : ℕ) : ℕ := 2^Nat.clog 2 (2*Q)

theorem dyadicDenominator_bounds (Q : ℕ) (hQ : 1 ≤ Q) :
    2*Q ≤ dyadicDenominator Q ∧ dyadicDenominator Q < 4*Q := by
  have hk := Nat.clog_pos (by norm_num : 1 < (2:ℕ)) (by omega : 1 < 2*Q)
  have hprev := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2:ℕ)) (by omega : 1 < 2*Q)
  have heq : Nat.clog 2 (2*Q) = (Nat.clog 2 (2*Q)).pred+1 := by
    simp only [Nat.pred_eq_sub_one]
    omega
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  unfold dyadicDenominator
  rw [heq,pow_succ]
  omega

theorem dyadic_trace_coefficient_bound (p V Q : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQpos : 1 ≤ Q) (hQ : Q ≤ 4*p-3) :
    2*(dyadicDenominator Q:ℝ)*fullCoefficient p V ≤ 64*(p:ℝ)^4*(V:ℝ)^3 := by
  have hd : (dyadicDenominator Q:ℝ) ≤ 4*(Q:ℝ) := by
    exact_mod_cast (dyadicDenominator_bounds Q hQpos).2.le
  have hqN : Q ≤ 4*p := hQ.trans (Nat.sub_le _ _)
  have hq : (Q:ℝ) ≤ 4*(p:ℝ) := by exact_mod_cast hqN
  have hdp : (dyadicDenominator Q:ℝ) ≤ 16*(p:ℝ) := by linarith only [hd,hq]
  calc
    _ ≤ 2*(dyadicDenominator Q:ℝ)*(2*(p:ℝ)^3*(V:ℝ)^3) :=
      mul_le_mul_of_nonneg_left (fullCoefficient_bound p V hp hV) (by positivity)
    _ ≤ 2*(16*(p:ℝ))*(2*(p:ℝ)^3*(V:ℝ)^3) := by gcongr
    _ = _ := by ring

theorem dyadic_uniform_d13 (p V Q d : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQpos : 1 ≤ Q) (hQ : Q ≤ 4*p-3) (hpd : p ≤ d) (hVd : V ≤ 5*d^3) :
    2*(dyadicDenominator Q:ℝ)*fullCoefficient p V ≤ 8000*(d:ℝ)^13 := by
  have hpR : (p:ℝ) ≤ d := by exact_mod_cast hpd
  have hVR : (V:ℝ) ≤ 5*(d:ℝ)^3 := by exact_mod_cast hVd
  calc
    _ ≤ 64*(p:ℝ)^4*(V:ℝ)^3 := dyadic_trace_coefficient_bound p V Q hp hV hQpos hQ
    _ ≤ 64*(d:ℝ)^4*(5*(d:ℝ)^3)^3 := by gcongr
    _ = _ := by ring

/-- Scalar changed-cutoff corollary. The hypotheses on p and V do not
construct a physical transport bound, cutoff classification, or sampler. -/
theorem rational_uniform_d10 (p V Q d : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQ : Q ≤ 4*p-3) (hpd : p ≤ d) (hVd : V ≤ 11*d^2) :
    4*(Q:ℝ)*fullCoefficient p V ≤ 42592*(d:ℝ)^10 := by
  have hpR : (p:ℝ) ≤ d := by exact_mod_cast hpd
  have hVR : (V:ℝ) ≤ 11*(d:ℝ)^2 := by exact_mod_cast hVd
  calc
    _ ≤ 32*(p:ℝ)^4*(V:ℝ)^3 := rational_trace_coefficient_bound p V Q hp hV hQ
    _ ≤ 32*(d:ℝ)^4*(11*(d:ℝ)^2)^3 := by gcongr
    _ = _ := by ring

/-- Scalar dyadic corollary under the changed width allowance; no physical
proposal, trace composition, or runtime integration is asserted here. -/
theorem dyadic_uniform_d10 (p V Q d : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQpos : 1 ≤ Q) (hQ : Q ≤ 4*p-3) (hpd : p ≤ d) (hVd : V ≤ 11*d^2) :
    2*(dyadicDenominator Q:ℝ)*fullCoefficient p V ≤ 85184*(d:ℝ)^10 := by
  have hpR : (p:ℝ) ≤ d := by exact_mod_cast hpd
  have hVR : (V:ℝ) ≤ 11*(d:ℝ)^2 := by exact_mod_cast hVd
  calc
    _ ≤ 64*(p:ℝ)^4*(V:ℝ)^3 := dyadic_trace_coefficient_bound p V Q hp hV hQpos hQ
    _ ≤ 64*(d:ℝ)^4*(11*(d:ℝ)^2)^3 := by gcongr
    _ = _ := by ring

open Math115.ShapeDegreeBound

/-- Discharge the scalar shape allowance from layout capacities; no proposed
neighbor-count conclusion or coefficient conclusion is assumed. -/
theorem shape_rational_trace_bound (m n R C V : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hR : R ≤ m) (hC : C ≤ n) (hp : 2 ≤ m*n-R*C) (hV : 2 ≤ V) :
    4*(proposalAllowance m n R C:ℝ)*fullCoefficient (m*n-R*C) V ≤
      32*((m*n-R*C:ℕ):ℝ)^4*(V:ℝ)^3 :=
  rational_trace_coefficient_bound _ _ _ hp hV (proposalAllowance_bounds m n R C hm hn hR hC hp).2

theorem shape_dyadic_trace_bound (m n R C V : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hR : R ≤ m) (hC : C ≤ n) (hp : 2 ≤ m*n-R*C) (hV : 2 ≤ V) :
    2*(dyadicDenominator (proposalAllowance m n R C):ℝ)*fullCoefficient (m*n-R*C) V ≤
      64*((m*n-R*C:ℕ):ℝ)^4*(V:ℝ)^3 :=
  dyadic_trace_coefficient_bound _ _ _ hp hV
    (proposalAllowance_bounds m n R C hm hn hR hC hp).1
    (proposalAllowance_bounds m n R C hm hn hR hC hp).2

end Math115.RetainedRoot
