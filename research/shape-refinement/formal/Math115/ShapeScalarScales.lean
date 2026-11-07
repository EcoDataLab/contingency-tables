import Math115.ShapeDegreeBound
import Math115.EffectiveWidthBound
import Math115.PaddingGrowth
import Mathlib.Data.Nat.Log

/-! Scalar composition of shape envelopes and local completion scales.
The graph degree and accepted trace coefficient interface remain separate. -/
namespace Math115.ShapeScalarScales

open Math115.ShapeDegreeBound Math115.PhysicalRepairRefinement

def dyadicDenominator (Q : ℕ) : ℕ := 2 ^ Nat.clog 2 (2*Q)

theorem dyadicDenominator_bounds (Q : ℕ) (hQ : 1 ≤ Q) :
    2*Q ≤ dyadicDenominator Q ∧ dyadicDenominator Q < 4*Q := by
  have hk := Nat.clog_pos (by norm_num : 1 < (2:ℕ)) (by omega : 1 < 2*Q)
  have hprev := Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2:ℕ))
    (by omega : 1 < 2*Q)
  have heq : Nat.clog 2 (2*Q) = (Nat.clog 2 (2*Q)).pred + 1 := by
    simp only [Nat.pred_eq_sub_one]
    omega
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  unfold dyadicDenominator
  rw [heq, pow_succ]
  omega

/-- The scalar rational allowance uses the actual refined width coefficient,
not an assumed p³V⁴ coefficient. Q may be any smaller geometric allowance. -/
theorem rational_coefficient_le (p V Q : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQ : Q ≤ 4*p-3) :
    4*(Q:ℝ)*refinedConstant p V ≤ 16*(p:ℝ)^4*(V:ℝ)^4 := by
  have hw := Math115.EffectiveWidthBound.refinedConstant_le_actual_width p V hp hV
  have hqN : Q ≤ 4*p := hQ.trans (Nat.sub_le _ _)
  have hq : (Q:ℝ) ≤ 4*(p:ℝ) := by exact_mod_cast hqN
  calc
    _ ≤ 4*(Q:ℝ)*((p:ℝ)^3*(V:ℝ)^4) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ 4*(4*(p:ℝ))*((p:ℝ)^3*(V:ℝ)^4) := by gcongr
    _ = _ := by ring

theorem dyadic_coefficient_le (p V Q : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQpos : 1 ≤ Q) (hQ : Q ≤ 4*p-3) :
    2*(dyadicDenominator Q:ℝ)*refinedConstant p V ≤ 32*(p:ℝ)^4*(V:ℝ)^4 := by
  have hw := Math115.EffectiveWidthBound.refinedConstant_le_actual_width p V hp hV
  have hdN := (dyadicDenominator_bounds Q hQpos).2.le
  have hd : (dyadicDenominator Q:ℝ) ≤ 4*(Q:ℝ) := by exact_mod_cast hdN
  have hqN : Q ≤ 4*p := hQ.trans (Nat.sub_le _ _)
  have hq : (Q:ℝ) ≤ 4*(p:ℝ) := by exact_mod_cast hqN
  have hdp : (dyadicDenominator Q:ℝ) ≤ 4*(4*(p:ℝ)) := by linarith only [hd, hq]
  calc
    _ ≤ 2*(dyadicDenominator Q:ℝ)*((p:ℝ)^3*(V:ℝ)^4) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ 2*(4*(4*(p:ℝ)))*((p:ℝ)^3*(V:ℝ)^4) := by gcongr
    _ = _ := by ring

theorem shape_rational_coefficient_le (m n R C V : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hR : R ≤ m) (hC : C ≤ n) (hp : 2 ≤ m*n-R*C) (hV : 2 ≤ V) :
    4*(degreeEnvelope m n R C:ℝ)*refinedConstant (m*n-R*C) V ≤
      16*((m*n-R*C:ℕ):ℝ)^4*(V:ℝ)^4 :=
  rational_coefficient_le _ _ _ hp hV (degreeEnvelope_le m n R C hm hn hR hC hp)

theorem proposal_rational_coefficient_le (m n R C V : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hR : R ≤ m) (hC : C ≤ n) (hp : 2 ≤ m*n-R*C) (hV : 2 ≤ V) :
    4*(proposalAllowance m n R C:ℝ)*refinedConstant (m*n-R*C) V ≤
      16*((m*n-R*C:ℕ):ℝ)^4*(V:ℝ)^4 :=
  rational_coefficient_le _ _ _ hp hV (proposalAllowance_bounds m n R C hm hn hR hC hp).2

theorem proposal_dyadic_coefficient_le (m n R C V : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hR : R ≤ m) (hC : C ≤ n) (hp : 2 ≤ m*n-R*C) (hV : 2 ≤ V) :
    2*(dyadicDenominator (proposalAllowance m n R C):ℝ)*refinedConstant (m*n-R*C) V ≤
      32*((m*n-R*C:ℕ):ℝ)^4*(V:ℝ)^4 :=
  dyadic_coefficient_le _ _ _ hp hV (proposalAllowance_bounds m n R C hm hn hR hC hp).1
    (proposalAllowance_bounds m n R C hm hn hR hC hp).2

theorem rational_uniform_d16 (p V Q d : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQ : Q ≤ 4*p-3) (hpd : p ≤ d) (hVd : V ≤ 5*d^3) :
    4*(Q:ℝ)*refinedConstant p V ≤ 10000*(d:ℝ)^16 := by
  have hpR : (p:ℝ) ≤ (d:ℝ) := by exact_mod_cast hpd
  have hvR : (V:ℝ) ≤ 5*(d:ℝ)^3 := by exact_mod_cast hVd
  calc
    _ ≤ 16*(p:ℝ)^4*(V:ℝ)^4 := rational_coefficient_le p V Q hp hV hQ
    _ ≤ 16*(d:ℝ)^4*(5*(d:ℝ)^3)^4 := by gcongr
    _ = _ := by ring

theorem dyadic_uniform_d16 (p V Q d : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQpos : 1 ≤ Q) (hQ : Q ≤ 4*p-3) (hpd : p ≤ d) (hVd : V ≤ 5*d^3) :
    2*(dyadicDenominator Q:ℝ)*refinedConstant p V ≤ 20000*(d:ℝ)^16 := by
  have hpR : (p:ℝ) ≤ (d:ℝ) := by exact_mod_cast hpd
  have hvR : (V:ℝ) ≤ 5*(d:ℝ)^3 := by exact_mod_cast hVd
  calc
    _ ≤ 32*(p:ℝ)^4*(V:ℝ)^4 := dyadic_coefficient_le p V Q hp hV hQpos hQ
    _ ≤ 32*(d:ℝ)^4*(5*(d:ℝ)^3)^4 := by gcongr
    _ = _ := by ring

def guardedCutoff (g L e : ℕ) : ℕ := max 2 (max (2*L) ((47*g*L*e+31)/32-1))

/-- The exact integer ceiling-minus-one convention discharges the padding
budget even when its subexpression is truncated at zero. -/
theorem guardedCutoff_budget (g L e : ℕ) :
    47*g*L*e ≤ 32*(guardedCutoff g L e+1) := by
  have h := Nat.mod_lt (47*g*L*e+31) (by norm_num : 0 < (32:ℕ))
  have heq := Nat.mod_add_div (47*g*L*e+31) 32
  have hcut : (47*g*L*e+31)/32-1 ≤ guardedCutoff g L e := by
    exact (le_max_right (2*L) _).trans (le_max_right 2 _)
  omega

theorem guardedCutoff_floors (g L e : ℕ) :
    2 ≤ guardedCutoff g L e ∧ 2*L ≤ guardedCutoff g L e :=
  ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _)⟩

theorem guardedCutoff_linear_majorant (g L e : ℕ) :
    guardedCutoff g L e ≤ max 2 (max (2*L) (2*g*L*e)) := by
  have h := Nat.mod_lt (47*g*L*e+31) (by norm_num : 0 < (32:ℕ))
  have heq := Nat.mod_add_div (47*g*L*e+31) 32
  have ha : 47*g*L*e = 47*(g*L*e) := by ring
  have hb : 2*g*L*e = 2*(g*L*e) := by ring
  have hcut : (47*g*L*e+31)/32-1 ≤ 2*g*L*e := by
    rw [ha] at h heq ⊢
    rw [hb]
    omega
  unfold guardedCutoff
  exact max_le_max (le_refl 2) (max_le_max (le_refl (2*L)) hcut)

theorem two_by_two_cutoff_le (e d : ℕ) (he : e ≤ d) (hd : 1 ≤ d) :
    guardedCutoff 4 3 e ≤ 18*d := by
  have h := Nat.mod_lt (47*4*3*e+31) (by norm_num : 0 < (32:ℕ))
  have heq := Nat.mod_add_div (47*4*3*e+31) 32
  unfold guardedCutoff
  omega

open OAI.ContingencyTables OAI.CommonBasesFPRAS CompletionCounts

/-- An actual ordinary-table cardinality consequence of the guarded cutoff.
Marked-cell membership is supplied from the cutoff classification separately. -/
theorem guarded_padded_count_le_twice
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (r : I → ℕ) (c : J → ℕ) (K : Finset (I × J)) (L : ℕ)
    (hrow : ∀ p ∈ K, guardedCutoff K.card L ((Fintype.card I-1)*(Fintype.card J-1)) ≤ r p.1)
    (hcol : ∀ p ∈ K, guardedCutoff K.card L ((Fintype.card I-1)*(Fintype.card J-1)) ≤ c p.2) :
    Fintype.card (Table (paddedRows r (largePadding K L))
      (paddedColumns c (largePadding K L))) ≤ 2*Fintype.card (Table r c) := by
  apply Math115.PaddingGrowthAlgebra.count_le_twice_of_growth _ _ _ _ _
    (Math115.PaddingGrowth.large_padding_count_growth r c K L _ hrow hcol)
  have h := guardedCutoff_budget K.card L ((Fintype.card I-1)*(Fintype.card J-1))
  convert h using 1
  ring

def localDimension (R C : ℕ) : ℕ := max 14 (max R (max C ((R-1)*(C-1)+1)))
def localPadding (R C : ℕ) : ℕ := 3*localDimension R C

theorem localDimension_conditions (R C : ℕ) :
    14 ≤ localDimension R C ∧ R ≤ localDimension R C ∧ C ≤ localDimension R C ∧
      (R-1)*(C-1) ≤ localDimension R C-1 := by
  unfold localDimension
  have h14 := le_max_left 14 (max R (max C ((R-1)*(C-1)+1)))
  have hR := (le_max_left R (max C ((R-1)*(C-1)+1))).trans
    (le_max_right 14 (max R (max C ((R-1)*(C-1)+1))))
  have hC := (le_max_left C ((R-1)*(C-1)+1)).trans
    ((le_max_right R (max C ((R-1)*(C-1)+1))).trans
      (le_max_right 14 (max R (max C ((R-1)*(C-1)+1)))))
  have he := (le_max_right C ((R-1)*(C-1)+1)).trans
    ((le_max_right R (max C ((R-1)*(C-1)+1))).trans
      (le_max_right 14 (max R (max C ((R-1)*(C-1)+1)))))
  omega

theorem localPadding_half_acceptance_budget (R C : ℕ) :
    3*((R-1)*(C-1)) ≤ localPadding R C := by
  have h := (localDimension_conditions R C).2.2.2
  unfold localPadding
  omega

/-- Scalar floors for padded residual margins with ordinary slack. This does
not construct the physical reindexing/call adapter to draw_semantics. -/
theorem localPadding_residual_floors (R C rowSlack colSlack : ℕ) :
    C*(3*localDimension R C) ≤ rowSlack+C*localPadding R C ∧
    R*(3*localDimension R C) ≤ colSlack+R*localPadding R C := by
  unfold localPadding
  omega

end Math115.ShapeScalarScales
