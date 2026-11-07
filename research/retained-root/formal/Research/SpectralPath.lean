import Math115.PathVariance
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace Research.SpectralPath

open scoped BigOperators Classical
open OAI.ContingencyTables.FiniteExposureVariance
open Metric Set

variable {X : Type*} [Fintype X]

noncomputable def weightedSum (z : X → ℝ) : (X → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, z i*x i
  map_add' x y := by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' t x := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring


noncomputable def weightedSquare (z x : X → ℝ) : ℝ := ∑ i, z i*(x i)^2

lemma weightedSquare_nonnegative (z x : X → ℝ) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ weightedSquare z x := Finset.sum_nonneg (fun i _ => mul_nonneg (hz i) (sq_nonneg _))

lemma weightedSquare_positive (z x : X → ℝ) (hz : ∀ i, 0 < z i) (hx : x ≠ 0) :
    0 < weightedSquare z x := by
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    apply hx
    funext i
    exact h i
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hz i).le (sq_nonneg _)
  · exact ⟨i,Finset.mem_univ _,mul_pos (hz i) (sq_pos_of_ne_zero hi)⟩

lemma weightedSquare_smul (z x : X → ℝ) (t : ℝ) :
    weightedSquare z (t • x)=t^2*weightedSquare z x := by
  unfold weightedSquare
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

lemma weightedSquare_continuous (z : X → ℝ) : Continuous (weightedSquare z) := by
  unfold weightedSquare
  fun_prop

/-- Compactness produces a positive minimizing Rayleigh eigenvalue for any
continuous, quadratic-homogeneous energy whose only zero on the mean-zero
subspace is zero. No numerical variance/Poincare bound is a premise. -/
theorem exists_positive_minimizer (z : X → ℝ) (Q : (X → ℝ) → ℝ)
    (hz : ∀ i, 0 < z i) (hQ : Continuous Q)
    (hQ0 : Q 0=0) (hhom : ∀ t x, Q (t • x)=t^2*Q x)
    (hpos : ∀ x, weightedSum z x=0 → x ≠ 0 → 0 < Q x)
    (hnontrivial : ∃ x, weightedSum z x=0 ∧ x ≠ 0) :
    ∃ (lam : ℝ) (h : X → ℝ), 0 < lam ∧ weightedSum z h=0 ∧ h ≠ 0 ∧
      Q h=lam*weightedSquare z h ∧
      ∀ x, weightedSum z x=0 → lam*weightedSquare z x ≤ Q x := by
  let V := LinearMap.ker (weightedSum z)
  obtain ⟨v,hvmean,hv0⟩ := hnontrivial
  let v' : V := ⟨v,hvmean⟩
  have hv' : v' ≠ 0 := by
    intro he
    exact hv0 (congrArg Subtype.val he)
  have hvnorm : ‖v'‖ ≠ 0 := norm_ne_zero_iff.mpr hv'
  let vunit : V := (‖v'‖⁻¹ : ℝ) • v'
  have hvunit : vunit ∈ sphere (0:V) 1 := by
    simp only [mem_sphere_zero_iff_norm,vunit,norm_smul,Real.norm_eq_abs,
      abs_inv,abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ hvnorm
  let q : V → ℝ := fun x => Q x.val/weightedSquare z x.val
  have hcompact : IsCompact (sphere (0:V) 1) := isCompact_sphere _ _
  have hcont : ContinuousOn q (sphere (0:V) 1) := by
    apply ContinuousOn.div
    · exact hQ.comp continuous_subtype_val |>.continuousOn
    · exact (weightedSquare_continuous z).comp continuous_subtype_val |>.continuousOn
    · intro x hx
      have hx0 : x.val ≠ 0 := by
        intro he
        have he' : x=0 := Subtype.ext he
        simp [he'] at hx
      exact ne_of_gt (weightedSquare_positive z x.val hz hx0)
  obtain ⟨h,hh,hmin⟩ := hcompact.exists_isMinOn ⟨vunit,hvunit⟩ hcont
  have hh0 : h.val ≠ 0 := by
    intro he
    have he' : h=0 := Subtype.ext he
    simp [he'] at hh
  have hhsq : 0 < weightedSquare z h.val := weightedSquare_positive z h.val hz hh0
  have hhmean : weightedSum z h.val=0 := h.property
  refine ⟨q h,h.val,div_pos (hpos _ hhmean hh0) hhsq,hhmean,hh0,?_,?_⟩
  · exact (div_mul_cancel₀ _ (ne_of_gt hhsq)).symm
  · intro x hxmean
    by_cases hx0 : x=0
    · simp [hx0,weightedSquare,hQ0]
    let x' : V := ⟨x,hxmean⟩
    have hx' : x' ≠ 0 := by
      intro he
      exact hx0 (congrArg Subtype.val he)
    have hxnorm : ‖x'‖ ≠ 0 := norm_ne_zero_iff.mpr hx'
    let unit : V := (‖x'‖⁻¹ : ℝ) • x'
    have hunit : unit ∈ sphere (0:V) 1 := by
      simp only [mem_sphere_zero_iff_norm,unit,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_of_nonneg (norm_nonneg _)]
      exact inv_mul_cancel₀ hxnorm
    have hratio : q unit=Q x/weightedSquare z x := by
      change Q ((‖x'‖⁻¹ : ℝ) • x)/weightedSquare z ((‖x'‖⁻¹ : ℝ) • x)=_
      rw [hhom,weightedSquare_smul]
      exact mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero hxnorm))
    have hbound := hmin hunit
    change q h ≤ q unit at hbound
    rw [hratio] at hbound
    exact (le_div_iff₀ (weightedSquare_positive z x hz hx0)).mp hbound


noncomputable def weightedPair (z x y : X → ℝ) : ℝ := ∑ i, z i*x i*y i

lemma weightedSquare_add_smul (z x y : X → ℝ) (t : ℝ) :
    weightedSquare z (x+t • y)=weightedSquare z x+2*t*weightedPair z x y+
      t^2*weightedSquare z y := by
  unfold weightedSquare weightedPair
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

noncomputable def pathEnergy (N : ℕ) (r : ℕ → ℝ) (x : Fin (N+1) → ℝ) : ℝ :=
  ∑ l : Fin N, (x l.castSucc-x l.succ)^2/r (l.val+1)

noncomputable def pathPair (N : ℕ) (r : ℕ → ℝ) (x y : Fin (N+1) → ℝ) : ℝ :=
  ∑ l : Fin N, (x l.castSucc-x l.succ)*(y l.castSucc-y l.succ)/r (l.val+1)

lemma pathEnergy_nonnegative (N : ℕ) (r : ℕ → ℝ) (x : Fin (N+1) → ℝ)
    (hr : ∀ l : Fin N, 0 < r (l.val+1)) : 0 ≤ pathEnergy N r x :=
  Finset.sum_nonneg (fun l _ => div_nonneg (sq_nonneg _) (hr l).le)

lemma pathEnergy_continuous (N : ℕ) (r : ℕ → ℝ) : Continuous (pathEnergy N r) := by
  unfold pathEnergy
  fun_prop

lemma pathEnergy_smul (N : ℕ) (r : ℕ → ℝ) (x : Fin (N+1) → ℝ) (t : ℝ) :
    pathEnergy N r (t • x)=t^2*pathEnergy N r x := by
  unfold pathEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

lemma pathEnergy_add_smul (N : ℕ) (r : ℕ → ℝ) (x y : Fin (N+1) → ℝ) (t : ℝ) :
    pathEnergy N r (x+t • y)=pathEnergy N r x+2*t*pathPair N r x y+
      t^2*pathEnergy N r y := by
  unfold pathEnergy pathPair
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma pathEnergy_zero_constant (N : ℕ) (r : ℕ → ℝ) (x : Fin (N+1) → ℝ)
    (hr : ∀ l : Fin N, 0 < r (l.val+1)) (hQ : pathEnergy N r x=0) :
    ∀ i : Fin (N+1), x i=x 0 := by
  have hedge : ∀ l : Fin N, x l.castSucc=x l.succ := by
    intro l
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) =>
        div_nonneg (sq_nonneg (x j.castSucc-x j.succ)) (hr j).le)).mp hQ l (Finset.mem_univ _)
    have he : (x l.castSucc-x l.succ)^2=0 :=
      (div_eq_zero_iff.mp hs).resolve_right (ne_of_gt (hr l))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp he)
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact (hedge i).symm.trans ih

lemma pathEnergy_positive_meanZero (N : ℕ) (z : Fin (N+1) → ℝ) (r : ℕ → ℝ)
    (hz : ∀ i, 0 < z i) (hr : ∀ l : Fin N, 0 < r (l.val+1))
    (x : Fin (N+1) → ℝ) (hmean : weightedSum z x=0) (hx : x ≠ 0) :
    0 < pathEnergy N r x := by
  by_contra hn
  have hQ : pathEnergy N r x=0 :=
    le_antisymm (le_of_not_gt hn) (pathEnergy_nonnegative N r x hr)
  have hconst := pathEnergy_zero_constant N r x hr hQ
  have hZ : 0 < ∑ i, z i := Finset.sum_pos' (fun i _ => (hz i).le)
    ⟨0,Finset.mem_univ _,hz 0⟩
  have ht : (∑ i, z i)*x 0=0 := by
    rw [Finset.sum_mul]
    change (∑ i, z i*x i)=0 at hmean
    simpa only [hconst] using hmean
  have hx0 : x 0=0 := (mul_eq_zero.mp ht).resolve_left (ne_of_gt hZ)
  apply hx
  funext i
  exact (hconst i).trans hx0

lemma weightedSum_single (z : X → ℝ) [DecidableEq X] (i : X) (a : ℝ) :
    weightedSum z (Pi.single i a : X → ℝ)=z i*a := by
  change (∑ j, z j*(Pi.single i a : X → ℝ) j)=_
  simp [Pi.single_apply]

lemma exists_meanZero_nonzero (N : ℕ) (hN : 1 ≤ N) (z : Fin (N+1) → ℝ)
    (hz : ∀ i, 0 < z i) : ∃ x, weightedSum z x=0 ∧ x ≠ 0 := by
  let i : Fin (N+1) := 0
  let j : Fin (N+1) := ⟨1,by omega⟩
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i,j] at this
  let x : Fin (N+1) → ℝ := Pi.single i (z j)-Pi.single j (z i)
  refine ⟨x,?_,?_⟩
  · rw [map_sub,weightedSum_single,weightedSum_single]
    ring
  · intro hx
    have ht := congrFun hx i
    simp only [x,Pi.sub_apply,Pi.single_eq_same,Pi.single_eq_of_ne hij,sub_zero,Pi.zero_apply] at ht
    exact (ne_of_gt (hz j)) ht

lemma quadratic_linear_vanish (a b : ℝ) (ha : 0 ≤ a)
    (h : ∀ t : ℝ, 0 ≤ a*t^2+2*b*t) : b=0 := by
  have ha1 : 0 < a+1 := by linarith
  have hp := mul_nonneg (h (-b/(a+1))) (sq_nonneg (a+1))
  have he : (a*(-b/(a+1))^2+2*b*(-b/(a+1)))*(a+1)^2=-(a+2)*b^2 := by
    field_simp [ne_of_gt ha1]
    ring
  rw [he] at hp
  have hb : b^2=0 := by nlinarith [sq_nonneg b]
  exact sq_eq_zero_iff.mp hb

/-- The Euler identity follows by perturbing the actual minimizing quadratic
energy. The proof uses finite polynomial algebra, without differentiability
or a spectral/Poincare premise. -/
lemma minimizer_stationary_meanZero (N : ℕ) (z : Fin (N+1) → ℝ) (r : ℕ → ℝ)
    (lam : ℝ) (h v : Fin (N+1) → ℝ)
    (hh : weightedSum z h=0) (hv : weightedSum z v=0)
    (hmin : ∀ x, weightedSum z x=0 → lam*weightedSquare z x ≤ pathEnergy N r x)
    (heq : pathEnergy N r h=lam*weightedSquare z h) :
    pathPair N r h v=lam*weightedPair z h v := by
  have ha : 0 ≤ pathEnergy N r v-lam*weightedSquare z v := sub_nonneg.mpr (hmin v hv)
  have hall : ∀ t : ℝ, 0 ≤ (pathEnergy N r v-lam*weightedSquare z v)*t^2+
      2*(pathPair N r h v-lam*weightedPair z h v)*t := by
    intro t
    have hm : weightedSum z (h+t • v)=0 := by rw [map_add,map_smul,hh,hv]; simp
    have ht := hmin (h+t • v) hm
    rw [pathEnergy_add_smul,weightedSquare_add_smul,heq] at ht
    nlinarith only [ht]
  exact sub_eq_zero.mp (quadratic_linear_vanish _ _ ha hall)


noncomputable def centered (z x : X → ℝ) : X → ℝ := fun i => x i-mean z x

lemma weightedSum_centered (z x : X → ℝ) (hz : ∀ i, 0 ≤ z i) :
    weightedSum z (centered z x)=0 := by
  have he := mean_moment z x hz
  change (∑ i, z i*(x i-mean z x))=0
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  linarith

lemma weightedSquare_centered (z x : X → ℝ) :
    weightedSquare z (centered z x)=variance z x := rfl

lemma variance_meanZero (z h : X → ℝ) (hh : weightedSum z h=0) :
    variance z h=weightedSquare z h := by
  change (∑ i, z i*(h i-(∑ j, z j*h j)/(∑ j, z j))^2)=∑ i, z i*(h i)^2
  change (∑ j, z j*h j)=0 at hh
  rw [hh]
  simp

lemma pathEnergy_centered (N : ℕ) (r : ℕ → ℝ) (z x : Fin (N+1) → ℝ) :
    pathEnergy N r (centered z x)=pathEnergy N r x := by
  unfold pathEnergy centered
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma pathPair_centered_right (N : ℕ) (r : ℕ → ℝ) (z h x : Fin (N+1) → ℝ) :
    pathPair N r h (centered z x)=pathPair N r h x := by
  unfold pathPair centered
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma weightedPair_centered_right (z h x : X → ℝ) (hh : weightedSum z h=0) :
    weightedPair z h (centered z x)=weightedPair z h x := by
  have he : weightedPair z h (centered z x)=weightedPair z h x-weightedSum z h*mean z x := by
    unfold weightedPair centered
    change (∑ i, z i*h i*(x i-mean z x))=(∑ i, z i*h i*x i)-
      (∑ i, z i*h i)*mean z x
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,hh]
  ring

lemma minimizer_stationary (N : ℕ) (z : Fin (N+1) → ℝ) (r : ℕ → ℝ)
    (lam : ℝ) (h : Fin (N+1) → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hh : weightedSum z h=0)
    (hmin : ∀ x, weightedSum z x=0 → lam*weightedSquare z x ≤ pathEnergy N r x)
    (heq : pathEnergy N r h=lam*weightedSquare z h) :
    ∀ v, pathPair N r h v=lam*weightedPair z h v := by
  intro v
  have hs := minimizer_stationary_meanZero N z r lam h (centered z v)
    hh (weightedSum_centered z v hz) hmin heq
  rw [pathPair_centered_right,weightedPair_centered_right z h v hh] at hs
  exact hs

noncomputable def prefixIndicator (N : ℕ) (l : Fin N) : Fin (N+1) → ℝ :=
  fun i => if i.val ≤ l.val then 1 else 0

noncomputable def prefixFlux (N : ℕ) (z h : Fin (N+1) → ℝ) (l : Fin N) : ℝ :=
  ∑ i, if i.val ≤ l.val then z i*h i else 0

lemma pathPair_prefixIndicator (N : ℕ) (r : ℕ → ℝ) (h : Fin (N+1) → ℝ) (l : Fin N) :
    pathPair N r h (prefixIndicator N l)=(h l.castSucc-h l.succ)/r (l.val+1) := by
  have he : pathPair N r h (prefixIndicator N l)=
      ∑ j : Fin N, if j=l then (h l.castSucc-h l.succ)/r (l.val+1) else 0 := by
    unfold pathPair
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j=l
    · subst j
      simp [prefixIndicator]
    · have hjv : j.val ≠ l.val := by intro he; exact hj (Fin.ext he)
      by_cases hjl : j.val < l.val
      · simp only [prefixIndicator,Fin.val_castSucc,Fin.val_succ,
          ite_eq_left (show j.val ≤ l.val by omega),
          ite_eq_left (show j.val+1 ≤ l.val by omega),ite_eq_right hj,sub_self,mul_zero,zero_div]
      · simp only [prefixIndicator,Fin.val_castSucc,Fin.val_succ,
          ite_eq_right (show ¬j.val ≤ l.val by omega),
          ite_eq_right (show ¬j.val+1 ≤ l.val by omega),ite_eq_right hj,sub_self,mul_zero,zero_div]
  rw [he]
  simp

lemma weightedPair_prefixIndicator (N : ℕ) (z h : Fin (N+1) → ℝ) (l : Fin N) :
    weightedPair z h (prefixIndicator N l)=prefixFlux N z h l := by
  unfold weightedPair prefixIndicator prefixFlux
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- The prefix test observable turns the variational Euler identity into the
literal path eigenflux identity, with no factor two or mass normalization. -/
lemma minimizer_prefix_flux (N : ℕ) (z : Fin (N+1) → ℝ) (r : ℕ → ℝ)
    (lam : ℝ) (h : Fin (N+1) → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hr : ∀ l : Fin N, 0 < r (l.val+1))
    (hh : weightedSum z h=0)
    (hmin : ∀ x, weightedSum z x=0 → lam*weightedSquare z x ≤ pathEnergy N r x)
    (heq : pathEnergy N r h=lam*weightedSquare z h) :
    ∀ l : Fin N, h l.castSucc-h l.succ=lam*r (l.val+1)*prefixFlux N z h l := by
  intro l
  have hs := minimizer_stationary N z r lam h hz hh hmin heq (prefixIndicator N l)
  rw [pathPair_prefixIndicator,weightedPair_prefixIndicator] at hs
  have ht := (div_eq_iff (ne_of_gt (hr l))).mp hs
  calc
    _ = _ := ht
    _ = _ := by ring

lemma minimizer_universal_variance (N : ℕ) (z : Fin (N+1) → ℝ) (r : ℕ → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (hz : ∀ i, 0 ≤ z i)
    (hmin : ∀ x, weightedSum z x=0 → lam*weightedSquare z x ≤ pathEnergy N r x) :
    ∀ g, variance z g ≤ (1/lam)*pathEnergy N r g := by
  intro g
  have hs := hmin (centered z g) (weightedSum_centered z g hz)
  rw [weightedSquare_centered,pathEnergy_centered] at hs
  calc
    _ ≤ pathEnergy N r g/lam := (le_div_iff₀ hlam).mpr (by simpa only [mul_comm] using hs)
    _ = _ := by ring

/-- Positive finite path resistances have an attained positive Rayleigh
minimizer. Its literal prefix eigenflux controls the original unnormalized
weighted variance of every observable. All spectral statements are conclusions;
only positive weights/resistances and N>=1 are assumed. -/
theorem exists_positive_path_eigenflux (N : ℕ) (hN : 1 ≤ N)
    (z : Fin (N+1) → ℝ) (r : ℕ → ℝ) (hz : ∀ i, 0 < z i)
    (hr : ∀ l : Fin N, 0 < r (l.val+1)) :
    ∃ (lam : ℝ) (h : Fin (N+1) → ℝ), 0 < lam ∧ weightedSum z h=0 ∧ h ≠ 0 ∧
      pathEnergy N r h=lam*variance z h ∧
      (∀ l : Fin N, h l.castSucc-h l.succ=lam*r (l.val+1)*prefixFlux N z h l) ∧
      (∀ g, variance z g ≤ (1/lam)*pathEnergy N r g) := by
  obtain ⟨lam,h,hlam,hhmean,hh0,heq,hmin⟩ := exists_positive_minimizer z (pathEnergy N r)
    hz (pathEnergy_continuous N r) (by simp [pathEnergy])
    (fun t x => pathEnergy_smul N r x t)
    (fun x hxmean hx0 => pathEnergy_positive_meanZero N z r hz hr x hxmean hx0)
    (exists_meanZero_nonzero N hN z hz)
  refine ⟨lam,h,hlam,hhmean,hh0,?_,?_,?_⟩
  · rw [variance_meanZero z h hhmean]
    exact heq
  · exact minimizer_prefix_flux N z r lam h (fun i => (hz i).le) hr hhmean hmin heq
  · exact minimizer_universal_variance N z r lam hlam (fun i => (hz i).le) hmin


/-- The eigenflux equality gives the exact resistance-weighted flux energy.
The path energy counts each edge once. -/
lemma pathEnergy_eq_flux_square (N : ℕ) (r : ℕ → ℝ) (z h : Fin (N+1) → ℝ)
    (lam : ℝ) (hr : ∀ l : Fin N, 0 < r (l.val+1))
    (hflux : ∀ l : Fin N, h l.castSucc-h l.succ=lam*r (l.val+1)*prefixFlux N z h l) :
    pathEnergy N r h=lam^2*(∑ l : Fin N, r (l.val+1)*(prefixFlux N z h l)^2) := by
  unfold pathEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [hflux l]
  field_simp

/-- Explicit attained-Rayleigh API for the original weighted variance, not
merely an unspecified eigenvector. The universal bound is derived by the
compact minimization, not assumed. -/
theorem exists_path_rayleigh_minimizer (N : ℕ) (hN : 1 ≤ N)
    (z : Fin (N+1) → ℝ) (r : ℕ → ℝ) (hz : ∀ i, 0 < z i)
    (hr : ∀ l : Fin N, 0 < r (l.val+1)) :
    ∃ (lam : ℝ) (h : Fin (N+1) → ℝ), 0 < lam ∧ weightedSum z h=0 ∧ h ≠ 0 ∧
      0 < variance z h ∧ lam=pathEnergy N r h/variance z h ∧
      (∀ g, weightedSum z g=0 → g ≠ 0 → lam ≤ pathEnergy N r g/variance z g) ∧
      (∀ l : Fin N, h l.castSucc-h l.succ=lam*r (l.val+1)*prefixFlux N z h l) ∧
      (variance z h=lam*(∑ l : Fin N, r (l.val+1)*(prefixFlux N z h l)^2)) ∧
      (∀ g, variance z g ≤ (1/lam)*pathEnergy N r g) := by
  obtain ⟨lam,h,hlam,hhmean,hh0,heq,hflux,huniv⟩ :=
    exists_positive_path_eigenflux N hN z r hz hr
  have hvar : 0 < variance z h := by
    rw [variance_meanZero z h hhmean]
    exact weightedSquare_positive z h hz hh0
  refine ⟨lam,h,hlam,hhmean,hh0,hvar,?_,?_,hflux,?_,huniv⟩
  · rw [heq]
    exact (mul_div_cancel_right₀ lam (ne_of_gt hvar)).symm
  · intro g hgmean hg0
    have hgv : 0 < variance z g := by
      rw [variance_meanZero z g hgmean]
      exact weightedSquare_positive z g hz hg0
    have hb : variance z g ≤ pathEnergy N r g/lam := by
      convert huniv g using 1
      ring
    have hb' := (le_div_iff₀ hlam).mp hb
    exact (le_div_iff₀ hgv).mpr (by simpa only [mul_comm] using hb')
  · have hf := pathEnergy_eq_flux_square N r z h lam hr hflux
    rw [heq] at hf
    exact mul_left_cancel₀ (ne_of_gt hlam) (by simpa only [pow_two,mul_assoc] using hf)

end Research.SpectralPath

#print axioms Research.SpectralPath.exists_path_rayleigh_minimizer
#check Research.SpectralPath.exists_path_rayleigh_minimizer
