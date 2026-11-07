import Math115.FiniteStarTrace
import OAI.Combinatorics.ContingencyTables.Transport.FiniteChainWeightVariance

namespace Research.WeightedHarmonicTrace

open OAI.ContingencyTables.FiniteExposureVariance
open OAI.CommonBasesFPRAS
open scoped BigOperators Classical

variable {X B D : Type*} [Fintype X] [Fintype B] [Fintype D]

noncomputable def graphEnergy (c : X → X → ℝ) (F : X → ℝ) : ℝ :=
  (∑ x, ∑ y, c x y * (F x - F y) ^ 2) / 2

noncomputable def starMass (S : B → D → ℝ) (b : B) : ℝ := ∑ d, S b d

noncomputable def fullConductance (W : D → D → ℝ) (S : B → D → ℝ) :
    B ⊕ D → B ⊕ D → ℝ
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inl b, Sum.inr d => S b d
  | Sum.inr d, Sum.inl b => S b d
  | Sum.inr d, Sum.inr e => W d e

noncomputable def traceConductance (W : D → D → ℝ) (S : B → D → ℝ) (d e : D) : ℝ :=
  W d e + ∑ b, S b d * S b e / starMass S b

noncomputable def harmonicExtension (S : B → D → ℝ) (g : D → ℝ) : B ⊕ D → ℝ :=
  Sum.elim (fun b => mean (S b) g) g

noncomputable def decomposedEnergy (W : D → D → ℝ) (S : B → D → ℝ) (F : B ⊕ D → ℝ) : ℝ :=
  graphEnergy W (fun d => F (Sum.inr d)) +
    ∑ b, ∑ d, S b d * (F (Sum.inr d) - F (Sum.inl b)) ^ 2

omit [Fintype B] [Fintype D] in
lemma fullConductance_symmetric (W : D → D → ℝ) (S : B → D → ℝ)
    (hW : ∀ d e, W d e = W e d) :
    ∀ x y, fullConductance W S x y = fullConductance W S y x := by
  intro x y
  cases x <;> cases y <;> simp only [fullConductance]
  exact hW _ _

omit [Fintype B] [Fintype D] in
lemma fullConductance_nonnegative (W : D → D → ℝ) (S : B → D → ℝ)
    (hW : ∀ d e, 0 ≤ W d e) (hS : ∀ b d, 0 ≤ S b d) :
    ∀ x y, 0 ≤ fullConductance W S x y := by
  intro x y
  cases x <;> cases y
  · exact le_refl _
  · exact hS _ _
  · exact hS _ _
  · exact hW _ _

omit [Fintype B] [Fintype D] in
/-- Literal accepted conductances identify this block form from symmetry and
zero B-B conductance. Multiple balanced neighbors impose no restriction. -/
theorem fullConductance_of_blocks (c : B ⊕ D → B ⊕ D → ℝ)
    (hsym : ∀ x y, c x y = c y x)
    (hBB : ∀ b b', c (Sum.inl b) (Sum.inl b') = 0) :
    fullConductance (fun d e => c (Sum.inr d) (Sum.inr e))
      (fun b d => c (Sum.inl b) (Sum.inr d)) = c := by
  funext x y
  cases x <;> cases y
  · exact (hBB _ _).symm
  · rfl
  · exact hsym _ _
  · rfl

/-- The full accepted energy is exactly DD energy plus independent weighted
balanced-star energies. Ordered-pair normalization is the existing factor1/2. -/
theorem full_energy_decomposition (W : D → D → ℝ) (S : B → D → ℝ) (F : B ⊕ D → ℝ) :
    graphEnergy (fullConductance W S) F = decomposedEnergy W S F := by
  have hcross : (∑ d, ∑ b, S b d * (F (Sum.inr d) - F (Sum.inl b)) ^ 2) =
      ∑ b, ∑ d, S b d * (F (Sum.inl b) - F (Sum.inr d)) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hflip : (∑ b, ∑ d, S b d * (F (Sum.inl b) - F (Sum.inr d)) ^ 2) =
      ∑ b, ∑ d, S b d * (F (Sum.inr d) - F (Sum.inl b)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    ring
  simp only [graphEnergy, decomposedEnergy, Fintype.sum_sum_type, fullConductance,
    zero_mul, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_add_distrib, hcross, hflip]
  ring

omit [Fintype B] in
lemma weighted_star_energy (S : B → D → ℝ) (b : B) (g : D → ℝ)
    (hS : ∀ d, 0 ≤ S b d) :
    graphEnergy (fun d e => S b d * S b e / starMass S b) g = variance (S b) g := by
  rw [Math115.FiniteStarTrace.variance_eq_pairwise _ _ hS]
  unfold graphEnergy starMass
  simp only [div_mul_eq_mul_div]
  simp_rw [← Finset.sum_div]
  rw [div_div]
  congr 1
  ring

/-- Exact weighted Schur conductance energy, including zero-mass stars. -/
theorem trace_energy_eq_stars (W : D → D → ℝ) (S : B → D → ℝ)
    (hS : ∀ b d, 0 ≤ S b d) (g : D → ℝ) :
    graphEnergy (traceConductance W S) g = graphEnergy W g + ∑ b, variance (S b) g := by
  have hswap : (∑ d, ∑ e, (∑ b, S b d * S b e / starMass S b) * (g d - g e) ^ 2) =
      ∑ b, ∑ d, ∑ e, (S b d * S b e / starMass S b) * (g d - g e) ^ 2 := by
    simp_rw [Finset.sum_mul]
    calc
      _ = ∑ d, ∑ b, ∑ e, (S b d * S b e / starMass S b) * (g d - g e) ^ 2 := by
        apply Finset.sum_congr rfl
        intro d _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hstars : (∑ b, ∑ d, ∑ e, (S b d * S b e / starMass S b) * (g d - g e) ^ 2) / 2 =
      ∑ b, variance (S b) g := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    exact weighted_star_energy S b g (hS b)
  unfold graphEnergy traceConductance
  simp only [add_mul, Finset.sum_add_distrib]
  rw [hswap, add_div, hstars]

/-- Exact harmonic extension energy equals the Schur trace energy. -/
theorem harmonic_energy_eq_trace (W : D → D → ℝ) (S : B → D → ℝ)
    (hS : ∀ b d, 0 ≤ S b d) (g : D → ℝ) :
    graphEnergy (fullConductance W S) (harmonicExtension S g) =
      graphEnergy (traceConductance W S) g := by
  rw [full_energy_decomposition, trace_energy_eq_stars W S hS g]
  rfl

theorem harmonic_energy_min (W : D → D → ℝ) (S : B → D → ℝ)
    (hS : ∀ b d, 0 ≤ S b d) (g : D → ℝ) (h : B → ℝ) :
    graphEnergy (fullConductance W S) (harmonicExtension S g) ≤
      graphEnergy (fullConductance W S) (Sum.elim h g) := by
  rw [full_energy_decomposition, full_energy_decomposition]
  unfold decomposedEnergy harmonicExtension
  simp only [Sum.elim_inr, Sum.elim_inl]
  apply add_le_add (le_refl _)
  apply Finset.sum_le_sum
  intro b _
  exact variance_le_center (S b) g (hS b) (h b)

/-- Restricting to defects decreases unnormalized variance. No full/defect
normalizer ratio occurs; the balanced values can be arbitrary. -/
theorem variance_restrict_le (wB : B → ℝ) (wD : D → ℝ)
    (hwB : ∀ b, 0 ≤ wB b) (hwD : ∀ d, 0 ≤ wD d) (h : B → ℝ) (g : D → ℝ) :
    variance wD g ≤ variance (Sum.elim wB wD) (Sum.elim h g) := by
  let a := mean (Sum.elim wB wD) (Sum.elim h g)
  have hc := variance_le_center wD g hwD a
  have hb : 0 ≤ ∑ b, wB b * (h b - a) ^ 2 :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (hwB b) (sq_nonneg _))
  calc
    _ ≤ ∑ d, wD d * (g d - a) ^ 2 := hc
    _ ≤ (∑ b, wB b * (h b - a) ^ 2) + ∑ d, wD d * (g d - a) ^ 2 := le_add_of_nonneg_left hb
    _ = _ := by
      unfold variance
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, a]

/-- Transfer from a supplied genuine full minimum-weight graph inequality
and its accepted-energy comparison, not an assumed trace spectral conclusion. -/
theorem unnormalized_poincare_transfer (wB : B → ℝ) (wD : D → ℝ)
    (hwB : ∀ b, 0 ≤ wB b) (hwD : ∀ d, 0 ≤ wD d)
    (W : D → D → ℝ) (S : B → D → ℝ) (hS : ∀ b d, 0 ≤ S b d)
    (Emin : (B ⊕ D → ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hfull : ∀ F, variance (Sum.elim wB wD) F ≤ C * Emin F)
    (haccept : ∀ F, Emin F ≤ 2 * graphEnergy (fullConductance W S) F) (g : D → ℝ) :
    variance wD g ≤ 2 * C * graphEnergy (traceConductance W S) g := by
  have hv := variance_restrict_le wB wD hwB hwD (fun b => mean (S b) g) g
  have hf := hfull (harmonicExtension S g)
  have he := mul_le_mul_of_nonneg_left (haccept (harmonicExtension S g)) hC
  rw [harmonic_energy_eq_trace W S hS g] at he
  exact hv.trans (hf.trans (by simpa only [mul_assoc, mul_comm, mul_left_comm] using he))


lemma graphEnergy_nonnegative (c : X → X → ℝ) (hc : ∀ x y, 0 ≤ c x y) (F : X → ℝ) :
    0 ≤ graphEnergy c F := by
  apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Finset.sum_nonneg
  intro x _
  exact Finset.sum_nonneg (fun y _ => mul_nonneg (hc x y) (sq_nonneg _))

/-- Pointwise directed half acceptance on the actual min-weight edge matrix
implies the unnormalized accepted-energy bridge. Offedges may have M=0. -/
theorem half_matrix_energy_comparison (M A : X → X → ℝ)
    (hhalf : ∀ x y, M x y / 2 ≤ A x y) (F : X → ℝ) :
    graphEnergy M F ≤ 2 * graphEnergy A F := by
  have hsum : (∑ x, ∑ y, M x y * (F x - F y) ^ 2) ≤
      2 * (∑ x, ∑ y, A x y * (F x - F y) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    have h := mul_le_mul_of_nonneg_right (show M x y ≤ 2 * A x y by linarith only [hhalf x y])
      (sq_nonneg (F x - F y))
    simpa only [mul_assoc] using h
  unfold graphEnergy
  exact (div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

omit [Fintype B] in
lemma starMass_nonnegative (S : B → D → ℝ) (hS : ∀ b d, 0 ≤ S b d) (b : B) :
    0 ≤ starMass S b := Finset.sum_nonneg (fun d _ => hS b d)

lemma traceConductance_nonnegative (W : D → D → ℝ) (S : B → D → ℝ)
    (hW : ∀ d e, 0 ≤ W d e) (hS : ∀ b d, 0 ≤ S b d) (d e : D) :
    0 ≤ traceConductance W S d e := by
  apply add_nonneg (hW d e)
  exact Finset.sum_nonneg (fun b _ => div_nonneg (mul_nonneg (hS b d) (hS b e))
    (starMass_nonnegative S hS b))

lemma traceConductance_symmetric (W : D → D → ℝ) (S : B → D → ℝ)
    (hW : ∀ d e, W d e = W e d) (d e : D) :
    traceConductance W S d e = traceConductance W S e d := by
  unfold traceConductance
  rw [hW]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [Fintype B] in
/-- Each weighted star's full row mass is its incident conductance. The
zero-mass case uses nonnegative weights to prove every incident value zero. -/
lemma star_row_sum (S : B → D → ℝ) (hS : ∀ b d, 0 ≤ S b d) (b : B) (d : D) :
    (∑ e, S b d * S b e / starMass S b) = S b d := by
  by_cases hm : starMass S b = 0
  · have hz := zero_mass_weights (S b) (hS b) (by simpa only [starMass] using hm)
    simp only [hz, zero_mul, zero_div, Finset.sum_const_zero]
  · rw [← Finset.sum_div, ← Finset.mul_sum]
    change S b d * starMass S b / starMass S b = S b d
    exact mul_div_cancel_right₀ _ hm

/-- Trace row mass includes all star returns to the starting defect. Omitting
its diagonal therefore only decreases the row; shared balanced centers add. -/
theorem traceConductance_row_sum (W : D → D → ℝ) (S : B → D → ℝ)
    (hS : ∀ b d, 0 ≤ S b d) (d : D) :
    (∑ e, traceConductance W S d e) = (∑ e, W d e) + ∑ b, S b d := by
  unfold traceConductance
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact star_row_sum S hS b d

section Chain
variable [Nonempty D]

noncomputable def defectMass (w : D → ℝ) : ℝ := ∑ d, w d

lemma defectMass_positive (w : D → ℝ) (hw : ∀ d, 0 < w d) : 0 < defectMass w :=
  Finset.sum_pos (fun d _ => hw d) Finset.univ_nonempty

noncomputable def traceMove (w : D → ℝ) (W : D → D → ℝ) (S : B → D → ℝ)
    (beta : ℝ) (d e : D) : ℝ :=
  if d = e then 0 else beta * traceConductance W S d e / w d

omit [Nonempty D] in
lemma traceMove_nonnegative (w : D → ℝ) (W : D → D → ℝ) (S : B → D → ℝ)
    (hw : ∀ d, 0 < w d) (hW : ∀ d e, 0 ≤ W d e) (hS : ∀ b d, 0 ≤ S b d)
    (beta : ℝ) (hb : 0 ≤ beta) : ∀ d e, 0 ≤ traceMove w W S beta d e := by
  intro d e
  unfold traceMove
  split_ifs
  · exact le_refl _
  · exact div_nonneg (mul_nonneg hb (traceConductance_nonnegative W S hW hS d e)) (hw d).le

omit [Nonempty D] in
/-- Only defect-source row capacity is needed; balanced rows need no degree
budget because their centers are eliminated rather than clocked as a chain. -/
lemma traceMove_row_bound (w : D → ℝ) (W : D → D → ℝ) (S : B → D → ℝ)
    (hw : ∀ d, 0 < w d) (hW : ∀ d e, 0 ≤ W d e) (hS : ∀ b d, 0 ≤ S b d)
    (beta : ℝ) (hb : 0 ≤ beta) (Q : ℕ)
    (hrow : ∀ d, (∑ e, W d e) + (∑ b, S b d) ≤ (Q : ℝ) * w d)
    (hscale : beta * (Q : ℝ) ≤ 1 / 2) : ∀ d, (∑ e, traceMove w W S beta d e) ≤ 1 / 2 := by
  intro d
  have ht : (∑ e, traceConductance W S d e) ≤ (Q : ℝ) * w d := by
    rw [traceConductance_row_sum W S hS d]
    exact hrow d
  calc
    _ ≤ ∑ e, beta * traceConductance W S d e / w d := by
      apply Finset.sum_le_sum
      intro e _
      unfold traceMove
      split_ifs
      · exact div_nonneg (mul_nonneg hb (traceConductance_nonnegative W S hW hS d e)) (hw d).le
      · exact le_refl _
    _ = (beta / w d) * (∑ e, traceConductance W S d e) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ (beta / w d) * ((Q : ℝ) * w d) :=
      mul_le_mul_of_nonneg_left ht (div_nonneg hb (hw d).le)
    _ = beta * (Q : ℝ) := by field_simp [ne_of_gt (hw d)]
    _ ≤ _ := hscale

lemma traceMove_reversible (w : D → ℝ) (W : D → D → ℝ) (S : B → D → ℝ)
    (hw : ∀ d, 0 < w d) (hW : ∀ d e, W d e = W e d) (beta : ℝ) (d e : D) :
    (w d / defectMass w) * traceMove w W S beta d e =
      (w e / defectMass w) * traceMove w W S beta e d := by
  by_cases he : d = e
  · subst e
    rfl
  · simp only [traceMove, he, Ne.symm he, ite_false]
    rw [traceConductance_symmetric W S hW d e]
    field_simp [ne_of_gt (hw d), ne_of_gt (hw e), ne_of_gt (defectMass_positive w hw)]

/-- The actual finite lazy reversible weighted Schur trace. Its move diagonal
is zero; the omitted star-return mass becomes holding probability. -/
noncomputable def traceChain (w : D → ℝ) (W : D → D → ℝ) (S : B → D → ℝ)
    (hw : ∀ d, 0 < w d) (hW : ∀ d e, 0 ≤ W d e) (hWsym : ∀ d e, W d e = W e d)
    (hS : ∀ b d, 0 ≤ S b d) (beta : ℝ) (hb : 0 ≤ beta) (Q : ℕ)
    (hrow : ∀ d, (∑ e, W d e) + (∑ b, S b d) ≤ (Q : ℝ) * w d)
    (hscale : beta * (Q : ℝ) ≤ 1 / 2) : FiniteChain D :=
  FiniteChain.ofMoves (fun d => w d / defectMass w) (traceMove w W S beta)
    (fun d => div_pos (hw d) (defectMass_positive w hw))
    (by rw [← Finset.sum_div]; exact div_self (ne_of_gt (defectMass_positive w hw)))
    (traceMove_nonnegative w W S hw hW hS beta hb)
    (traceMove_row_bound w W S hw hW hS beta hb Q hrow hscale)
    (traceMove_reversible w W S hw hWsym beta)

/-- Exact trace normalization: no full-state partition-function ratio or
extra star-elimination factor appears. -/
theorem traceChain_energy (w : D → ℝ) (W : D → D → ℝ) (S : B → D → ℝ)
    (hw : ∀ d, 0 < w d) (hW : ∀ d e, 0 ≤ W d e) (hWsym : ∀ d e, W d e = W e d)
    (hS : ∀ b d, 0 ≤ S b d) (beta : ℝ) (hb : 0 ≤ beta) (Q : ℕ)
    (hrow : ∀ d, (∑ e, W d e) + (∑ b, S b d) ≤ (Q : ℝ) * w d)
    (hscale : beta * (Q : ℝ) ≤ 1 / 2) (g : D → ℝ) :
    (traceChain w W S hw hW hWsym hS beta hb Q hrow hscale).energy g =
      (beta / defectMass w) * graphEnergy (traceConductance W S) g := by
  have hp (d e : D) : (w d / defectMass w) * traceMove w W S beta d e * (g d - g e) ^ 2 =
      (beta / defectMass w) * (traceConductance W S d e * (g d - g e) ^ 2) := by
    by_cases he : d = e
    · subst e
      simp
    · simp only [traceMove, he, ite_false]
      field_simp [ne_of_gt (hw d)]
  unfold traceChain
  rw [FiniteChain.ofMoves_energy]
  simp_rw [hp]
  unfold graphEnergy
  simp_rw [← Finset.mul_sum]
  ring

/-- Full weighted graph variance and the actual accepted-energy bridge imply
the normalized defect trace Poincare bound, for its constructed finite chain. -/
theorem normalized_poincare_transfer (wB : B → ℝ) (w : D → ℝ)
    (hwB : ∀ b, 0 ≤ wB b) (hw : ∀ d, 0 < w d)
    (W : D → D → ℝ) (S : B → D → ℝ) (hW : ∀ d e, 0 ≤ W d e)
    (hWsym : ∀ d e, W d e = W e d) (hS : ∀ b d, 0 ≤ S b d)
    (beta : ℝ) (hb : 0 < beta) (Q : ℕ)
    (hrow : ∀ d, (∑ e, W d e) + (∑ b, S b d) ≤ (Q : ℝ) * w d)
    (hscale : beta * (Q : ℝ) ≤ 1 / 2)
    (Emin : (B ⊕ D → ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hfull : ∀ F, variance (Sum.elim wB w) F ≤ C * Emin F)
    (haccept : ∀ F, Emin F ≤ 2 * graphEnergy (fullConductance W S) F) (g : D → ℝ) :
    (traceChain w W S hw hW hWsym hS beta hb.le Q hrow hscale).variance g ≤
      (2 * C / beta) * (traceChain w W S hw hW hWsym hS beta hb.le Q hrow hscale).energy g := by
  have hv := unnormalized_poincare_transfer wB w hwB (fun d => (hw d).le)
    W S hS Emin C hC hfull haccept g
  have hZ := defectMass_positive w hw
  rw [chain_variance_eq _ w g (fun _ => rfl)]
  calc
    _ ≤ (2 * C * graphEnergy (traceConductance W S) g) / defectMass w :=
      div_le_div_of_nonneg_right hv hZ.le
    _ = (2 * C / beta) * ((beta / defectMass w) * graphEnergy (traceConductance W S) g) := by
      field_simp [ne_of_gt hb, ne_of_gt hZ]
    _ = _ := by rw [traceChain_energy]

/-- Pointwise half acceptance on a specified actual minimum-weight edge
matrix supplies the energy bridge; no trace spectral conclusion is an input. -/
theorem normalized_poincare_of_half_matrix (wB : B → ℝ) (w : D → ℝ)
    (hwB : ∀ b, 0 ≤ wB b) (hw : ∀ d, 0 < w d)
    (W : D → D → ℝ) (S : B → D → ℝ) (hW : ∀ d e, 0 ≤ W d e)
    (hWsym : ∀ d e, W d e = W e d) (hS : ∀ b d, 0 ≤ S b d)
    (beta : ℝ) (hb : 0 < beta) (Q : ℕ)
    (hrow : ∀ d, (∑ e, W d e) + (∑ b, S b d) ≤ (Q : ℝ) * w d)
    (hscale : beta * (Q : ℝ) ≤ 1 / 2)
    (M : B ⊕ D → B ⊕ D → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hfull : ∀ F, variance (Sum.elim wB w) F ≤ C * graphEnergy M F)
    (hhalf : ∀ x y, M x y / 2 ≤ fullConductance W S x y) (g : D → ℝ) :
    (traceChain w W S hw hW hWsym hS beta hb.le Q hrow hscale).variance g ≤
      (2 * C / beta) * (traceChain w W S hw hW hWsym hS beta hb.le Q hrow hscale).energy g :=
  normalized_poincare_transfer wB w hwB hw W S hW hWsym hS beta hb Q hrow hscale
    (graphEnergy M) C hC hfull (half_matrix_energy_comparison M _ hhalf) g


lemma rational_proposal_positive (Q : ℕ) (hQ : 1 ≤ Q) : 0 < 1 / (2 * (Q : ℝ)) := by
  have hqr : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  positivity

lemma rational_proposal_half (Q : ℕ) (hQ : 1 ≤ Q) :
    (1 / (2 * (Q : ℝ))) * (Q : ℝ) = 1 / 2 := by
  have hqr : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  field_simp [ne_of_gt hqr]

noncomputable def rationalChain (w : D → ℝ) (W : D → D → ℝ) (S : B → D → ℝ)
    (hw : ∀ d, 0 < w d) (hW : ∀ d e, 0 ≤ W d e) (hWsym : ∀ d e, W d e = W e d)
    (hS : ∀ b d, 0 ≤ S b d) (Q : ℕ) (hQ : 1 ≤ Q)
    (hrow : ∀ d, (∑ e, W d e) + (∑ b, S b d) ≤ (Q : ℝ) * w d) : FiniteChain D :=
  traceChain w W S hw hW hWsym hS (1 / (2 * (Q : ℝ)))
    (rational_proposal_positive Q hQ).le Q hrow (rational_proposal_half Q hQ).le

/-- At the exact rational defect proposal1/(2Q), the normalized trace
constant is4QC. All full graph and local acceptance premises are explicit. -/
theorem rational_poincare_transfer (wB : B → ℝ) (w : D → ℝ)
    (hwB : ∀ b, 0 ≤ wB b) (hw : ∀ d, 0 < w d)
    (W : D → D → ℝ) (S : B → D → ℝ) (hW : ∀ d e, 0 ≤ W d e)
    (hWsym : ∀ d e, W d e = W e d) (hS : ∀ b d, 0 ≤ S b d)
    (Q : ℕ) (hQ : 1 ≤ Q)
    (hrow : ∀ d, (∑ e, W d e) + (∑ b, S b d) ≤ (Q : ℝ) * w d)
    (M : B ⊕ D → B ⊕ D → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hfull : ∀ F, variance (Sum.elim wB w) F ≤ C * graphEnergy M F)
    (hhalf : ∀ x y, M x y / 2 ≤ fullConductance W S x y) (g : D → ℝ) :
    (rationalChain w W S hw hW hWsym hS Q hQ hrow).variance g ≤
      (4 * (Q : ℝ) * C) * (rationalChain w W S hw hW hWsym hS Q hQ hrow).energy g := by
  have h := normalized_poincare_of_half_matrix wB w hwB hw W S hW hWsym hS
    (1 / (2 * (Q : ℝ))) (rational_proposal_positive Q hQ) Q hrow
    (rational_proposal_half Q hQ).le M C hC hfull hhalf g
  have hid : 2 * C / (1 / (2 * (Q : ℝ))) = 4 * (Q : ℝ) * C := by
    simp only [div_div_eq_mul_div, div_one]
    ring
  rw [hid] at h
  exact h

/-- Conditional physical-width envelope for the actual constructed normalized
trace chain. The full-state variance and geometric accepted row budget remain
visible premises for the physical adapter to discharge. -/
theorem width_square_rational_trace (wB : B → ℝ) (w : D → ℝ)
    (hwB : ∀ b, 0 ≤ wB b) (hw : ∀ d, 0 < w d)
    (W : D → D → ℝ) (S : B → D → ℝ) (hW : ∀ d e, 0 ≤ W d e)
    (hWsym : ∀ d e, W d e = W e d) (hS : ∀ b d, 0 ≤ S b d)
    (p U Q : ℕ) (hQ : 1 ≤ Q) (hQp : Q ≤ 4 * p - 3)
    (hrow : ∀ d, (∑ e, W d e) + (∑ b, S b d) ≤ (Q : ℝ) * w d)
    (M : B ⊕ D → B ⊕ D → ℝ)
    (hfull : ∀ F, variance (Sum.elim wB w) F ≤ (2 * (p : ℝ) ^ 3 * (U : ℝ) ^ 2) * graphEnergy M F)
    (hhalf : ∀ x y, M x y / 2 ≤ fullConductance W S x y) (g : D → ℝ) :
    (rationalChain w W S hw hW hWsym hS Q hQ hrow).variance g ≤
      (32 * (p : ℝ) ^ 4 * (U : ℝ) ^ 2) *
        (rationalChain w W S hw hW hWsym hS Q hQ hrow).energy g := by
  have h := rational_poincare_transfer wB w hwB hw W S hW hWsym hS Q hQ hrow M
    (2 * (p : ℝ) ^ 3 * (U : ℝ) ^ 2) (by positivity) hfull hhalf g
  have hqp : (Q : ℝ) ≤ 4 * (p : ℝ) := by exact_mod_cast hQp.trans (Nat.sub_le _ _)
  have hc : 4 * (Q : ℝ) * (2 * (p : ℝ) ^ 3 * (U : ℝ) ^ 2) ≤
      32 * (p : ℝ) ^ 4 * (U : ℝ) ^ 2 := by
    calc
      _ ≤ 4 * (4 * (p : ℝ)) * (2 * (p : ℝ) ^ 3 * (U : ℝ) ^ 2) := by gcongr
      _ = _ := by ring
  exact h.trans (mul_le_mul_of_nonneg_right hc (FiniteChain.energy_nonneg _ g))

end Chain
end Research.WeightedHarmonicTrace
