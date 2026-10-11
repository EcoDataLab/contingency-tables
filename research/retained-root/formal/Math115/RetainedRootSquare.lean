import Math115.RetainedRoot

namespace Math115.RetainedRootSquare

noncomputable def squareCoefficient (a b u x y : ℝ) : ℝ :=
  2 * u ^ 2 / (a * b) - (u - a * x) ^ 2 / a ^ 2 - (u + b * y) ^ 2 / b ^ 2

/-- Exact right-oriented negative-square identity. No ordering or eigenmode
hypothesis is needed for this algebraic identity. -/
theorem right_negative_square (a b u x y : ℝ) (ha : 0 < a) (hb : 0 < b) :
    b * squareCoefficient a b u x y - 2 * u * (x - y) =
      -(u * (b - a) / a - b * x) ^ 2 / b - b * y ^ 2 := by
  unfold squareCoefficient
  field_simp
  ring

theorem left_negative_square (a b u x y : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a * squareCoefficient a b u x y - 2 * u * (x - y) =
      -(u * (a - b) / b + a * y) ^ 2 / a - a * x ^ 2 := by
  unfold squareCoefficient
  field_simp
  ring

theorem maximum_square_coefficient (a b u x y : ℝ) (ha : 0 < a) (hb : 0 < b) :
    max a b * squareCoefficient a b u x y ≤ 2 * u * (x - y) := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    have h := right_negative_square a b u x y ha hb
    simp only [neg_div] at h
    have hsq : 0 ≤ (u * (b - a) / a - b * x) ^ 2 / b := by positivity
    have hy : 0 ≤ b * y ^ 2 := by positivity
    linarith
  · rw [max_eq_left hba]
    have h := left_negative_square a b u x y ha hb
    simp only [neg_div] at h
    have hsq : 0 ≤ (u * (a - b) / b + a * y) ^ 2 / a := by positivity
    have hx : 0 ≤ a * x ^ 2 := by positivity
    linarith

/-- Local correction cap valid on both signs of the retained coefficient.
The moment cap and positivity derive K≥0; no global path inequality is assumed. -/
theorem capped_square_coefficient (a b u x y c K : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 ≤ c) (hcap : c ≤ K * max a b) (hflux : 0 ≤ u * (x - y)) :
    c * squareCoefficient a b u x y ≤ 2 * K * (u * (x - y)) := by
  have hK := Math115.RetainedRoot.cap_constant_nonnegative a b c K ha hb hc hcap
  by_cases hD : squareCoefficient a b u x y ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos hc hD).trans (by positivity)
  · have hD0 : 0 ≤ squareCoefficient a b u x y := (lt_of_not_ge hD).le
    calc
      _ ≤ (K * max a b) * squareCoefficient a b u x y := mul_le_mul_of_nonneg_right hcap hD0
      _ = K * (max a b * squareCoefficient a b u x y) := by ring
      _ ≤ K * (2 * u * (x - y)) :=
        mul_le_mul_of_nonneg_left (maximum_square_coefficient a b u x y ha hb) hK
      _ = _ := by ring

/-- An actual nonnegative eigenvalue/resistance flux relation gives the
needed sign even when the minimizing eigenfunction changes direction. -/
theorem flux_nonnegative (u x y lambda rho : ℝ) (hl : 0 ≤ lambda) (hr : 0 ≤ rho)
    (hflux : x - y = lambda * rho * u) : 0 ≤ u * (x - y) := by
  rw [hflux]
  have hid : u * (lambda * rho * u) = lambda * rho * u ^ 2 := by ring
  rw [hid]
  positivity

theorem capped_square_coefficient_of_flux (a b u x y c K lambda rho : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hcap : c ≤ K * max a b)
    (hl : 0 ≤ lambda) (hr : 0 ≤ rho) (hflux : x - y = lambda * rho * u) :
    c * squareCoefficient a b u x y ≤ 2 * K * (u * (x - y)) :=
  capped_square_coefficient a b u x y c K ha hb hc hcap
    (flux_nonnegative u x y lambda rho hl hr hflux)

/-- The unrestricted exterior corrections retain their actual nonpositive
sign. No bound on the exterior moments is imposed. -/
theorem exterior_correction_nonpos (c u z : ℝ) (hc : 0 ≤ c) :
    -c * u ^ 2 / z ^ 2 ≤ 0 := by
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg u]) (sq_nonneg z)

/-- Candidate scalar context coefficient. Its use for physical variance
requires the separately proved sharp path transport and moment-cap assembly. -/
noncomputable def transversalCoefficient (p V : ℕ) : ℝ :=
  (V : ℝ) * ((V : ℝ) + 1) + 2 * ((p - 1 : ℕ) : ℝ) * Math115.RetainedRoot.quarterProduct V

noncomputable def fullCoefficient (p V : ℕ) : ℝ :=
  transversalCoefficient p V + (Real.sqrt ((p : ℝ) ^ 2 * transversalCoefficient p V) + 1) ^ 2

theorem transversal_bounds (p V : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V) :
    6 ≤ transversalCoefficient p V ∧ transversalCoefficient p V ≤ (5 / 4 : ℝ) * p * (V : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : 0 ≤ (p : ℝ) - 1 := by linarith only [hpR]
  have hVR : (2 : ℝ) ≤ V := by exact_mod_cast hV
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hq := Math115.RetainedRoot.quarterProduct_bound V hV
  have hm := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2 * ((p : ℝ) - 1) by positivity)
  unfold transversalCoefficient
  rw [hcast]
  constructor
  · have hn : 0 ≤ 2 * ((p : ℝ) - 1) * (Math115.RetainedRoot.quarterProduct V : ℝ) := by positivity
    nlinarith only [hn, hVR, sq_nonneg ((V : ℝ) - 2)]
  · have hwidth : (V : ℝ) ≤ (V : ℝ) ^ 2 / 2 := by
      have hv2 : 0 ≤ (V : ℝ) - 2 := by linarith only [hVR]
      have hpoly : 0 ≤ (V : ℝ) * ((V : ℝ) - 2) := by positivity
      nlinarith only [hpoly]
    have hpquarter : (1 / 2 : ℝ) * (V : ℝ) ^ 2 ≤ (1 / 4 : ℝ) * p * (V : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (by linarith only [hpR]) (sq_nonneg (V : ℝ))
    nlinarith only [hm, hwidth, hpquarter]

theorem fullCoefficient_bound (p V : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V) :
    fullCoefficient p V ≤ (5 / 2 : ℝ) * (p : ℝ) ^ 3 * (V : ℝ) ^ 2 := by
  have ht := transversal_bounds p V hp hV
  unfold fullCoefficient
  calc
    _ ≤ 2 * (p : ℝ) ^ 2 * transversalCoefficient p V :=
      Math115.RetainedRoot.repair_coefficient_bound p _ hp ht.1
    _ ≤ 2 * (p : ℝ) ^ 2 * ((5 / 4 : ℝ) * p * (V : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left ht.2 (by positivity)
    _ = _ := by ring

/-- Scalar rational trace envelope only. The use of this new coefficient in
an actual physical trace is an additional premise of its global assembly. -/
theorem rational_trace_bound (p V Q : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V) (hQ : Q ≤ 4 * p - 3) :
    4 * (Q : ℝ) * fullCoefficient p V ≤ 40 * (p : ℝ) ^ 4 * (V : ℝ) ^ 2 := by
  have hq : (Q : ℝ) ≤ 4 * (p : ℝ) := by exact_mod_cast hQ.trans (Nat.sub_le _ _)
  calc
    _ ≤ 4 * (Q : ℝ) * ((5 / 2 : ℝ) * (p : ℝ) ^ 3 * (V : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (fullCoefficient_bound p V hp hV) (by positivity)
    _ ≤ 4 * (4 * (p : ℝ)) * ((5 / 2 : ℝ) * (p : ℝ) ^ 3 * (V : ℝ) ^ 2) := by gcongr
    _ = _ := by ring

theorem dyadic_trace_bound (p V Q : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQpos : 1 ≤ Q) (hQ : Q ≤ 4 * p - 3) :
    2 * (Math115.RetainedRoot.dyadicDenominator Q : ℝ) * fullCoefficient p V ≤
      80 * (p : ℝ) ^ 4 * (V : ℝ) ^ 2 := by
  have hd : (Math115.RetainedRoot.dyadicDenominator Q : ℝ) ≤ 4 * (Q : ℝ) := by
    exact_mod_cast (Math115.RetainedRoot.dyadicDenominator_bounds Q hQpos).2.le
  have hq : (Q : ℝ) ≤ 4 * (p : ℝ) := by exact_mod_cast hQ.trans (Nat.sub_le _ _)
  have hdp : (Math115.RetainedRoot.dyadicDenominator Q : ℝ) ≤ 16 * (p : ℝ) := by linarith only [hd, hq]
  calc
    _ ≤ 2 * (Math115.RetainedRoot.dyadicDenominator Q : ℝ) *
        ((5 / 2 : ℝ) * (p : ℝ) ^ 3 * (V : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (fullCoefficient_bound p V hp hV) (by positivity)
    _ ≤ 2 * (16 * (p : ℝ)) * ((5 / 2 : ℝ) * (p : ℝ) ^ 3 * (V : ℝ) ^ 2) := by gcongr
    _ = _ := by ring

theorem rational_uniform_d8 (p V Q d : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQ : Q ≤ 4 * p - 3) (hpd : p ≤ d) (hVd : V ≤ 11 * d ^ 2) :
    4 * (Q : ℝ) * fullCoefficient p V ≤ 4840 * (d : ℝ) ^ 8 := by
  have hpR : (p : ℝ) ≤ d := by exact_mod_cast hpd
  have hVR : (V : ℝ) ≤ 11 * (d : ℝ) ^ 2 := by exact_mod_cast hVd
  calc
    _ ≤ 40 * (p : ℝ) ^ 4 * (V : ℝ) ^ 2 := rational_trace_bound p V Q hp hV hQ
    _ ≤ 40 * (d : ℝ) ^ 4 * (11 * (d : ℝ) ^ 2) ^ 2 := by gcongr
    _ = _ := by ring

theorem dyadic_uniform_d8 (p V Q d : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQpos : 1 ≤ Q) (hQ : Q ≤ 4 * p - 3) (hpd : p ≤ d) (hVd : V ≤ 11 * d ^ 2) :
    2 * (Math115.RetainedRoot.dyadicDenominator Q : ℝ) * fullCoefficient p V ≤ 9680 * (d : ℝ) ^ 8 := by
  have hpR : (p : ℝ) ≤ d := by exact_mod_cast hpd
  have hVR : (V : ℝ) ≤ 11 * (d : ℝ) ^ 2 := by exact_mod_cast hVd
  calc
    _ ≤ 80 * (p : ℝ) ^ 4 * (V : ℝ) ^ 2 := dyadic_trace_bound p V Q hp hV hQpos hQ
    _ ≤ 80 * (d : ℝ) ^ 4 * (11 * (d : ℝ) ^ 2) ^ 2 := by gcongr
    _ = _ := by ring

theorem rational_shape_d6 (p V Q d s : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQ : Q ≤ 4 * p - 3) (hpd : p ≤ d) (hVd : V ≤ 11 * d * s) :
    4 * (Q : ℝ) * fullCoefficient p V ≤ 4840 * (d : ℝ) ^ 6 * (s : ℝ) ^ 2 := by
  have hpR : (p : ℝ) ≤ d := by exact_mod_cast hpd
  have hVR : (V : ℝ) ≤ 11 * (d : ℝ) * s := by exact_mod_cast hVd
  calc
    _ ≤ 40 * (p : ℝ) ^ 4 * (V : ℝ) ^ 2 := rational_trace_bound p V Q hp hV hQ
    _ ≤ 40 * (d : ℝ) ^ 4 * (11 * (d : ℝ) * s) ^ 2 := by gcongr
    _ = _ := by ring

theorem dyadic_shape_d6 (p V Q d s : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQpos : 1 ≤ Q) (hQ : Q ≤ 4 * p - 3) (hpd : p ≤ d) (hVd : V ≤ 11 * d * s) :
    2 * (Math115.RetainedRoot.dyadicDenominator Q : ℝ) * fullCoefficient p V ≤
      9680 * (d : ℝ) ^ 6 * (s : ℝ) ^ 2 := by
  have hpR : (p : ℝ) ≤ d := by exact_mod_cast hpd
  have hVR : (V : ℝ) ≤ 11 * (d : ℝ) * s := by exact_mod_cast hVd
  calc
    _ ≤ 80 * (p : ℝ) ^ 4 * (V : ℝ) ^ 2 := dyadic_trace_bound p V Q hp hV hQpos hQ
    _ ≤ 80 * (d : ℝ) ^ 4 * (11 * (d : ℝ) * s) ^ 2 := by gcongr
    _ = _ := by ring


/-- Tight candidate coefficient: its physical use requires the separately
verified support diameter N≤V−1, made explicit by support_coefficient_bound. -/
noncomputable def tightTransversalCoefficient (p V : ℕ) : ℝ :=
  ((V - 1 : ℕ) : ℝ) * V + 2 * ((p - 1 : ℕ) : ℝ) * Math115.RetainedRoot.quarterProduct V

noncomputable def tightFullCoefficient (p V : ℕ) : ℝ :=
  tightTransversalCoefficient p V + (Real.sqrt ((p : ℝ) ^ 2 * tightTransversalCoefficient p V) + 1) ^ 2

/-- The actual-support scalar input needed before replacing the safe context
coefficient by the tight one. This does not construct physical child support. -/
theorem support_coefficient_bound (p V N : ℕ) (hN : N ≤ V - 1) (hV : 1 ≤ V) :
    (N : ℝ) * ((N : ℝ) + 1) + 2 * ((p - 1 : ℕ) : ℝ) * Math115.RetainedRoot.quarterProduct V ≤
      tightTransversalCoefficient p V := by
  have hN' : (N : ℝ) ≤ (V - 1 : ℕ) := by exact_mod_cast hN
  have hN1 : (N : ℝ) + 1 ≤ V := by exact_mod_cast (show N + 1 ≤ V by omega)
  unfold tightTransversalCoefficient
  exact add_le_add (mul_le_mul hN' hN1 (by positivity) (by positivity)) (le_refl _)

theorem quarterProduct_lower (V : ℕ) (hV : 2 ≤ V) :
    2 ≤ Math115.RetainedRoot.quarterProduct V := by
  unfold Math115.RetainedRoot.quarterProduct
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr
  nlinarith

theorem tight_transversal_bounds (p V : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V) :
    6 ≤ tightTransversalCoefficient p V ∧ tightTransversalCoefficient p V ≤ (p : ℝ) * (V : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hVR : (2 : ℝ) ≤ V := by exact_mod_cast hV
  have hp1 : 0 ≤ (p : ℝ) - 1 := by linarith only [hpR]
  have hpcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hvcast : ((V - 1 : ℕ) : ℝ) = (V : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hq := Math115.RetainedRoot.quarterProduct_bound V hV
  have hqlo : (2 : ℝ) ≤ Math115.RetainedRoot.quarterProduct V := by exact_mod_cast quarterProduct_lower V hV
  have hmul := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2 * ((p : ℝ) - 1) by positivity)
  unfold tightTransversalCoefficient
  rw [hpcast, hvcast]
  constructor
  · have hbase : 2 ≤ ((V : ℝ) - 1) * V := by nlinarith only [hVR, sq_nonneg ((V : ℝ) - 2)]
    have hmoment := mul_le_mul_of_nonneg_right (show 1 ≤ (p : ℝ) - 1 by linarith only [hpR])
      (show 0 ≤ (Math115.RetainedRoot.quarterProduct V : ℝ) by positivity)
    nlinarith only [hbase, hmoment, hqlo]
  · nlinarith only [hmul, hVR]

theorem tight_fullCoefficient_bound (p V : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V) :
    tightFullCoefficient p V ≤ 2 * (p : ℝ) ^ 3 * (V : ℝ) ^ 2 := by
  have ht := tight_transversal_bounds p V hp hV
  unfold tightFullCoefficient
  calc
    _ ≤ 2 * (p : ℝ) ^ 2 * tightTransversalCoefficient p V :=
      Math115.RetainedRoot.repair_coefficient_bound p _ hp ht.1
    _ ≤ 2 * (p : ℝ) ^ 2 * ((p : ℝ) * (V : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left ht.2 (by positivity)
    _ = _ := by ring

theorem tight_rational_trace_bound (p V Q : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V) (hQ : Q ≤ 4 * p - 3) :
    4 * (Q : ℝ) * tightFullCoefficient p V ≤ 32 * (p : ℝ) ^ 4 * (V : ℝ) ^ 2 := by
  have hq : (Q : ℝ) ≤ 4 * (p : ℝ) := by exact_mod_cast hQ.trans (Nat.sub_le _ _)
  calc
    _ ≤ 4 * (Q : ℝ) * (2 * (p : ℝ) ^ 3 * (V : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (tight_fullCoefficient_bound p V hp hV) (by positivity)
    _ ≤ 4 * (4 * (p : ℝ)) * (2 * (p : ℝ) ^ 3 * (V : ℝ) ^ 2) := by gcongr
    _ = _ := by ring

theorem tight_dyadic_trace_bound (p V Q : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQpos : 1 ≤ Q) (hQ : Q ≤ 4 * p - 3) :
    2 * (Math115.RetainedRoot.dyadicDenominator Q : ℝ) * tightFullCoefficient p V ≤
      64 * (p : ℝ) ^ 4 * (V : ℝ) ^ 2 := by
  have hd : (Math115.RetainedRoot.dyadicDenominator Q : ℝ) ≤ 4 * (Q : ℝ) := by
    exact_mod_cast (Math115.RetainedRoot.dyadicDenominator_bounds Q hQpos).2.le
  have hq : (Q : ℝ) ≤ 4 * (p : ℝ) := by exact_mod_cast hQ.trans (Nat.sub_le _ _)
  have hdp : (Math115.RetainedRoot.dyadicDenominator Q : ℝ) ≤ 16 * (p : ℝ) := by linarith only [hd, hq]
  calc
    _ ≤ 2 * (Math115.RetainedRoot.dyadicDenominator Q : ℝ) *
        (2 * (p : ℝ) ^ 3 * (V : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (tight_fullCoefficient_bound p V hp hV) (by positivity)
    _ ≤ 2 * (16 * (p : ℝ)) * (2 * (p : ℝ) ^ 3 * (V : ℝ) ^ 2) := by gcongr
    _ = _ := by ring

theorem tight_rational_uniform_d8 (p V Q d : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQ : Q ≤ 4 * p - 3) (hpd : p ≤ d) (hVd : V ≤ 11 * d ^ 2) :
    4 * (Q : ℝ) * tightFullCoefficient p V ≤ 3872 * (d : ℝ) ^ 8 := by
  have hpR : (p : ℝ) ≤ d := by exact_mod_cast hpd
  have hVR : (V : ℝ) ≤ 11 * (d : ℝ) ^ 2 := by exact_mod_cast hVd
  calc
    _ ≤ 32 * (p : ℝ) ^ 4 * (V : ℝ) ^ 2 := tight_rational_trace_bound p V Q hp hV hQ
    _ ≤ 32 * (d : ℝ) ^ 4 * (11 * (d : ℝ) ^ 2) ^ 2 := by gcongr
    _ = _ := by ring

theorem tight_dyadic_uniform_d8 (p V Q d : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQpos : 1 ≤ Q) (hQ : Q ≤ 4 * p - 3) (hpd : p ≤ d) (hVd : V ≤ 11 * d ^ 2) :
    2 * (Math115.RetainedRoot.dyadicDenominator Q : ℝ) * tightFullCoefficient p V ≤ 7744 * (d : ℝ) ^ 8 := by
  have hpR : (p : ℝ) ≤ d := by exact_mod_cast hpd
  have hVR : (V : ℝ) ≤ 11 * (d : ℝ) ^ 2 := by exact_mod_cast hVd
  calc
    _ ≤ 64 * (p : ℝ) ^ 4 * (V : ℝ) ^ 2 := tight_dyadic_trace_bound p V Q hp hV hQpos hQ
    _ ≤ 64 * (d : ℝ) ^ 4 * (11 * (d : ℝ) ^ 2) ^ 2 := by gcongr
    _ = _ := by ring

theorem tight_rational_shape_d6 (p V Q d s : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQ : Q ≤ 4 * p - 3) (hpd : p ≤ d) (hVd : V ≤ 11 * d * s) :
    4 * (Q : ℝ) * tightFullCoefficient p V ≤ 3872 * (d : ℝ) ^ 6 * (s : ℝ) ^ 2 := by
  have hpR : (p : ℝ) ≤ d := by exact_mod_cast hpd
  have hVR : (V : ℝ) ≤ 11 * (d : ℝ) * s := by exact_mod_cast hVd
  calc
    _ ≤ 32 * (p : ℝ) ^ 4 * (V : ℝ) ^ 2 := tight_rational_trace_bound p V Q hp hV hQ
    _ ≤ 32 * (d : ℝ) ^ 4 * (11 * (d : ℝ) * s) ^ 2 := by gcongr
    _ = _ := by ring

theorem tight_dyadic_shape_d6 (p V Q d s : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V)
    (hQpos : 1 ≤ Q) (hQ : Q ≤ 4 * p - 3) (hpd : p ≤ d) (hVd : V ≤ 11 * d * s) :
    2 * (Math115.RetainedRoot.dyadicDenominator Q : ℝ) * tightFullCoefficient p V ≤
      7744 * (d : ℝ) ^ 6 * (s : ℝ) ^ 2 := by
  have hpR : (p : ℝ) ≤ d := by exact_mod_cast hpd
  have hVR : (V : ℝ) ≤ 11 * (d : ℝ) * s := by exact_mod_cast hVd
  calc
    _ ≤ 64 * (p : ℝ) ^ 4 * (V : ℝ) ^ 2 := tight_dyadic_trace_bound p V Q hp hV hQpos hQ
    _ ≤ 64 * (d : ℝ) ^ 4 * (11 * (d : ℝ) * s) ^ 2 := by gcongr
    _ = _ := by ring

end Math115.RetainedRootSquare
