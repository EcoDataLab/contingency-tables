import Research.SpectralPath
import Research.RetainedStencilSum
import Math115.RetainedRootSquare
import Research.SpectralPrefix

namespace Research.SpectralRetained

open scoped BigOperators Classical
open OAI.ContingencyTables.FiniteExposureVariance
open Research.SpectralPath Research.RetainedStencilSum
open Math115.RetainedRootSquare
open Research.SpectralPrefix

noncomputable def signedPrefix (N : ℕ) (z : ℕ → ℝ) (h : Fin (N + 1) → ℝ) (j : ℕ) : ℝ :=
  ∑ i, if i.val < j then z i.val * h i else 0

lemma prefix_zero (N : ℕ) (z : ℕ → ℝ) (h : Fin (N + 1) → ℝ) :
    signedPrefix N z h 0 = 0 := by simp [signedPrefix]

lemma prefix_full (N : ℕ) (z : ℕ → ℝ) (h : Fin (N + 1) → ℝ) :
    signedPrefix N z h (N + 1) = weightedSum (fun i : Fin (N + 1) => z i.val) h := by
  simp only [signedPrefix, Fin.isLt, ite_true]
  rfl

lemma prefix_edge (N : ℕ) (z : ℕ → ℝ) (h : Fin (N + 1) → ℝ) (l : Fin N) :
    signedPrefix N z h (l.val + 1) = prefixFlux N (fun i => z i.val) h l := by
  simp only [signedPrefix, prefixFlux, Nat.lt_succ_iff]

lemma prefix_step (N : ℕ) (z : ℕ → ℝ) (h : Fin (N + 1) → ℝ) (j : Fin (N + 1)) :
    signedPrefix N z h (j.val + 1) = signedPrefix N z h j.val + z j.val * h j := by
  have he : signedPrefix N z h (j.val + 1) - signedPrefix N z h j.val =
      ∑ i : Fin (N + 1), if i = j then z i.val * h i else 0 := by
    unfold signedPrefix
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : i = j
    · subst i
      simp
    · have hijv : i.val ≠ j.val := by intro he; exact hij (Fin.ext he)
      by_cases hi : i.val < j.val
      · simp only [hi, show i.val < j.val + 1 by omega, ite_true, ite_false, hij, sub_self]
      · simp only [hi, show ¬ i.val < j.val + 1 by omega, ite_false, hij, sub_self]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at he
  linarith

/-- Exact square-signedPrefix correction collection, with both actual exterior
moments retained. No positivity or moment cap is needed for this identity. -/
lemma square_correction_collection (z c U : ℕ → ℝ) (N : ℕ)
    (hU0 : U 0 = 0) (hUN : U (N + 1) = 0) :
    (∑ k ∈ Finset.range N, U (k + 1) ^ 2 *
      (2 * c (k + 1) / (z k * z (k + 1)) - c k / z k ^ 2 - c (k + 2) / z (k + 1) ^ 2)) =
      -c 0 * U 1 ^ 2 / z 0 ^ 2 +
      (∑ k ∈ Finset.range N, c (k + 1) *
        (2 * U (k + 1) ^ 2 / (z k * z (k + 1)) - U k ^ 2 / z k ^ 2 -
          U (k + 2) ^ 2 / z (k + 1) ^ 2)) -
      c (N + 1) * U N ^ 2 / z N ^ 2 := by
  cases N with
  | zero => simp only [Finset.sum_range_zero, hU0, hUN, zero_pow (by decide : 2 ≠ 0)]; ring
  | succ n =>
    have h := correction_collection (fun j => U j ^ 2)
      (fun j => 1 / (z (j - 1) * z j)) (fun j => 1 / z j ^ 2) c
      (by simp only [hU0, zero_pow (by decide : 2 ≠ 0)]) n
    simp only [Nat.add_sub_cancel] at h
    conv_rhs => rw [Finset.sum_range_succ]
    have hEnd : U (n + 2) = 0 := by simpa only [Nat.add_assoc] using hUN
    simp only [hEnd, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]
    convert h using 1
    all_goals simp only [div_eq_mul_inv, one_mul]
    all_goals ring_nf

lemma collected_square (N : ℕ) (z : ℕ → ℝ) (h : Fin (N + 1) → ℝ) (l : Fin N) :
    2 * signedPrefix N z h (l.val + 1) ^ 2 / (z l.val * z (l.val + 1)) -
      signedPrefix N z h l.val ^ 2 / z l.val ^ 2 -
      signedPrefix N z h (l.val + 2) ^ 2 / z (l.val + 1) ^ 2 =
    squareCoefficient (z l.val) (z (l.val + 1))
      (prefixFlux N (fun i => z i.val) h l) (h l.castSucc) (h l.succ) := by
  have hp := prefix_step N z h l.castSucc
  have hn := prefix_step N z h l.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at hp hn
  have hp' : signedPrefix N z h l.val =
      signedPrefix N z h (l.val + 1) - z l.val * h l.castSucc := by linarith
  have hn' : signedPrefix N z h (l.val + 2) =
      signedPrefix N z h (l.val + 1) + z (l.val + 1) * h l.succ := by
    simpa only [Nat.add_assoc] using hn
  rw [hp', hn', prefix_edge]
  rfl

lemma prefix_correction_collection (N : ℕ) (z c : ℕ → ℝ) (h : Fin (N + 1) → ℝ)
    (hh : weightedSum (fun i : Fin (N + 1) => z i.val) h = 0) :
    (∑ l : Fin N, (prefixFlux N (fun i => z i.val) h l) ^ 2 *
      (2 * c (l.val + 1) / (z l.val * z (l.val + 1)) - c l.val / z l.val ^ 2 -
        c (l.val + 2) / z (l.val + 1) ^ 2)) =
      -c 0 * signedPrefix N z h 1 ^ 2 / z 0 ^ 2 +
      (∑ l : Fin N, c (l.val + 1) *
        squareCoefficient (z l.val) (z (l.val + 1))
          (prefixFlux N (fun i => z i.val) h l) (h l.castSucc) (h l.succ)) -
      c (N + 1) * signedPrefix N z h N ^ 2 / z N ^ 2 := by
  have hcoll := square_correction_collection z c (signedPrefix N z h) N
    (prefix_zero N z h) (by rw [prefix_full, hh])
  have hfin :
      (∑ l : Fin N, signedPrefix N z h (l.val + 1) ^ 2 *
        (2 * c (l.val + 1) / (z l.val * z (l.val + 1)) - c l.val / z l.val ^ 2 -
          c (l.val + 2) / z (l.val + 1) ^ 2)) =
        -c 0 * signedPrefix N z h 1 ^ 2 / z 0 ^ 2 +
        (∑ l : Fin N, c (l.val + 1) *
          (2 * signedPrefix N z h (l.val + 1) ^ 2 / (z l.val * z (l.val + 1)) -
            signedPrefix N z h l.val ^ 2 / z l.val ^ 2 -
            signedPrefix N z h (l.val + 2) ^ 2 / z (l.val + 1) ^ 2)) -
        c (N + 1) * signedPrefix N z h N ^ 2 / z N ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => signedPrefix N z h (k + 1) ^ 2 *
      (2 * c (k + 1) / (z k * z (k + 1)) - c k / z k ^ 2 - c (k + 2) / z (k + 1) ^ 2)) N,
      Fin.sum_univ_eq_sum_range (fun k => c (k + 1) *
        (2 * signedPrefix N z h (k + 1) ^ 2 / (z k * z (k + 1)) -
          signedPrefix N z h k ^ 2 / z k ^ 2 - signedPrefix N z h (k + 2) ^ 2 / z (k + 1) ^ 2)) N]
    exact hcoll
  simp_rw [collected_square, prefix_edge] at hfin
  exact hfin

/-- The actual finite correction stencil is bounded by eigenflux squares.
The flux is supplied by the proved compact Rayleigh construction, not by a
numerical Poincare assumption. -/
lemma correction_bound_of_eigenflux (N : ℕ) (z c r : ℕ → ℝ)
    (h : Fin (N + 1) → ℝ) (K lam : ℝ)
    (hz : ∀ i ≤ N, 0 < z i) (hc : ∀ i ≤ N + 1, 0 ≤ c i)
    (hcap : ∀ j, 1 ≤ j → j ≤ N → c j ≤ K * max (z (j - 1)) (z j))
    (hlam : 0 ≤ lam) (hr : ∀ l : Fin N, 0 ≤ r (l.val + 1))
    (hh : weightedSum (fun i : Fin (N + 1) => z i.val) h = 0)
    (hflux : ∀ l : Fin N, h l.castSucc - h l.succ =
      lam * r (l.val + 1) * prefixFlux N (fun i => z i.val) h l) :
    (∑ l : Fin N, (prefixFlux N (fun i => z i.val) h l) ^ 2 *
      (2 * c (l.val + 1) / (z l.val * z (l.val + 1)) - c l.val / z l.val ^ 2 -
        c (l.val + 2) / z (l.val + 1) ^ 2)) ≤
      2 * K * lam * (∑ l : Fin N, r (l.val + 1) * (prefixFlux N (fun i => z i.val) h l) ^ 2) := by
  rw [prefix_correction_collection N z c h hh]
  have hleft := exterior_correction_nonpos (c 0) (signedPrefix N z h 1) (z 0) (hc 0 (by omega))
  have hright : 0 ≤ c (N + 1) * signedPrefix N z h N ^ 2 / z N ^ 2 := by
    have hcn := hc (N + 1) (by omega)
    positivity
  have hsum :
      (∑ l : Fin N, c (l.val + 1) *
        squareCoefficient (z l.val) (z (l.val + 1))
          (prefixFlux N (fun i => z i.val) h l) (h l.castSucc) (h l.succ)) ≤
        2 * K * lam * (∑ l : Fin N, r (l.val + 1) * (prefixFlux N (fun i => z i.val) h l) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    have h := capped_square_coefficient_of_flux (z l.val) (z (l.val + 1))
      (prefixFlux N (fun i => z i.val) h l) (h l.castSucc) (h l.succ) (c (l.val + 1)) K lam
      (r (l.val + 1)) (hz _ (by omega)) (hz _ (by omega)) (hc _ (by omega))
      (by simpa only [Nat.add_sub_cancel] using hcap (l.val + 1) (by omega) (by omega))
      hlam (hr l) (hflux l)
    rw [hflux l] at h
    convert h using 1
    ring
  linarith only [hleft, hright, hsum]

lemma regularized_energy_le (N : ℕ) (Xi E : ℕ → ℝ) (g : Fin (N + 1) → ℝ)
    (eps : ℝ) (heps : 0 < eps)
    (hXi : ∀ l : Fin N, 0 ≤ Xi (l.val + 1))
    (hE : ∀ l : Fin N, 0 ≤ E (l.val + 1))
    (hedge : ∀ l : Fin N, (g l.castSucc - g l.succ) ^ 2 ≤ Xi (l.val + 1) * E (l.val + 1)) :
    pathEnergy N (fun j => Xi j + eps) g ≤ ∑ l : Fin N, E (l.val + 1) := by
  unfold pathEnergy
  apply Finset.sum_le_sum
  intro l _
  apply (div_le_iff₀ (by linarith [hXi l] : 0 < Xi (l.val + 1) + eps)).mpr
  have hprod : 0 ≤ eps * E (l.val + 1) := mul_nonneg heps.le (hE l)
  nlinarith only [hedge l, hprod]

/-- Elementary closure of the positive regularization estimates. -/
lemma remove_regularization (A C M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hbound : ∀ eps : ℝ, 0 < eps → A ≤ (C + eps * M) * B) : A ≤ C * B := by
  apply le_of_forall_pos_le_add
  intro delta hdelta
  let eps := delta / (M * B + 1)
  have hden : 0 < M * B + 1 := by positivity
  have heps : 0 < eps := div_pos hdelta hden
  have heq : eps * (M * B + 1) = delta := div_mul_cancel₀ _ (ne_of_gt hden)
  have hsmall : eps * M * B ≤ delta := by nlinarith only [heq, heps]
  have h := hbound eps heps
  nlinarith only [h, hsmall]

lemma inverse_rayleigh_bound (lam V S C : ℝ) (hlam : 0 < lam) (hV : 0 < V)
    (hVS : V = lam * S) (hS : S ≤ C * V) : 1 / lam ≤ C := by
  have hm := mul_le_mul_of_nonneg_left hS hlam.le
  rw [← hVS] at hm
  apply (div_le_iff₀ hlam).mpr
  apply (mul_le_mul_iff_right₀ hV).mp
  nlinarith only [hm]

lemma regularized_flux_sum_split (N : ℕ) (z c : ℕ → ℝ) (h : Fin (N + 1) → ℝ) (eps : ℝ) :
    (∑ l : Fin N, (stencil z c (l.val + 1) + eps) *
      (prefixFlux N (fun i => z i.val) h l) ^ 2) =
      (∑ l : Fin N, (1 / z l.val + 1 / z (l.val + 1)) *
        (prefixFlux N (fun i => z i.val) h l) ^ 2) +
      (∑ l : Fin N, (prefixFlux N (fun i => z i.val) h l) ^ 2 *
        (2 * c (l.val + 1) / (z l.val * z (l.val + 1)) - c l.val / z l.val ^ 2 -
          c (l.val + 2) / z (l.val + 1) ^ 2)) +
      eps * (∑ l : Fin N, (prefixFlux N (fun i => z i.val) h l) ^ 2) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  simp only [stencil, Nat.add_sub_cancel]
  ring

theorem regularized_retained_variance_bound (N m : ℕ) (hN : 1 ≤ N) (hm : m ≤ N)
    (z c E : ℕ → ℝ) (g : Fin (N + 1) → ℝ) (K eps : ℝ) (hK : 0 ≤ K) (heps : 0 < eps)
    (hz : ∀ i ≤ N, 0 < z i)
    (hleftmono : ∀ i j, i ≤ j → j ≤ m → z i ≤ z j)
    (hrightmono : ∀ i j, m ≤ i → i ≤ j → j ≤ N → z j ≤ z i)
    (hc : ∀ i ≤ N + 1, 0 ≤ c i)
    (hcap : ∀ j, 1 ≤ j → j ≤ N → c j ≤ K * max (z (j - 1)) (z j))
    (hXi : ∀ l : Fin N, 0 ≤ stencil z c (l.val + 1))
    (hE : ∀ l : Fin N, 0 ≤ E (l.val + 1))
    (hedge : ∀ l : Fin N, (g l.castSucc - g l.succ) ^ 2 ≤
      stencil z c (l.val + 1) * E (l.val + 1)) :
    variance (fun i : Fin (N + 1) => z i.val) g ≤
      ((N : ℝ) * ((N : ℝ) + 1) + 2 * K +
        eps * ((N : ℝ) * totalMass N (fun i => z i.val) / 4)) *
          (∑ l : Fin N, E (l.val + 1)) := by
  let zf : Fin (N + 1) → ℝ := fun i => z i.val
  let r : ℕ → ℝ := fun j => stencil z c j + eps
  have hzf : ∀ i, 0 < zf i := fun i => hz i.val (by omega)
  have hr : ∀ l : Fin N, 0 < r (l.val + 1) := by intro l; dsimp [r]; linarith [hXi l]
  obtain ⟨lam, h, hlam, hmean, _h0, hv, _hq, _hmin, hflux, hres, huniv⟩ :=
    exists_path_rayleigh_minimizer N hN zf r hzf hr
  have hb := unimodal_base_bound N zf h m hzf hmean hm
    (fun i j hij hj => hleftmono i.val j.val hij hj)
    (fun i j hmi hij => hrightmono i.val j.val hmi hij (by omega))
  have hs := prefix_square_sum_bound N zf h hzf hmean
  have he := mul_le_mul_of_nonneg_left hs heps.le
  have hcor := correction_bound_of_eigenflux N z c r h K lam hz hc hcap
    hlam.le (fun l => (hr l).le) hmean hflux
  have hcor' :
      (∑ l : Fin N, (prefixFlux N zf h l) ^ 2 *
        (2 * c (l.val + 1) / (z l.val * z (l.val + 1)) - c l.val / z l.val ^ 2 -
          c (l.val + 2) / z (l.val + 1) ^ 2)) ≤ 2 * K * variance zf h := by
    calc
      _ ≤ 2 * K * lam * (∑ l : Fin N, r (l.val + 1) * (prefixFlux N zf h l) ^ 2) := hcor
      _ = 2 * K * variance zf h := by rw [hres]; ring
  let C : ℝ := (N : ℝ) * ((N : ℝ) + 1) + 2 * K + eps * ((N : ℝ) * totalMass N zf / 4)
  have hsum : (∑ l : Fin N, r (l.val + 1) * (prefixFlux N zf h l) ^ 2) ≤ C * variance zf h := by
    change (∑ l : Fin N, (stencil z c (l.val + 1) + eps) *
      (prefixFlux N (fun i => z i.val) h l) ^ 2) ≤ _
    rw [regularized_flux_sum_split]
    simp only [zf, Fin.val_castSucc, Fin.val_succ] at hb he hcor'
    dsimp only [C, zf]
    nlinarith only [hb, hcor', he]
  have hinv := inverse_rayleigh_bound lam (variance zf h)
    (∑ l : Fin N, r (l.val + 1) * (prefixFlux N zf h l) ^ 2) C hlam hv hres hsum
  have hC : 0 ≤ C := by
    have hZ := totalMass_pos N zf hzf
    dsimp only [C]
    positivity
  have henergy := regularized_energy_le N (stencil z c) E g eps heps hXi hE hedge
  calc
    variance zf g ≤ (1 / lam) * pathEnergy N r g := huniv g
    _ ≤ C * pathEnergy N r g :=
      mul_le_mul_of_nonneg_right hinv (pathEnergy_nonnegative N r g hr)
    _ ≤ C * (∑ l : Fin N, E (l.val + 1)) := mul_le_mul_of_nonneg_left henergy hC

/-- Full width-square retained-stencil theorem for the actual upstream
unnormalized variance. Only positive unimodal masses, nonnegative local
moments/caps, nonnegative stencil, and local energy comparisons are inputs.
The Rayleigh/Poincare estimate and zero-stencil closure are proved internally. -/
theorem retained_spectral_variance_bound_fin (N m : ℕ) (hN : 1 ≤ N) (hm : m ≤ N)
    (z c E : ℕ → ℝ) (g : Fin (N + 1) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hz : ∀ i ≤ N, 0 < z i)
    (hleftmono : ∀ i j, i ≤ j → j ≤ m → z i ≤ z j)
    (hrightmono : ∀ i j, m ≤ i → i ≤ j → j ≤ N → z j ≤ z i)
    (hc : ∀ i ≤ N + 1, 0 ≤ c i)
    (hcap : ∀ j, 1 ≤ j → j ≤ N → c j ≤ K * max (z (j - 1)) (z j))
    (hXi : ∀ l : Fin N, 0 ≤ stencil z c (l.val + 1))
    (hE : ∀ l : Fin N, 0 ≤ E (l.val + 1))
    (hedge : ∀ l : Fin N, (g l.castSucc - g l.succ) ^ 2 ≤
      stencil z c (l.val + 1) * E (l.val + 1)) :
    variance (fun i : Fin (N + 1) => z i.val) g ≤
      ((N : ℝ) * ((N : ℝ) + 1) + 2 * K) * (∑ l : Fin N, E (l.val + 1)) := by
  have hZ := totalMass_pos N (fun i : Fin (N + 1) => z i.val) (fun i => hz i.val (by omega))
  apply remove_regularization _ _ ((N : ℝ) * totalMass N (fun i => z i.val) / 4) _
    (by positivity) (Finset.sum_nonneg (fun l _ => hE l))
  intro eps heps
  exact regularized_retained_variance_bound N m hN hm z c E g K eps hK heps hz
    hleftmono hrightmono hc hcap hXi hE hedge

lemma fin_energy_sum_eq (N : ℕ) (E : ℕ → ℝ) :
    (∑ l : Fin N, E (l.val + 1)) = ∑ j ∈ Finset.Icc 1 N, E j := by
  rw [Fin.sum_univ_eq_sum_range (fun k => E (k + 1)) N,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.add_comm]

/-- Natural-index/Icc interface matching the previous mode-anchor theorem,
now with the improved constant and the proved finite Rayleigh engine. -/
theorem retained_spectral_variance_bound (z h c E : ℕ → ℝ) (K : ℝ) (N m : ℕ)
    (hN : 1 ≤ N) (hm : m ≤ N) (hK : 0 ≤ K) (hz : ∀ i ≤ N, 0 < z i)
    (hleftmono : ∀ i j, i ≤ j → j ≤ m → z i ≤ z j)
    (hrightmono : ∀ i j, m ≤ i → i ≤ j → j ≤ N → z j ≤ z i)
    (hc : ∀ i ≤ N + 1, 0 ≤ c i)
    (hcap : ∀ j, 1 ≤ j → j ≤ N → c j ≤ K * max (z (j - 1)) (z j))
    (hXi : ∀ l ∈ Finset.Icc 1 N, 0 ≤ stencil z c l)
    (hE : ∀ l ∈ Finset.Icc 1 N, 0 ≤ E l)
    (hedge : ∀ l ∈ Finset.Icc 1 N, (h l - h (l - 1)) ^ 2 ≤ stencil z c l * E l) :
    variance (fun i : Fin (N + 1) => z i.val) (fun i => h i.val) ≤
      ((N : ℝ) * ((N : ℝ) + 1) + 2 * K) * (∑ l ∈ Finset.Icc 1 N, E l) := by
  have hmem (l : Fin N) : l.val + 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hf := retained_spectral_variance_bound_fin N m hN hm z c E (fun i => h i.val) K hK hz
    hleftmono hrightmono hc hcap (fun l => hXi _ (hmem l)) (fun l => hE _ (hmem l))
    (fun l => by
      simp only [Fin.val_castSucc, Fin.val_succ]
      have hh := hedge _ (hmem l)
      simp only [Nat.add_sub_cancel] at hh
      convert hh using 1
      ring)
  rw [fin_energy_sum_eq] at hf
  exact hf

#print axioms retained_spectral_variance_bound

end Research.SpectralRetained
