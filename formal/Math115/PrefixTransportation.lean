import Math115.LatticeCellVolume

/-!
# Transportation regions in interior prefix coordinates

The region is the image of finite nonnegative real tables with prescribed
signed real margins. Zero-boundary prefix offsets perturb entries by mixed
differences, preserve margins, and recover precisely the chosen interior
prefix displacement. These are the concrete geometric bridges for lattice
cells; a coarse floor cover and finite integer-table count identification
are separate obligations.
-/

namespace Math115.PrefixTransportation

open MeasureTheory
open scoped BigOperators Pointwise ENNReal

noncomputable section

abbrev Array := ℕ → ℕ → ℝ
abbrev Matrix (a b : ℕ) := Fin a → Fin b → ℝ
abbrev Interior (a b : ℕ) := Fin (a - 1) × Fin (b - 1)

def difference (u : Array) : Array := fun i j =>
  u (i + 1) (j + 1) - u i (j + 1) - u (i + 1) j + u i j

def prefixSum (X : Array) (p q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, X i j

def ZeroAxes (u : Array) : Prop := (∀ q, u 0 q = 0) ∧ (∀ p, u p 0 = 0)

def ZeroBoundary (a b : ℕ) (u : Array) : Prop :=
  ZeroAxes u ∧ (∀ q, u a q = 0) ∧ (∀ p, u p b = 0)

lemma difference_row_sum (u : Array) (i b : ℕ) :
    (∑ j ∈ Finset.range b, difference u i j) =
      (u (i + 1) b - u i b) - (u (i + 1) 0 - u i 0) := by
  calc
    _ = ∑ j ∈ Finset.range b,
        ((u (i + 1) (j + 1) - u i (j + 1)) - (u (i + 1) j - u i j)) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold difference
      ring
    _ = _ := Finset.sum_range_sub (fun j => u (i + 1) j - u i j) b

lemma difference_column_sum (u : Array) (a j : ℕ) :
    (∑ i ∈ Finset.range a, difference u i j) =
      (u a (j + 1) - u a j) - (u 0 (j + 1) - u 0 j) := by
  calc
    _ = ∑ i ∈ Finset.range a,
        ((u (i + 1) (j + 1) - u (i + 1) j) - (u i (j + 1) - u i j)) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold difference
      ring
    _ = _ := Finset.sum_range_sub (fun i => u i (j + 1) - u i j) a

lemma difference_row_sum_zero (a b : ℕ) (u : Array) (hu : ZeroBoundary a b u) (i : ℕ) :
    (∑ j ∈ Finset.range b, difference u i j) = 0 := by
  rw [difference_row_sum, hu.2.2, hu.2.2, hu.1.2, hu.1.2]
  ring

lemma difference_column_sum_zero (a b : ℕ) (u : Array) (hu : ZeroBoundary a b u) (j : ℕ) :
    (∑ i ∈ Finset.range a, difference u i j) = 0 := by
  rw [difference_column_sum, hu.2.1, hu.2.1, hu.1.1, hu.1.1]
  ring

lemma prefix_zero_axes (X : Array) : ZeroAxes (prefixSum X) := by
  constructor <;> intro n <;> simp [prefixSum]

lemma prefix_difference (u : Array) (hu : ZeroAxes u) (p q : ℕ) :
    prefixSum (difference u) p q = u p q := by
  unfold prefixSum
  simp_rw [difference_row_sum, hu.2, sub_self, sub_zero]
  rw [Finset.sum_range_sub (fun i => u i q) p, hu.1, sub_zero]

lemma difference_prefix (X : Array) : difference (prefixSum X) = X := by
  funext i j
  unfold difference prefixSum
  simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
  ring

def extend {a b : ℕ} (X : Matrix a b) : Array := fun i j =>
  if h : i < a ∧ j < b then X ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

def restrict {a b : ℕ} (X : Array) : Matrix a b := fun i j => X i.val j.val

@[simp] lemma extend_inside {a b : ℕ} (X : Matrix a b) (i : Fin a) (j : Fin b) :
    extend X i.val j.val = X i j := by simp [extend, i.isLt, j.isLt]

lemma extend_outside {a b : ℕ} (X : Matrix a b) (i j : ℕ)
    (h : a ≤ i ∨ b ≤ j) : extend X i j = 0 := by
  simp [extend, show ¬(i < a ∧ j < b) by omega]

lemma range_sum_extend_row {a b : ℕ} (X : Matrix a b) (i : Fin a) :
    (∑ j ∈ Finset.range b, extend X i.val j) = ∑ j : Fin b, X i j := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp

lemma range_sum_extend_column {a b : ℕ} (X : Matrix a b) (j : Fin b) :
    (∑ i ∈ Finset.range a, extend X i j.val) = ∑ i : Fin a, X i j := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp

def interiorPrefix {a b : ℕ} (X : Matrix a b) : Interior a b → ℝ := fun p =>
  prefixSum (extend X) (p.1.val + 1) (p.2.val + 1)

lemma interiorPrefix_add {a b : ℕ} (X Y : Matrix a b) :
    interiorPrefix (X + Y) = interiorPrefix X + interiorPrefix Y := by
  have he : extend (X + Y) = extend X + extend Y := by
    funext i j
    by_cases h : i < a ∧ j < b <;> simp [extend, h]
  funext p
  simp [interiorPrefix, he, prefixSum, Finset.sum_add_distrib]

lemma interiorPrefix_smul {a b : ℕ} (t : ℝ) (X : Matrix a b) :
    interiorPrefix (t • X) = t • interiorPrefix X := by
  have he : extend (t • X) = t • extend X := by
    funext i j
    by_cases h : i < a ∧ j < b <;> simp [extend, h]
  funext p
  simp [interiorPrefix, he, prefixSum, Finset.mul_sum]

/-- Fixed row and column margins make the interior prefix coordinates
injective. This does not require nonnegative entries. -/
lemma interiorPrefix_injective_of_margins {a b : ℕ} (X Y : Matrix a b)
    (hrows : ∀ i, (∑ j, X i j) = ∑ j, Y i j)
    (hcols : ∀ j, (∑ i, X i j) = ∑ i, Y i j)
    (hxy : interiorPrefix X = interiorPrefix Y) : X = Y := by
  have hfull (p : ℕ) (hp : p ≤ a) (q : ℕ) (hq : q ≤ b) :
      prefixSum (extend X) p q = prefixSum (extend Y) p q := by
    by_cases hp0 : p = 0
    · subst p; simp [prefixSum]
    by_cases hq0 : q = 0
    · subst q; simp [prefixSum]
    by_cases hpa : p = a
    · subst p
      unfold prefixSum
      conv_lhs => rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      have hjb : j < b := lt_of_lt_of_le (Finset.mem_range.mp hj) hq
      rw [range_sum_extend_column X ⟨j, hjb⟩,
        range_sum_extend_column Y ⟨j, hjb⟩]
      exact hcols ⟨j, hjb⟩
    by_cases hqb : q = b
    · subst q
      unfold prefixSum
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i < a := lt_of_lt_of_le (Finset.mem_range.mp hi) hp
      rw [range_sum_extend_row X ⟨i, hia⟩,
        range_sum_extend_row Y ⟨i, hia⟩]
      exact hrows ⟨i, hia⟩
    have hip : p - 1 < a - 1 := by omega
    have hjq : q - 1 < b - 1 := by omega
    have h := congrFun hxy (⟨p - 1, hip⟩, ⟨q - 1, hjq⟩)
    simpa only [interiorPrefix, show p - 1 + 1 = p by omega,
      show q - 1 + 1 = q by omega] using h
  funext i j
  have hi := i.isLt
  have hj := j.isLt
  calc
    X i j = difference (prefixSum (extend X)) i.val j.val := by
      rw [difference_prefix, extend_inside]
    _ = difference (prefixSum (extend Y)) i.val j.val := by
      unfold difference
      rw [hfull (i.val + 1) (by omega) (j.val + 1) (by omega),
        hfull i.val (by omega) (j.val + 1) (by omega),
        hfull (i.val + 1) (by omega) j.val (by omega),
        hfull i.val (by omega) j.val (by omega)]
    _ = Y i j := by rw [difference_prefix, extend_inside]

/-- Real prefix displacements, extended by zero on every rectangle boundary
and outside it. -/
def offsets (a b : ℕ) (u : Interior a b → ℝ) : Array := fun p q =>
  if h : 0 < p ∧ p < a ∧ 0 < q ∧ q < b then
    u (⟨p - 1, by omega⟩, ⟨q - 1, by omega⟩)
  else 0

lemma offsets_zero_boundary (a b : ℕ) (u : Interior a b → ℝ) :
    ZeroBoundary a b (offsets a b u) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro q; simp [offsets]
  · intro p; simp [offsets]
  · intro q; simp [offsets]
  · intro p; simp [offsets]

lemma offsets_apply (a b : ℕ) (u : Interior a b → ℝ)
    (i : Fin (a - 1)) (j : Fin (b - 1)) :
    offsets a b u (i.val + 1) (j.val + 1) = u (i, j) := by
  have hi := i.isLt
  have hj := j.isLt
  have h : 0 < i.val + 1 ∧ i.val + 1 < a ∧ 0 < j.val + 1 ∧ j.val + 1 < b := by omega
  have heI : (⟨i.val + 1 - 1, by omega⟩ : Fin (a - 1)) = i := by
    apply Fin.ext
    change i.val + 1 - 1 = i.val
    omega
  have heJ : (⟨j.val + 1 - 1, by omega⟩ : Fin (b - 1)) = j := by
    apply Fin.ext
    change j.val + 1 - 1 = j.val
    omega
  simp only [offsets, dite_eq_left h, heI, heJ]

lemma offsets_difference_outside (a b : ℕ) (u : Interior a b → ℝ) (i j : ℕ)
    (h : a ≤ i ∨ b ≤ j) : difference (offsets a b u) i j = 0 := by
  have h00 : ¬(0 < i ∧ i < a ∧ 0 < j ∧ j < b) := by omega
  have h01 : ¬(0 < i ∧ i < a ∧ 0 < j + 1 ∧ j + 1 < b) := by omega
  have h10 : ¬(0 < i + 1 ∧ i + 1 < a ∧ 0 < j ∧ j < b) := by omega
  have h11 : ¬(0 < i + 1 ∧ i + 1 < a ∧ 0 < j + 1 ∧ j + 1 < b) := by omega
  simp only [difference, offsets, dite_eq_right h00, dite_eq_right h01,
    dite_eq_right h10, dite_eq_right h11]
  ring

def perturbation (a b : ℕ) (u : Interior a b → ℝ) : Matrix a b :=
  restrict (difference (offsets a b u))

lemma extend_perturbation (a b : ℕ) (u : Interior a b → ℝ) :
    extend (perturbation a b u) = difference (offsets a b u) := by
  funext i j
  by_cases h : i < a ∧ j < b
  · simp only [extend, dite_eq_left h, perturbation, restrict]
  · have hout : a ≤ i ∨ b ≤ j := by omega
    rw [extend_outside _ _ _ hout, offsets_difference_outside _ _ _ _ _ hout]

lemma perturbation_rows_zero (a b : ℕ) (u : Interior a b → ℝ) (i : Fin a) :
    (∑ j : Fin b, perturbation a b u i j) = 0 := by
  rw [← range_sum_extend_row, extend_perturbation]
  exact difference_row_sum_zero a b _ (offsets_zero_boundary a b u) i.val

lemma perturbation_columns_zero (a b : ℕ) (u : Interior a b → ℝ) (j : Fin b) :
    (∑ i : Fin a, perturbation a b u i j) = 0 := by
  rw [← range_sum_extend_column, extend_perturbation]
  exact difference_column_sum_zero a b _ (offsets_zero_boundary a b u) j.val

lemma interiorPrefix_perturbation (a b : ℕ) (u : Interior a b → ℝ) :
    interiorPrefix (perturbation a b u) = u := by
  funext p
  rw [interiorPrefix, extend_perturbation, prefix_difference _
    (offsets_zero_boundary a b u).1, offsets_apply]

lemma offsets_error (a b : ℕ) (t : ℝ) (ht : 0 < t) (u : Interior a b → ℝ)
    (hu : ∀ p, 0 ≤ u p ∧ u p < t) (p q : ℕ) :
    0 ≤ offsets a b u p q ∧ offsets a b u p q < t := by
  unfold offsets
  split_ifs with h
  · exact hu _
  · exact ⟨le_refl 0, ht⟩

lemma perturbation_error (a b : ℕ) (t : ℝ) (ht : 0 < t) (u : Interior a b → ℝ)
    (hu : ∀ p, 0 ≤ u p ∧ u p < t) (i : Fin a) (j : Fin b) :
    -(2 * t) < perturbation a b u i j ∧ perturbation a b u i j < 2 * t := by
  exact LatticeCellVolume.mixed_difference_error t _ _ _ _
    (offsets_error a b t ht u hu i.val j.val)
    (offsets_error a b t ht u hu i.val (j.val + 1))
    (offsets_error a b t ht u hu (i.val + 1) j.val)
    (offsets_error a b t ht u hu (i.val + 1) (j.val + 1))

/-- Fixed-margin finite real tables. Margins are signed reals; no natural
subtraction or dense-margin normalization is built into the definition. -/
def Feasible {a b : ℕ} (R : Fin a → ℝ) (P : Fin b → ℝ) (X : Matrix a b) : Prop :=
  (∀ i j, 0 ≤ X i j) ∧ (∀ i, ∑ j, X i j = R i) ∧ (∀ j, ∑ i, X i j = P j)

def PrefixRegion {a b : ℕ} (R : Fin a → ℝ) (P : Fin b → ℝ) : Set (Interior a b → ℝ) :=
  {z | ∃ X : Matrix a b, Feasible R P X ∧ interiorPrefix X = z}

lemma feasible_add {a b : ℕ} (R S : Fin a → ℝ) (P Q : Fin b → ℝ)
    (X Y : Matrix a b) (hX : Feasible R P X) (hY : Feasible S Q Y) :
    Feasible (R + S) (P + Q) (X + Y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; exact add_nonneg (hX.1 i j) (hY.1 i j)
  · intro i; simp [Finset.sum_add_distrib, hX.2.1 i, hY.2.1 i]
  · intro j; simp [Finset.sum_add_distrib, hX.2.2 j, hY.2.2 j]

lemma feasible_smul {a b : ℕ} (R : Fin a → ℝ) (P : Fin b → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (X : Matrix a b) (hX : Feasible R P X) :
    Feasible (t • R) (t • P) (t • X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; exact mul_nonneg ht (hX.1 i j)
  · intro i
    change (∑ j, t * X i j) = t * R i
    rw [← Finset.mul_sum, hX.2.1 i]
  · intro j
    change (∑ i, t * X i j) = t * P j
    rw [← Finset.mul_sum, hX.2.2 j]

lemma feasible_const (a b : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Feasible (fun (_ : Fin a) => (b : ℝ) * t)
      (fun (_ : Fin b) => (a : ℝ) * t) (fun _ _ => t) := by
  refine ⟨fun _ _ => ht, ?_, ?_⟩ <;> intro i <;>
    simp [Finset.sum_const, nsmul_eq_mul]

/-- An actual nonnegative difference-margin table translates the whole
smaller transportation region into the larger one. -/
lemma prefixRegion_translate_subset {a b : ℕ}
    (R S : Fin a → ℝ) (P Q : Fin b → ℝ) (W : Matrix a b)
    (hW : Feasible S Q W) :
    (fun z => interiorPrefix W + z) '' PrefixRegion R P ⊆ PrefixRegion (R + S) (P + Q) := by
  rintro _ ⟨z, ⟨X, hX, rfl⟩, rfl⟩
  refine ⟨X + W, feasible_add R S P Q X W hX hW, ?_⟩
  rw [interiorPrefix_add, add_comm]

lemma prefixRegion_volume_mono_of_difference_table {a b : ℕ}
    (R S : Fin a → ℝ) (P Q : Fin b → ℝ) (W : Matrix a b)
    (hW : Feasible S Q W) :
    volume (PrefixRegion R P) ≤ volume (PrefixRegion (R + S) (P + Q)) := by
  exact LatticeCellVolume.volume_le_of_translated_subset _ _ _
    (prefixRegion_translate_subset R S P Q W hW)

lemma prefixRegion_constant_translate_subset {a b : ℕ}
    (R : Fin a → ℝ) (P : Fin b → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (fun z => interiorPrefix (fun (_ : Fin a) (_ : Fin b) => t) + z) ''
      PrefixRegion R P ⊆
        PrefixRegion (fun i => R i + (b : ℝ) * t) (fun j => P j + (a : ℝ) * t) := by
  exact prefixRegion_translate_subset R _ P _ _ (feasible_const a b t ht)

/-- Any nonnegative real margins with equal totals admit a nonnegative
real table, including the zero-total case. -/
lemma exists_feasible_of_nonnegative_equal_total {a b : ℕ}
    (R : Fin a → ℝ) (P : Fin b → ℝ)
    (hR : ∀ i, 0 ≤ R i) (hP : ∀ j, 0 ≤ P j)
    (htotal : (∑ i, R i) = ∑ j, P j) :
    ∃ X : Matrix a b, Feasible R P X := by
  let H := ∑ i, R i
  have hH : 0 ≤ H := Finset.sum_nonneg (fun i _ => hR i)
  by_cases hz : H = 0
  · have hr0 : ∀ i, R i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hR i)).mp hz i (Finset.mem_univ i)
    have hp0 : ∀ j, P j = 0 := by
      intro j
      have hsum : (∑ j, P j) = 0 := htotal.symm.trans hz
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hP j)).mp hsum j (Finset.mem_univ j)
    refine ⟨fun _ _ => 0, fun _ _ => le_refl 0, ?_, ?_⟩
    · intro i; simp [hr0 i]
    · intro j; simp [hp0 j]
  · refine ⟨fun i j => R i * P j / H, ?_, ?_, ?_⟩
    · intro i j; exact div_nonneg (mul_nonneg (hR i) (hP j)) hH
    · intro i
      rw [← Finset.sum_div, ← Finset.mul_sum, ← htotal]
      exact mul_div_cancel_right₀ (R i) hz
    · intro j
      rw [← Finset.sum_div, ← Finset.sum_mul]
      change H * P j / H = P j
      field_simp [hz]

/-- Coordinatewise larger equal-total margins have at least as much prefix
volume. The embedding comes from the constructed difference-margin table. -/
lemma prefixRegion_volume_mono {a b : ℕ}
    (R S : Fin a → ℝ) (P Q : Fin b → ℝ)
    (hR : ∀ i, R i ≤ S i) (hP : ∀ j, P j ≤ Q j)
    (hsource : (∑ i, R i) = ∑ j, P j)
    (htarget : (∑ i, S i) = ∑ j, Q j) :
    volume (PrefixRegion R P) ≤ volume (PrefixRegion S Q) := by
  have hdiff : (∑ i, (S - R) i) = ∑ j, (Q - P) j := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [hsource, htarget]
  obtain ⟨W, hW⟩ := exists_feasible_of_nonnegative_equal_total (S - R) (Q - P)
    (fun i => sub_nonneg.mpr (hR i)) (fun j => sub_nonneg.mpr (hP j)) hdiff
  have h := prefixRegion_volume_mono_of_difference_table R (S - R) P (Q - P) W hW
  have heR : R + (S - R) = S := by abel
  have heP : P + (Q - P) = Q := by abel
  simpa only [heR, heP] using h

/-- Positive scaling identifies the scaled transportation region exactly,
using inverse table scaling for the reverse inclusion. -/
lemma prefixRegion_scale_eq {a b : ℕ} (R : Fin a → ℝ) (P : Fin b → ℝ)
    (t : ℝ) (ht : 0 < t) :
    (fun z => t • z) '' PrefixRegion R P = PrefixRegion (t • R) (t • P) := by
  ext z
  constructor
  · rintro ⟨u, ⟨X, hX, rfl⟩, rfl⟩
    exact ⟨t • X, feasible_smul R P t ht.le X hX, interiorPrefix_smul t X⟩
  · rintro ⟨X, hX, hx⟩
    have hY : Feasible R P ((1 / t) • X) := by
      have h := feasible_smul (t • R) (t • P) (1 / t) (by positivity) X hX
      simpa only [smul_smul, one_div_mul_cancel (ne_of_gt ht), one_smul] using h
    refine ⟨interiorPrefix ((1 / t) • X), ⟨(1 / t) • X, hY, rfl⟩, ?_⟩
    change t • interiorPrefix ((1 / t) • X) = z
    rw [interiorPrefix_smul, smul_smul, mul_one_div_cancel (ne_of_gt ht), one_smul, hx]

lemma prefixRegion_volume_scale {a b : ℕ} (R : Fin a → ℝ) (P : Fin b → ℝ)
    (t : ℝ) (ht : 0 < t) :
    volume (PrefixRegion (t • R) (t • P)) =
      ENNReal.ofReal (t ^ ((a - 1) * (b - 1))) * volume (PrefixRegion R P) := by
  rw [← prefixRegion_scale_eq R P t ht, LatticeCellVolume.volume_image_scale t ht.le]
  simp [Interior, Fintype.card_prod, Fintype.card_fin]

/-- Every nonnegative real table admits the whole half-open prefix error
box after adding the entrywise buffer `2t`. This is the concrete upper-cell
containment, expressed at the point level with all boundary errors zero. -/
lemma prefix_error_upper_containment {a b : ℕ}
    (R : Fin a → ℝ) (P : Fin b → ℝ) (X : Matrix a b) (hX : Feasible R P X)
    (t : ℝ) (ht : 0 < t) (z : Interior a b → ℝ)
    (hz : ∀ p, 0 ≤ z p - interiorPrefix X p ∧ z p - interiorPrefix X p < t) :
    z + interiorPrefix (fun (_ : Fin a) (_ : Fin b) => 2 * t) ∈
      PrefixRegion (fun i => R i + (b : ℝ) * (2 * t))
        (fun j => P j + (a : ℝ) * (2 * t)) := by
  let u := z - interiorPrefix X
  let B : Matrix a b := fun _ _ => 2 * t
  let Y := X + perturbation a b u + B
  refine ⟨Y, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i j
    have hd := (perturbation_error a b t ht u hz i j).1
    have hentry := hX.1 i j
    change 0 ≤ X i j + perturbation a b u i j + 2 * t
    linarith only [hd, hentry]
  · intro i
    change (∑ j, (X i j + perturbation a b u i j + 2 * t)) = _
    simp [Finset.sum_add_distrib, hX.2.1 i, perturbation_rows_zero,
      Finset.sum_const, nsmul_eq_mul]
  · intro j
    change (∑ i, (X i j + perturbation a b u i j + 2 * t)) = _
    simp [Finset.sum_add_distrib, hX.2.2 j, perturbation_columns_zero,
      Finset.sum_const, nsmul_eq_mul]
  · change interiorPrefix (X + perturbation a b u + B) = _
    rw [interiorPrefix_add, interiorPrefix_add, interiorPrefix_perturbation]
    dsimp [u, B]
    abel

end

end Math115.PrefixTransportation
