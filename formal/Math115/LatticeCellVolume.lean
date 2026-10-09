import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Finite half-open lattice cells in prefix coordinates

The coordinate type is generic. In the completion application it is the
interior prefix index set. This module proves the geometric cell-count
identity and elementary cell errors. It does not identify a transportation
region with a union of cells or prove an acceptance probability.
-/

namespace Math115.LatticeCellVolume

open MeasureTheory
open scoped BigOperators Pointwise ENNReal

noncomputable section

variable {E A : Type*} [Fintype E] [Fintype A]

/-- A half-open cell anchored at an integer prefix vector on the lattice
of spacing `1/k`. The upper faces are excluded, so floor recovers the
anchor even at lower faces. -/
def prefixCell (k : ℤ) (c : E → ℤ) : Set (E → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico ((c i : ℝ) / (k : ℝ))
    (((c i : ℝ) + 1) / (k : ℝ)))

lemma prefixCell_measurable (k : ℤ) (c : E → ℤ) :
    MeasurableSet (prefixCell k c) := by
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

omit [Fintype E] in
lemma mem_prefixCell_iff (k : ℤ) (c : E → ℤ) (z : E → ℝ) :
    z ∈ prefixCell k c ↔ ∀ i,
      (c i : ℝ) / (k : ℝ) ≤ z i ∧ z i < ((c i : ℝ) + 1) / (k : ℝ) := by
  simp [prefixCell, Set.mem_pi]

omit [Fintype E] in
/-- Multiplying any cell coordinate by its positive dilation and flooring
recovers its anchor. -/
lemma floor_mul_eq_anchor (k : ℤ) (hk : 0 < k) (c : E → ℤ)
    (z : E → ℝ) (hz : z ∈ prefixCell k c) (i : E) :
    Int.floor ((k : ℝ) * z i) = c i := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hi := (mem_prefixCell_iff k c z).mp hz i
  apply Int.floor_eq_iff.mpr
  constructor
  · have h := (div_le_iff₀ hkR).mp hi.1
    nlinarith only [h]
  · have h := (lt_div_iff₀ hkR).mp hi.2
    nlinarith only [h]

omit [Fintype E] in
lemma prefixCell_disjoint (k : ℤ) (hk : 0 < k) (c d : E → ℤ)
    (hcd : c ≠ d) : Disjoint (prefixCell k c) (prefixCell k d) := by
  apply Set.disjoint_left.mpr
  intro z hc hd
  apply hcd
  funext i
  exact (floor_mul_eq_anchor k hk c z hc i).symm.trans
    (floor_mul_eq_anchor k hk d z hd i)

lemma prefixCell_volume (k : ℤ) (hk : 0 < k) (c : E → ℤ) :
    volume (prefixCell k c) =
      ENNReal.ofReal ((1 / (k : ℝ)) ^ Fintype.card E) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hside (i : E) : (((c i : ℝ) + 1) / (k : ℝ)) -
      (c i : ℝ) / (k : ℝ) = 1 / (k : ℝ) := by ring
  rw [prefixCell, Real.volume_pi_Ico]
  simp_rw [hside]
  rw [Finset.prod_const, Finset.card_univ]
  exact (ENNReal.ofReal_pow (by positivity) _).symm

lemma prefixCells_measurable (k : ℤ) (c : A → E → ℤ) :
    MeasurableSet (⋃ x : A, prefixCell k (c x)) := by
  exact MeasurableSet.iUnion (fun x => prefixCell_measurable k (c x))

omit [Fintype E] [Fintype A] in
lemma prefixCells_pairwiseDisjoint (k : ℤ) (hk : 0 < k)
    (c : A → E → ℤ) (hc : Function.Injective c) :
    Pairwise (fun x y => Disjoint (prefixCell k (c x)) (prefixCell k (c y))) := by
  intro x y hxy
  exact prefixCell_disjoint k hk (c x) (c y) (fun h => hxy (hc h))

/-- Exact volume of a finite family of disjoint half-open prefix cells.
This includes empty coordinate/index types. -/
theorem prefix_lattice_cells_volume (k : ℤ) (hk : 0 < k)
    (c : A → E → ℤ) (hc : Function.Injective c) :
    volume (⋃ x : A, prefixCell k (c x)) =
      (Fintype.card A : ℝ≥0∞) *
        ENNReal.ofReal ((1 / (k : ℝ)) ^ Fintype.card E) := by
  classical
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset A))
      (fun x => prefixCell k (c x)) := by
    intro x hx y hy hxy
    exact prefixCells_pairwiseDisjoint k hk c hc hxy
  have hmeasure := measure_biUnion_finset (μ := volume) hd
    (fun x _ => prefixCell_measurable k (c x))
  simpa [prefixCell_volume k hk, Finset.sum_const, nsmul_eq_mul] using hmeasure

/-- Coarse unit cells have total volume equal to their number. -/
theorem prefix_unit_cells_volume (c : A → E → ℤ) (hc : Function.Injective c) :
    volume (⋃ x : A, prefixCell 1 (c x)) = (Fintype.card A : ℝ≥0∞) := by
  simpa using prefix_lattice_cells_volume 1 (by norm_num) c hc

lemma prefix_lattice_cells_volume_ne_top (k : ℤ) (hk : 0 < k)
    (c : A → E → ℤ) (hc : Function.Injective c) :
    volume (⋃ x : A, prefixCell k (c x)) ≠ ⊤ := by
  rw [prefix_lattice_cells_volume k hk c hc]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top

lemma prefix_lattice_cells_volume_pos [Nonempty A] (k : ℤ) (hk : 0 < k)
    (c : A → E → ℤ) (hc : Function.Injective c) :
    0 < volume (⋃ x : A, prefixCell k (c x)) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  rw [prefix_lattice_cells_volume k hk c hc]
  apply ENNReal.mul_pos_iff.mpr
  constructor
  · exact_mod_cast Fintype.card_pos
  · apply ENNReal.ofReal_pos.mpr
    positivity

theorem prefix_lattice_cells_volume_toReal (k : ℤ) (hk : 0 < k)
    (c : A → E → ℤ) (hc : Function.Injective c) :
    (volume (⋃ x : A, prefixCell k (c x))).toReal =
      (Fintype.card A : ℝ) * (1 / (k : ℝ)) ^ Fintype.card E := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  rw [prefix_lattice_cells_volume k hk c hc, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)]

omit [Fintype E] in
/-- Each prefix-coordinate displacement lies in the half-open error
interval `[0,1/k)`. -/
lemma prefixCell_error (k : ℤ) (c : E → ℤ)
    (z : E → ℝ) (hz : z ∈ prefixCell k c) (i : E) :
    0 ≤ z i - (c i : ℝ) / (k : ℝ) ∧
      z i - (c i : ℝ) / (k : ℝ) < 1 / (k : ℝ) := by
  have hi := (mem_prefixCell_iff k c z).mp hz i
  have hside : (((c i : ℝ) + 1) / (k : ℝ)) -
      (c i : ℝ) / (k : ℝ) = 1 / (k : ℝ) := by ring
  constructor <;> linarith only [hi.1, hi.2, hside]

/-- The signed four-prefix perturbation of a table entry is strictly less
than twice the prefix error scale in either direction. Boundary errors
may be zero; no strictly positive error assumption is used. -/
lemma mixed_difference_error (t r00 r01 r10 r11 : ℝ)
    (h00 : 0 ≤ r00 ∧ r00 < t) (h01 : 0 ≤ r01 ∧ r01 < t)
    (h10 : 0 ≤ r10 ∧ r10 < t) (h11 : 0 ≤ r11 ∧ r11 < t) :
    -(2 * t) < r11 - r01 - r10 + r00 ∧
      r11 - r01 - r10 + r00 < 2 * t := by
  constructor <;> linarith only [h00.1, h00.2, h01.1, h01.2,
    h10.1, h10.2, h11.1, h11.2]

/-- Translation invariance for prefix-coordinate regions, including
nonmeasurable sets. -/
lemma volume_image_translate (v : E → ℝ) (S : Set (E → ℝ)) :
    volume ((fun z => v + z) '' S) = volume S := by
  have heq : (fun z => v + z) '' S = (fun z => -v + z) ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨-v + z, hz, by simp⟩
  rw [heq, measure_preimage_add]

/-- Nonnegative scalar dilation scales prefix-coordinate volume by the
coordinate dimension. -/
lemma volume_image_scale (t : ℝ) (ht : 0 ≤ t) (S : Set (E → ℝ)) :
    volume ((fun z => t • z) '' S) =
      ENNReal.ofReal (t ^ Fintype.card E) * volume S := by
  rw [Set.image_smul, Measure.addHaar_smul_of_nonneg volume ht,
    Module.finrank_fintype_fun_eq_card]

/-- A translated inclusion suffices for a volume comparison. The concrete
transportation-region inclusion remains an independent obligation. -/
lemma volume_le_of_translated_subset (v : E → ℝ) (S T : Set (E → ℝ))
    (h : (fun z => v + z) '' S ⊆ T) : volume S ≤ volume T := by
  rw [← volume_image_translate v S]
  exact measure_mono h

/-- A scaled-and-translated inclusion supplies the comparison factor. -/
lemma volume_le_of_subset_scaled_translate (t : ℝ) (ht : 0 ≤ t)
    (v : E → ℝ) (S T : Set (E → ℝ))
    (h : S ⊆ (fun z => v + t • z) '' T) :
    volume S ≤ ENNReal.ofReal (t ^ Fintype.card E) * volume T := by
  have heq : (fun z => v + t • z) '' T =
      (fun z => v + z) '' ((fun z => t • z) '' T) := by
    rw [Set.image_image]
  calc
    volume S ≤ volume ((fun z => v + t • z) '' T) := measure_mono h
    _ = ENNReal.ofReal (t ^ Fintype.card E) * volume T := by
      rw [heq, volume_image_translate, volume_image_scale t ht]

end

end Math115.LatticeCellVolume
