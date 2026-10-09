/-
SPDX-License-Identifier: Apache-2.0
Free-scale physical mass bounds, preserving every completion and defect.
-/
import Math115.PhysicalStateNonempty
import OAI.Combinatorics.ContingencyTables.Transport.BalancedCompletionMass

set_option maxHeartbeats 1200000

namespace Math115.PhysicalStationaryMass

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open ReducedSmallChain PhysicalStateNonempty
open SmallGraphProfiles SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres
open FirstPaperProfiles FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physical_mass_eq_profiles (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) :
    (∑ z : PhysicalStates small B r c L,hardMarginal small B r c L
      (physicalProfile small B r c L z))=
      ∑ z : Profiles small B,hardMarginal small B r c L (naturalProfile z.val) := by
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro z hz
    have hn : ¬0 < hardMarginal small B r c L (naturalProfile z.val) := by
      intro hp
      exact hz ⟨⟨z,hp⟩,rfl⟩
    exact le_antisymm (le_of_not_gt hn) (hardMarginal_nonnegative _ _ _ _ _ _)
  · intro z
    rfl

lemma physical_mass_eq_words_defects (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    (∑ z : PhysicalStates small B r c L,hardMarginal small B r c L
      (physicalProfile small B r c L z))=
      (∑ a,wordWeight small B r c L U a)+
      ∑ z : PositiveDefects small B r c L,hardMarginal small B r c L (naturalProfile z.val) := by
  rw [physical_mass_eq_profiles]
  have he := Fintype.sum_of_injective (encodeProfile small B r c L U hB)
    (encodeProfile_injective small B r c L U hB)
    (fun z => hardMarginal small B r c L (naturalProfile (encodeProfile small B r c L U hB z).val))
    (fun z => hardMarginal small B r c L (naturalProfile z.val))
    (outside_encoding_weight_zero small B r c L U hB) (fun _ => rfl)
  rw [← he,Fintype.sum_sum_type]
  rfl

/-- The repair preserves all completions and has at most one preimage per
ordered defect label. Thus defect mass costs at most |S| squared. -/
lemma defect_mass_le_words (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j ≤ B i j) :
    (∑ z : PositiveDefects (firstPaperSmall r c U) B r c L,
      hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val)) ≤
      (Fintype.card (Cells (firstPaperSmall r c U)×Cells (firstPaperSmall r c U)):ℝ)*
        ∑ a,wordWeight (firstPaperSmall r c U) B r c L U a := by
  have h := repair_center_mass (wordWeight (firstPaperSmall r c U) B r c L U)
    (fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
      hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val))
    (fun _ => (1:ℝ)) (repairWord r c U L B hB) (defectLabels _ B r c L)
    (fun _ => hardMarginal_nonnegative _ _ _ _ _ _)
    (repairWord_weight r c U L B hB hcap) (repairWord_type_injective r c U L B hB) 0
  simpa only [sub_zero,one_pow,mul_one] using h

abbrev PaddedTables (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :=
  Table (fun i => r i + rowLargeCount (firstPaperSmall r c U) i * L)
    (fun j => c j + columnLargeCount (firstPaperSmall r c U) j * L)

noncomputable def normalizer (r : I → ℕ) (c : J → ℕ) (U L : ℕ) : ℝ :=
  ∑ z : States r c U L, weight r c U L z

/-- The exact physical normalizer is controlled by padded ordinary tables.
No total-margin, positive-margin, or scale hypothesis is needed. -/
theorem normalizer_le_padded_count (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :
    normalizer r c U L ≤
      (1 + (Fintype.card (Cells (firstPaperSmall r c U)) : ℝ)^2) *
        (Fintype.card (PaddedTables r c U L) : ℝ) := by
  let small := firstPaperSmall r c U
  let B := capacity r c U L
  let W := ∑ a, wordWeight small B r c L U a
  have hB : ∀ i j, small i j = true → B i j = U := capacity_small r c U L
  have hcap := paper_residual_capacity r c (dimensionAllowance (I := I) (J := J)) L U
    dimension_le_allowance
  have hmass := physical_mass_eq_words_defects small B r c L U hB
  have hdef := defect_mass_le_words r c U L B hB hcap
  have hword := word_mass_le_padded_count small B r c L U hB
  have hfactor : 0 ≤ 1 + (Fintype.card (Cells small) : ℝ)^2 := by positivity
  have hZ : normalizer r c U L ≤ (1 + (Fintype.card (Cells small) : ℝ)^2) * W := by
    change (∑ z : PhysicalStates small B r c L, hardMarginal small B r c L
      (physicalProfile small B r c L z)) ≤ _
    rw [hmass]
    simp only [Fintype.card_prod, Nat.cast_mul] at hdef
    dsimp only [W]
    nlinarith only [hdef]
  exact hZ.trans (mul_le_mul_of_nonneg_left hword hfactor)

/-- A count ratio transfers to the actual defect-augmented normalizer. -/
theorem normalizer_le_original_count (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (A : ℝ) (hcount : (Fintype.card (PaddedTables r c U L) : ℝ) ≤
      A * (Fintype.card (Table r c) : ℝ)) :
    normalizer r c U L ≤
      (A * (1 + (Fintype.card (Cells (firstPaperSmall r c U)) : ℝ)^2)) *
        (Fintype.card (Table r c) : ℝ) := by
  have h := (normalizer_le_padded_count r c U L).trans
    (mul_le_mul_of_nonneg_left hcount (by positivity))
  convert h using 1
  ring

lemma normalizer_positive (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) : 0 < normalizer r c U L := by
  let := states_nonempty r c U L htotal
  exact Finset.sum_pos (fun z _ => weight_positive r c U L z) Finset.univ_nonempty

/-- The denominator is positive under equal ordinary total margins. -/
theorem success_ratio_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (A : ℝ) (hA : 0 < A)
    (hcount : (Fintype.card (PaddedTables r c U L) : ℝ) ≤
      A * (Fintype.card (Table r c) : ℝ)) :
    1 / (A * (1 + (Fintype.card (Cells (firstPaperSmall r c U)) : ℝ)^2)) ≤
      (Fintype.card (Table r c) : ℝ) / normalizer r c U L := by
  have hZ := normalizer_positive r c U L htotal
  apply (div_le_div_iff₀ (by positivity) hZ).mpr
  simpa only [one_mul, mul_comm] using normalizer_le_original_count r c U L A hcount

end Math115.PhysicalStationaryMass
