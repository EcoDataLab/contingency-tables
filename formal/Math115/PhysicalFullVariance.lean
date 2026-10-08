/-
SPDX-License-Identifier: Apache-2.0
Extends localized transversal variance using the unchanged upstream
completion-retaining repair and positive-support encoding.
-/
import Math115.PhysicalExposureVariance
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperPhysicalVariance

namespace Math115.PhysicalFullVariance

open OAI.ContingencyTables
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance IntegerWeightedTransport
open SmallGraphProfiles
open Math115.PhysicalExposureVariance

universe u

noncomputable def transversalConstant (p U : ℕ) : ℝ :=
  ((U : ℝ) * ((U : ℝ) + 1) / 2) *
    (2 + ((p - 1 : ℕ) : ℝ) * ((U : ℝ) + 1)^2 / 2)

noncomputable def fullConstant (p U : ℕ) : ℝ :=
  (1 + 2 * (p : ℝ)^2) * transversalConstant p U + 2

lemma transversalConstant_nonnegative (p U : ℕ) : 0 ≤ transversalConstant p U := by
  unfold transversalConstant
  positivity

lemma fullConstant_nonnegative (p U : ℕ) : 0 ≤ fullConstant p U := by
  unfold fullConstant
  have h := transversalConstant_nonnegative p U
  positivity

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The original finite repair inequality extends the localized bound to all
actual balanced words and positive defect profiles. This deliberately keeps
the source's factor-two repair estimate for a complete first integration. -/
theorem physical_full_variance_localized
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hU : 2 ≤ U)
    (hB : ∀ i j, firstPaperSmall r c U i j = true → B i j = U)
    (hlarge : ∀ i j, firstPaperSmall r c U i j = false → 2 ≤ B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i + rowLargeCount (firstPaperSmall r c U) i * L)
      (fun j => c j + columnLargeCount (firstPaperSmall r c U) j * L),
      ∀ i j, T.val.val i j ≤ B i j)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    let w := wordWeight small B r c L U
    let v := fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val)
    let G := wordObservable small U H
    let K := fun z : PositiveDefects small B r c L => H (naturalProfile z.val)
    variance (Sum.elim w v) (Sum.elim G K) ≤
      fullConstant (Fintype.card (Cells small)) U * fullEnergy r c U L B hB H := by
  dsimp only
  let small := firstPaperSmall r c U
  let p := Fintype.card (Cells small)
  let E := fullEnergy r c U L B hB H
  have hvar : variance (wordWeight small B r c L U) (wordObservable small U H) ≤
      transversalConstant p U * E := by
    exact (physical_transversal_variance_localized small B r c L U hU hB hlarge hcap H).trans
      (mul_le_mul_of_nonneg_left (physicalEnergy_le_full r c U L B hB H)
        (transversalConstant_nonnegative p U))
  have hrepair := actual_repair_energy_le r c U L B hB hcap H
  have hv := variance_sum_repair (wordWeight small B r c L U)
    (fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val))
    (wordObservable small U H) (fun z => H (naturalProfile z.val))
    (repairWord r c U L B hB) (defectLabels small B r c L)
    (fun a => hardMarginal_nonnegative _ _ _ _ _ _) (fun z => le_of_lt z.property.2)
    (repairWord_weight r c U L B hB hcap) (repairWord_type_injective r c U L B hB)
  have hcoef : (1 + 2 * (Fintype.card (Cells small × Cells small) : ℝ)) =
      1 + 2 * (p : ℝ)^2 := by simp only [Fintype.card_prod, Nat.cast_mul, p, pow_two]
  rw [hcoef] at hv
  calc
    _ ≤ _ := hv
    _ ≤ (1 + 2 * (p : ℝ)^2) * (transversalConstant p U * E) + 2 * E :=
      add_le_add (mul_le_mul_of_nonneg_left hvar (by positivity))
        (mul_le_mul_of_nonneg_left hrepair (by norm_num))
    _ = _ := by unfold fullConstant; ring

/-- The bound holds for every observable on the actual positive-weight
physical state space, using the unchanged support-removal identity. -/
theorem physical_variance_localized
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hU : 2 ≤ U)
    (hB : ∀ i j, firstPaperSmall r c U i j = true → B i j = U)
    (hlarge : ∀ i j, firstPaperSmall r c U i j = false → 2 ≤ B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i + rowLargeCount (firstPaperSmall r c U) i * L)
      (fun j => c j + columnLargeCount (firstPaperSmall r c U) j * L),
      ∀ i j, T.val.val i j ≤ B i j)
    (H : PhysicalStates (firstPaperSmall r c U) B r c L → ℝ) :
    let small := firstPaperSmall r c U
    variance (fun z => hardMarginal small B r c L (physicalProfile small B r c L z)) H ≤
      fullConstant (Fintype.card (Cells small)) U *
        fullEnergy r c U L B hB (physicalExtension small B r c L H) := by
  dsimp only
  let small := firstPaperSmall r c U
  let G := physicalExtension small B r c L H
  have hext : ∀ z : PhysicalStates small B r c L, G (naturalProfile z.val.val) = H z :=
    physicalExtension_at small B r c L H
  have hv := variance_positive_support
    (fun z : Profiles small B => hardMarginal small B r c L (naturalProfile z.val))
    (fun z => G (naturalProfile z.val)) (fun _ => hardMarginal_nonnegative _ _ _ _ _ _)
  have hv' : variance (fun z : PhysicalStates small B r c L =>
      hardMarginal small B r c L (physicalProfile small B r c L z)) H =
      variance (fun z : Profiles small B => hardMarginal small B r c L (naturalProfile z.val))
        (fun z => G (naturalProfile z.val)) := by
    simpa only [physicalProfile, hext] using hv
  rw [hv', ← encoding_variance_eq small B r c L U hB G]
  exact physical_full_variance_localized r c U L B hU hB hlarge hcap G

end Math115.PhysicalFullVariance
