/-
SPDX-License-Identifier: Apache-2.0
The exact finite rational law of the actual physical chain at free U,L.
Count-ratio laws and their cast identities do not implement an oracle or
assert a machine-cost bound.
-/
import Math115.PhysicalStationaryLaw
import OAI.Combinatorics.ContingencyTables.Transport.RationalChainMixing

namespace Math115.PhysicalRationalKernel

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open ReducedSmallChain ReducedAllSmallChain SmallGraphProfiles CompletionCounts
open CompletionTranslation ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

def proposalRat (d : ℕ) : ℚ := 1 / (2 : ℚ)^Nat.clog 2 (32 * d^2)

lemma proposalRat_cast (d : ℕ) : (proposalRat d : ℝ) = smallProposal d := by
  simp only [proposalRat, smallProposal, Rat.cast_div, Rat.cast_one,
    Rat.cast_pow, Rat.cast_ofNat]

/-- Transport probability laws through an exact rational-to-real kernel identity. -/
def lawOfCast {X : Type*} [Fintype X] (C : FiniteChain X) (P : X → X → ℚ)
    (hP : ∀ x y, (P x y : ℝ) = C.P x y) (x : X) : RationalLaw X where
  mass := P x
  nonnegative := fun y => by
    have h := C.nonnegative x y
    rw [← hP] at h
    exact_mod_cast h
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum, hP, Rat.cast_one]
    exact C.stochastic x

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def referenceMoveRat (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (x y : States r c U L) : ℚ :=
  if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y then
    proposalRat (dimensionAllowance (I := I) (J := J)) *
      (acceptedCount (referenceRows r c U L (capacity r c U L) i₀)
        (referenceColumns r c U L (capacity r c U L) j₀) x y : ℚ) /
      (blockCount (referenceRows r c U L (capacity r c U L) i₀)
        (referenceColumns r c U L (capacity r c U L) j₀) x : ℚ)
  else 0

def referenceTransitionRat (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (x y : States r c U L) : ℚ :=
  referenceMoveRat r c U L i₀ j₀ x y +
    if x = y then 1 - ∑ z, referenceMoveRat r c U L i₀ j₀ x z else 0

lemma referenceMoveRat_cast (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (x y : States r c U L) :
    (referenceMoveRat r c U L i₀ j₀ x y : ℝ) =
      completionMove (referenceRows r c U L (capacity r c U L) i₀)
        (referenceColumns r c U L (capacity r c U L) j₀)
        (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L))
        (smallProposal (dimensionAllowance (I := I) (J := J))) x y := by
  unfold referenceMoveRat completionMove
  split_ifs
  · simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, proposalRat_cast]
  · exact Rat.cast_zero

lemma referenceTransitionRat_cast (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x y : States r c U L) :
    (referenceTransitionRat r c U L i₀ j₀ x y : ℝ) =
      (ReducedSmallChain.chain r c U L i₀ j₀).P x y := by
  unfold referenceTransitionRat
  dsimp only [ReducedSmallChain.chain, completionChain, FiniteChain.ofMoves]
  by_cases hxy : x = y <;>
    simp only [hxy, ite_true, ite_false, Rat.cast_add, Rat.cast_sub,
      Rat.cast_sum, Rat.cast_one, Rat.cast_zero, referenceMoveRat_cast]

def referenceTransitionLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x : States r c U L) : RationalLaw (States r c U L) :=
  lawOfCast (ReducedSmallChain.chain r c U L i₀ j₀)
    (referenceTransitionRat r c U L i₀ j₀) (referenceTransitionRat_cast r c U L i₀ j₀) x

def unitMoveRat (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x y : States r c U L) : ℚ :=
  if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y then
    proposalRat (dimensionAllowance (I := I) (J := J)) else 0

def unitTransitionRat (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x y : States r c U L) : ℚ :=
  unitMoveRat r c U L x y + if x = y then 1 - ∑ z, unitMoveRat r c U L x z else 0

lemma unitMoveRat_cast (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (x y : States r c U L) :
    (unitMoveRat r c U L x y : ℝ) =
      MetropolisChain.move (fun _ : States r c U L => (1 : ℝ))
        (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L))
        (smallProposal (dimensionAllowance (I := I) (J := J))) x y := by
  unfold unitMoveRat MetropolisChain.move
  split_ifs
  · simp only [proposalRat_cast, div_self (by norm_num : (1 : ℝ) ≠ 0), min_self, mul_one]
  · exact Rat.cast_zero

lemma unitTransitionRat_cast (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (x y : States r c U L) :
    (unitTransitionRat r c U L x y : ℝ) = (unitChain r c U L).P x y := by
  unfold unitTransitionRat
  dsimp only [unitChain, MetropolisChain.chain, FiniteChain.ofMoves]
  by_cases hxy : x = y <;>
    simp only [hxy, ite_true, ite_false, Rat.cast_add, Rat.cast_sub,
      Rat.cast_sum, Rat.cast_one, Rat.cast_zero, unitMoveRat_cast]

def unitTransitionLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (x : States r c U L) : RationalLaw (States r c U L) :=
  lawOfCast (unitChain r c U L) (unitTransitionRat r c U L)
    (unitTransitionRat_cast r c U L) x

/-- Exactly the reference/unit branch predicate and choices used by the actual chain. -/
def selectedTransitionLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] : States r c U L → RationalLaw (States r c U L) :=
  if h : Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U) then
    referenceTransitionLaw r c U L (Classical.choice h.1) (Classical.choice h.2)
  else unitTransitionLaw r c U L

theorem selectedTransitionLaw_cast (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (x y : States r c U L) :
    ((selectedTransitionLaw r c U L x).mass y : ℝ) =
      (ReducedAllSmallChain.selectedChain r c U L).P x y := by
  unfold selectedTransitionLaw ReducedAllSmallChain.selectedChain
  split_ifs with h
  · exact referenceTransitionRat_cast r c U L (Classical.choice h.1) (Classical.choice h.2) x y
  · exact unitTransitionRat_cast r c U L x y

def selectedWalkLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (x : States r c U L) (n : ℕ) :
    RationalLaw (States r c U L) := walkLaw (selectedTransitionLaw r c U L) x n

theorem selectedWalkLaw_cast (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (n : ℕ) (x y : States r c U L) :
    ((selectedWalkLaw r c U L x n).mass y : ℝ) =
      ((ReducedAllSmallChain.selectedChain r c U L).kernel.power n).P x y :=
  walkLaw_cast_kernel _ _ (selectedTransitionLaw_cast r c U L) n x y

end
end Math115.PhysicalRationalKernel
