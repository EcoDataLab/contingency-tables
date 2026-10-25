/-
SPDX-License-Identifier: Apache-2.0
Bounded-bit correction of an actual partial repair. Failed padding remains
none; the success coin reuses the existing integer threshold and decoder.
-/
import ResearchPhysicalTraceJoin.GeneralTerminalLaw
import RepairAcceptanceThreshold

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open FirstSuccess ResidualMixture Math115.RepairAcceptanceCoin
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace

/-- Exactly k bits, including the failed-output branch. The supplied counter
is an ordinary function; no finite-type cardinality is computed here. -/
def partialBitTerminal {A : Type*} (out : Option A) (count : A → ℕ)
    (k c0 : ℕ) (bits : Fin k → Bool) : Option A :=
  match out with
  | none => none
  | some a => bitTerminal a k (min c0 (count a)) (count a) bits

noncomputable section
open scoped BigOperators Classical

namespace PartialRepairCorrection
variable {S A : Type*} [Fintype S] [Fintype A]

def finiteRow (out : Option A) (count : A → ℕ) (k c0 : ℕ) : RationalLaw (Option A) :=
  mapLaw (uniformLaw (α := Fin k → Bool)) (partialBitTerminal out count k c0)

lemma fibreSize_pos_of_some (f : S → Option A) (x : S) (a : A)
    (hx : f x = some a) : 0 < fibreSize f a :=
  Fintype.card_pos_iff.mpr ⟨⟨x,hx⟩⟩

/-- No conditioning on successful repairs: failure rows are identical, and
successful rows use the true fibre count and the existing clipped coin. -/
theorem finiteRow_variation (f : S → Option A) (count : A → ℕ)
    (hcount : ∀ a, count a = fibreSize f a) (k c0 : ℕ) (x : S) :
    variation (finiteRow (f x) count k c0) (row f c0 x) ≤ 1 / (2 : ℚ)^k := by
  cases hx : f x with
  | none =>
    simp only [finiteRow, partialBitTerminal, hx, row]
    rw [Math115.PhysicalCompletionOracle.mapLaw_constant]
    simp only [variation, sub_self, abs_zero, Finset.sum_const_zero, zero_div]
    exact (div_pos (by norm_num) (pow_pos (by norm_num) k)).le
  | some a =>
    have he : 0 < count a := by
      rw [hcount a]
      exact fibreSize_pos_of_some f x a hx
    have h := finiteBitLaw_variation_le a k (min c0 (count a)) (count a)
      he (min_le_right _ _)
    simp only [finiteRow, partialBitTerminal, hx, row]
    change variation (finiteBitLaw a k (min c0 (count a)) (count a))
      (clippedCoin a c0 (fibreSize f a)) ≤ _
    simpa only [clippedCoin, ← hcount a] using h

/-- Approximate endpoints and the fresh bounded coin are charged before
rejection, on the entire Option-valued output law. -/
theorem finiteRow_bind_variation (f : S → Option A) (count : A → ℕ)
    (hcount : ∀ a, count a = fibreSize f a) (k c0 : ℕ)
    (p q : RationalLaw S) :
    variation (bindLaw p (fun x => finiteRow (f x) count k c0))
      (bindLaw q (row f c0)) ≤ variation p q + 1 / (2 : ℚ)^k :=
  variation_bind_uniform _ _ _ _ _ (finiteRow_variation f count hcount k c0)

end PartialRepairCorrection
end
end Math115.PhysicalTraceJoin
