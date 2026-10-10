/-
SPDX-License-Identifier: Apache-2.0
The recover_display proof is adapted from OpenAI's IntegerLeafEnergy.lean
at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. New global owner and prefix
statements are added below that source-attributed recovery argument.
-/
import Mathlib.Tactic

/-!
# Global ownership of single-overfull displays

This module is independent of the large upstream proof tree. `eraseUnit` has
the same pointwise definition as upstream `removeOne`. Its maximum-recovery
proof is the existing `IntegerLeafEnergy.max_removeOne` argument, restated in
this independent abstraction. The new conclusion is global: even when the
special slot, adjacent level, and prefix vary, equal unordered exchange edges
have the same owner.

Connecting every physical context to these hypotheses is a separate task.
-/

namespace Math115.GlobalDisplayOwnership

def eraseUnit {C : Type*} [DecidableEq C] (D : C → ℕ) (i : C) : C → ℕ :=
  fun k => D k - if k = i then 1 else 0

/-- Existing maximum-recovery argument, with no positivity assumption needed. -/
lemma recover_display {C : Type*} [DecidableEq C] (D : C → ℕ) (i j : C)
    (hij : i ≠ j) :
    (fun k => max (eraseUnit D i k) (eraseUnit D j k)) = D := by
  funext k
  unfold eraseUnit
  by_cases hki : k = i
  · subst k
    simp only [hij, ↓reduceIte, Nat.sub_zero]
    exact max_eq_right (Nat.sub_le _ _)
  · by_cases hkj : k = j
    · subst k
      simp only [hki, ↓reduceIte, Nat.sub_zero]
      exact max_eq_left (Nat.sub_le _ _)
    · simp only [hki, hkj, ↓reduceIte, Nat.sub_zero, max_self]

def SameUnorderedPair {C : Type*} (X Y X' Y' : C → ℕ) : Prop :=
  (X = X' ∧ Y = Y') ∨ (X = Y' ∧ Y = X')

/-- Display recovery is global and does not depend on a fixed recursion root. -/
theorem display_unique {C : Type*} [DecidableEq C]
    (D D' : C → ℕ) (i j i' j' : C) (hij : i ≠ j) (hij' : i' ≠ j')
    (he : SameUnorderedPair
      (eraseUnit D i) (eraseUnit D j) (eraseUnit D' i') (eraseUnit D' j')) :
    D = D' := by
  rcases he with ⟨hX, hY⟩ | ⟨hX, hY⟩
  · calc
      D = fun k => max (eraseUnit D i k) (eraseUnit D j k) :=
        (recover_display D i j hij).symm
      _ = fun k => max (eraseUnit D' i' k) (eraseUnit D' j' k) := by rw [hX, hY]
      _ = D' := recover_display D' i' j' hij'
  · calc
      D = fun k => max (eraseUnit D i k) (eraseUnit D j k) :=
        (recover_display D i j hij).symm
      _ = fun k => max (eraseUnit D' j' k) (eraseUnit D' i' k) := by rw [hX, hY]
      _ = D' := recover_display D' j' i' (Ne.symm hij')

/-- Every ordinary pair has its prescribed occupancy; one special pair has
one extra unit. Widths may differ from slot to slot and may be zero. -/
def IsSpecialDisplay {S : Type*} [DecidableEq S]
    (U : S → ℕ) (special : S) (D : S × Bool → ℕ) : Prop :=
  ∀ t, D (t, false) + D (t, true) = U t + if t = special then 1 else 0

lemma special_unique {S : Type*} [DecidableEq S]
    (U : S → ℕ) (s s' : S) (D : S × Bool → ℕ)
    (hs : IsSpecialDisplay U s D) (hs' : IsSpecialDisplay U s' D) : s = s' := by
  by_contra hne
  have hself := hs s
  have hother := hs' s
  simp only [↓reduceIte] at hself
  simp only [hne, ↓reduceIte, Nat.add_zero] at hother
  omega

/-- A physical unordered exchange edge uniquely identifies the entire display,
the special slot, and its adjacent level, across all admissible displays. -/
theorem edge_owner_unique {S : Type*} [DecidableEq S]
    (U : S → ℕ) (s s' : S) (D D' : S × Bool → ℕ)
    (i j i' j' : S × Bool) (hij : i ≠ j) (hij' : i' ≠ j')
    (hs : IsSpecialDisplay U s D) (hs' : IsSpecialDisplay U s' D')
    (he : SameUnorderedPair
      (eraseUnit D i) (eraseUnit D j) (eraseUnit D' i') (eraseUnit D' j')) :
    D = D' ∧ s = s' ∧ D (s, false) = D' (s', false) := by
  have hd := display_unique D D' i j i' j' hij hij' he
  have hs'' : IsSpecialDisplay U s' D := by simpa only [hd] using hs'
  have hslot := special_unique U s s' D hs hs''
  exact ⟨hd, hslot, by rw [hd, hslot]⟩

/-- With any fixed exposure order, the prefix of the recovered special slot is
also recovered. No property of the order is needed beyond its being fixed. -/
theorem edge_prefix_unique {S : Type*} [DecidableEq S]
    (before : S → S → Prop) (U : S → ℕ) (s s' : S) (D D' : S × Bool → ℕ)
    (i j i' j' : S × Bool) (hij : i ≠ j) (hij' : i' ≠ j')
    (hs : IsSpecialDisplay U s D) (hs' : IsSpecialDisplay U s' D')
    (he : SameUnorderedPair
      (eraseUnit D i) (eraseUnit D j) (eraseUnit D' i') (eraseUnit D' j')) :
    s = s' ∧ D (s, false) = D' (s', false) ∧
      ∀ t, before t s → ∀ b, D (t, b) = D' (t, b) := by
  obtain ⟨hd, hslot, hlevel⟩ := edge_owner_unique U s s' D D' i j i' j'
    hij hij' hs hs' he
  exact ⟨hslot, hlevel, fun t _ b => congrFun hd (t, b)⟩

end Math115.GlobalDisplayOwnership
