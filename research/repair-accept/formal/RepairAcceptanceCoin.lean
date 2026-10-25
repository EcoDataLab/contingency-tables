import OAI.Combinatorics.ContingencyTables.Transport.RejectionLaw

namespace Math115.RepairAcceptanceCoin

open OAI.ContingencyTables.ResidualMixture OAI.ContingencyTables.FirstSuccess
open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Accept the fixed output `a` with rational probability `q`, otherwise fail. -/
def coinLaw (a : A) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : RationalLaw (Option A) where
  mass := fun z => match z with
    | none => 1 - q
    | some b => if b = a then q else 0
  nonnegative := fun z => by
    cases z with
    | none => exact sub_nonneg.mpr hq1
    | some b => by_cases h : b = a <;> simp [h, hq0]
  total := by simp

@[simp] theorem coinLaw_mass_none (a : A) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (coinLaw a q hq0 hq1).mass none = 1 - q := rfl

@[simp] theorem coinLaw_mass_some (a b : A) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (coinLaw a q hq0 hq1).mass (some b) = if b = a then q else 0 := rfl

/-- The optional-output law differs by precisely the acceptance-probability error. -/
theorem coinLaw_variation (a : A) (q r : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    variation (coinLaw a q hq0 hq1) (coinLaw a r hr0 hr1) = |q - r| := by
  unfold variation
  have hs : (∑ b : A, |(if b = a then q else 0) - (if b = a then r else 0)|) =
      |q - r| := by
    have hp (b : A) : |(if b = a then q else 0) - (if b = a then r else 0)| =
        if b = a then |q - r| else 0 := by
      split_ifs <;> simp
    simp_rw [hp]
    simp
  simp only [Fintype.sum_option, coinLaw_mass_none, coinLaw_mass_some, hs]
  have hn : |(1 - q) - (1 - r)| = |q - r| := by
    rw [show (1 - q) - (1 - r) = -(q - r) by ring, abs_neg]
  rw [hn]
  ring

end Math115.RepairAcceptanceCoin
