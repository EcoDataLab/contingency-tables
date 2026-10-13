import Mathlib.Tactic

/-! Scalar finite-type degree arithmetic. No physical neighbor-count map is
asserted here: the six input formulae are the reviewed candidate bounds. -/
namespace Math115.ShapeDegreeBound

inductive CellType where
  | SS | LS | SL
  deriving DecidableEq

def count (m n R C : ℕ) : CellType → ℕ
  | .SS => (m - R) * (n - C)
  | .LS => R * (n - C)
  | .SL => (m - R) * C

def available (m n R C : ℕ) (s t : CellType) : Prop :=
  1 ≤ count m n R C s ∧ 1 ≤ count m n R C t ∧
    (s = t → 2 ≤ count m n R C s)

def bound (m n R C : ℕ) : CellType → CellType → ℕ
  | .SS, .SS => 2 * (m + n) - 3
  | .SS, .LS | .LS, .SS => n + 2 * m + (m-R)*C + R*(n-C) - 3
  | .SS, .SL | .SL, .SS => 2 * n + m + (m-R)*C + R*(n-C) - 3
  | .LS, .LS => 2 * ((m-R)*C + R*(n-C) + m) - 3
  | .SL, .SL => 2 * ((m-R)*C + R*(n-C) + n) - 3
  | .LS, .SL | .SL, .LS => 2 * ((m-R)*C + R*(n-C)) + m + n - 4

lemma count_identity (m n R C : ℕ) (hR : R ≤ m) (hC : C ≤ n) :
    m*n-R*C = (m-R)*(n-C) + (m-R)*C + R*(n-C) := by
  have hm : m = (m-R)+R := by omega
  have hn : n = (n-C)+C := by omega
  have hprod : m*n = ((m-R)*(n-C) + (m-R)*C + R*(n-C)) + R*C := by
    conv_lhs => rw [hm, hn]
    ring
  omega

lemma row_le_small_count (m n R C : ℕ) (hR : R ≤ m) (hC : C ≤ n)
    (hb : 1 ≤ n-C) : m ≤ m*n-R*C := by
  rw [count_identity m n R C hR hC]
  have hm : m = (m-R)+R := by omega
  have h := Nat.mul_le_mul_left m hb
  have heq : (m-R)*(n-C) + (m-R)*C + R*(n-C) = m*(n-C)+(m-R)*C := by
    calc
      _ = ((m-R)+R)*(n-C)+(m-R)*C := by ring
      _ = _ := by rw [←hm]
  rw [heq]
  omega

lemma col_le_small_count (m n R C : ℕ) (hR : R ≤ m) (hC : C ≤ n)
    (ha : 1 ≤ m-R) : n ≤ m*n-R*C := by
  rw [count_identity m n R C hR hC]
  have hn : n = (n-C)+C := by omega
  have h := Nat.mul_le_mul_right n ha
  have heq : (m-R)*(n-C) + (m-R)*C + R*(n-C) = (m-R)*n+R*(n-C) := by
    calc
      _ = (m-R)*((n-C)+C)+R*(n-C) := by ring
      _ = _ := by rw [←hn]
  rw [heq]
  omega

/-- Every available type pair has its displayed numerical allowance ≤4p−3.
Availability enforces positive cell counts, and two cells for same-type pairs.
This proves arithmetic of formulae, not a degree theorem about a state graph. -/
theorem available_bound_le (m n R C : ℕ) (_hm : 2 ≤ m) (_hn : 2 ≤ n)
    (hR : R ≤ m) (hC : C ≤ n) (hp : 2 ≤ m*n-R*C)
    (s t : CellType) (hav : available m n R C s t) :
    bound m n R C s t ≤ 4*(m*n-R*C)-3 := by
  have hab : (m-R)*C + R*(n-C) ≤ m*n-R*C := by
    rw [count_identity m n R C hR hC]
    omega
  have hr := row_le_small_count m n R C hR hC
  have hc := col_le_small_count m n R C hR hC
  rcases hav with ⟨hs, ht, _⟩
  cases s <;> cases t <;> simp only [count] at hs ht <;> simp only [bound]
  all_goals
    have ha : 1 ≤ m-R ∨ (m-R) = 0 := by omega
    have hb : 1 ≤ n-C ∨ (n-C) = 0 := by omega
    rcases ha with ha | ha <;> rcases hb with hb | hb
    all_goals try { simp [ha, hb] at hs ht }
    all_goals omega

/-- The six unordered type pairs used by the Python shape helper. -/
def typePairs : Finset (CellType × CellType) :=
  {(.SS,.SS), (.SS,.LS), (.SS,.SL), (.LS,.LS), (.SL,.SL), (.LS,.SL)}

noncomputable def degreeEnvelope (m n R C : ℕ) : ℕ := by
  classical
  exact (typePairs.filter fun st => available m n R C st.1 st.2).sup
    (fun st => bound m n R C st.1 st.2)

theorem degreeEnvelope_le (m n R C : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hR : R ≤ m) (hC : C ≤ n) (hp : 2 ≤ m*n-R*C) :
    degreeEnvelope m n R C ≤ 4*(m*n-R*C)-3 := by
  classical
  unfold degreeEnvelope
  apply Finset.sup_le
  intro st hst
  exact available_bound_le m n R C hm hn hR hC hp st.1 st.2 (Finset.mem_filter.mp hst).2

theorem degreeEnvelope_linear (m n R C : ℕ) :
    degreeEnvelope m n R C ≤ 2*(m*C+R*n+m+n) := by
  classical
  have hA := Nat.mul_le_mul_right C (Nat.sub_le m R)
  have hB := Nat.mul_le_mul_left R (Nat.sub_le n C)
  unfold degreeEnvelope
  apply Finset.sup_le
  intro st _
  rcases st with ⟨s,t⟩
  cases s <;> cases t <;> simp only [bound] <;> omega

theorem available_bound_pos (m n R C : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s t : CellType) (hav : available m n R C s t) :
    1 ≤ bound m n R C s t := by
  rcases hav with ⟨hs, ht, _⟩
  cases s <;> cases t <;> simp only [count] at hs ht <;> simp only [bound] <;> omega

theorem degreeEnvelope_pos (m n R C : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hR : R ≤ m) (hC : C ≤ n) (hp : 2 ≤ m*n-R*C) :
    1 ≤ degreeEnvelope m n R C := by
  classical
  have hsum := count_identity m n R C hR hC
  have hex : ∃ st ∈ typePairs, available m n R C st.1 st.2 := by
    by_cases hss : 2 ≤ (m-R)*(n-C)
    · exact ⟨(.SS,.SS), by simp [typePairs], by simp [available, count]; omega⟩
    by_cases hls : 2 ≤ R*(n-C)
    · exact ⟨(.LS,.LS), by simp [typePairs], by simp [available, count]; omega⟩
    by_cases hsl : 2 ≤ (m-R)*C
    · exact ⟨(.SL,.SL), by simp [typePairs], by simp [available, count]; omega⟩
    by_cases hsspos : 1 ≤ (m-R)*(n-C)
    · by_cases hlspos : 1 ≤ R*(n-C)
      · exact ⟨(.SS,.LS), by simp [typePairs], by simp [available, count]; omega⟩
      · exact ⟨(.SS,.SL), by simp [typePairs], by simp [available, count]; omega⟩
    · exact ⟨(.LS,.SL), by simp [typePairs], by simp [available, count]; omega⟩
  rcases hex with ⟨st, hst, hav⟩
  have hpos := available_bound_pos m n R C hm hn st.1 st.2 hav
  exact hpos.trans (Finset.le_sup (f := fun st => bound m n R C st.1 st.2)
    (Finset.mem_filter.mpr ⟨hst, hav⟩))

/-- Match the two optional minima in defect_degree_bound. -/
noncomputable def proposalAllowance (m n R C : ℕ) : ℕ :=
  let Q := min (8*(m*n-R*C)-7) (degreeEnvelope m n R C)
  if R=0 ∨ C=0 then min Q (2*(m+n)-3) else Q

theorem proposalAllowance_bounds (m n R C : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hR : R ≤ m) (hC : C ≤ n) (hp : 2 ≤ m*n-R*C) :
    1 ≤ proposalAllowance m n R C ∧ proposalAllowance m n R C ≤ 4*(m*n-R*C)-3 := by
  have hpos := degreeEnvelope_pos m n R C hm hn hR hC hp
  have hbound := degreeEnvelope_le m n R C hm hn hR hC hp
  have hminpos : 1 ≤ min (8*(m*n-R*C)-7) (degreeEnvelope m n R C) :=
    le_min (by omega) hpos
  have hminbound : min (8*(m*n-R*C)-7) (degreeEnvelope m n R C) ≤ 4*(m*n-R*C)-3 :=
    (min_le_right _ _).trans hbound
  unfold proposalAllowance
  split_ifs
  · exact ⟨le_min hminpos (by omega), (min_le_left _ _).trans hminbound⟩
  · exact ⟨hminpos, hminbound⟩

end Math115.ShapeDegreeBound
