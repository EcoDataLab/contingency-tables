/- Scalar lemmas for shape-dependent sequential padding growth. -/
import Math115.PaddingGrowthAlgebra

namespace Research.GrowthRefinement

theorem pair_amgm (H a b : ℕ) :
    4 * (H + a) * (H + b) ≤ (2 * H + a + b)^2 := by
  zify
  nlinarith only [sq_nonneg ((a : ℤ) - b)]

theorem doubled_one_step (enlarged original H a b : ℕ)
    (hgrowth : enlarged * H^2 ≤ original * (H+a) * (H+b)) :
    enlarged * (2*H)^2 ≤ original * (2*H+a+b)^2 := by
  have hm := Nat.mul_le_mul_left original (pair_amgm H a b)
  have hg := Nat.mul_le_mul_left 4 hgrowth
  nlinarith only [hm, hg]

theorem doubled_growth_twice (enlarged original q H s : ℕ) (hH : 0 < H)
    (hgrowth : enlarged * (2*H)^(2*q) ≤ original * (2*H+s)^(2*q))
    (hbudget : 47*q*s ≤ 32*H) : enlarged ≤ 2*original := by
  have he : 2*H-1+1=2*H := by omega
  apply Math115.PaddingGrowthAlgebra.count_le_twice_of_growth
    enlarged original (2*q) (2*H-1) s
  · simpa only [he] using hgrowth
  · rw [he]
    nlinarith only [hbudget]

theorem shape_cutoff_budget (g d s : ℕ) (hg : g ≤ d) :
    47*(7*g)*s ≤ 32*(11*d*s+1) := by
  have h := Nat.mul_le_mul_right s
    (Nat.mul_le_mul_left 47 (Nat.mul_le_mul_left 7 hg))
  nlinarith only [h]

theorem shape_gap (K p V d s : ℕ) (hp : p ≤ d)
    (hV : V ≤ 11*d*s) (hK : K ≤ 32*p^4*V^3) :
    K ≤ 42592*d^7*s^3 := by
  have hp4 := Nat.pow_le_pow_left hp 4
  have hV3 := Nat.pow_le_pow_left hV 3
  calc
    K ≤ 32*p^4*V^3 := hK
    _ ≤ 32*d^4*(11*d*s)^3 := Nat.mul_le_mul (Nat.mul_le_mul_left 32 hp4) hV3
    _ = 42592*d^7*s^3 := by ring

theorem bounded_aspect_gap_squared (K d s A : ℕ)
    (hK : K ≤ 42592*d^7*s^3) (haspect : s^2 ≤ A*d) :
    K^2 ≤ 42592^2*A^3*d^17 := by
  have hK2 := Nat.pow_le_pow_left hK 2
  have hS3 := Nat.pow_le_pow_left haspect 3
  calc
    K^2 ≤ (42592*d^7*s^3)^2 := hK2
    _ = (42592^2*d^14)*(s^2)^3 := by ring
    _ ≤ (42592^2*d^14)*(A*d)^3 := Nat.mul_le_mul_left _ hS3
    _ = 42592^2*A^3*d^17 := by ring

theorem arbitrary_aspect_constant (K d s : ℕ)
    (hK : K ≤ 42592*d^7*s^3) (hshape : 3*s ≤ d) :
    27*K ≤ 42592*d^10 := by
  have hS3 := Nat.pow_le_pow_left hshape 3
  calc
    27*K ≤ 27*(42592*d^7*s^3) := Nat.mul_le_mul_left 27 hK
    _ = (42592*d^7)*(3*s)^3 := by ring
    _ ≤ (42592*d^7)*d^3 := Nat.mul_le_mul_left _ hS3
    _ = 42592*d^10 := by ring

/-- Width-square transport at the same preselected shape cutoff. -/
theorem shape_gap_width_square (K p V d s : ℕ) (hp : p ≤ d)
    (hV : V ≤ 11*d*s) (hK : K ≤ 32*p^4*V^2) :
    K ≤ 3872*d^6*s^2 := by
  have hp4 := Nat.pow_le_pow_left hp 4
  have hV2 := Nat.pow_le_pow_left hV 2
  calc
    K ≤ 32*p^4*V^2 := hK
    _ ≤ 32*d^4*(11*d*s)^2 := Nat.mul_le_mul (Nat.mul_le_mul_left 32 hp4) hV2
    _ = 3872*d^6*s^2 := by ring

theorem bounded_aspect_gap_width_square (K d s A : ℕ)
    (hK : K ≤ 3872*d^6*s^2) (haspect : s^2 ≤ A*d) :
    K ≤ 3872*A*d^7 := by
  calc
    K ≤ 3872*d^6*s^2 := hK
    _ ≤ (3872*d^6)*(A*d) := Nat.mul_le_mul_left _ haspect
    _ = 3872*A*d^7 := by ring

theorem arbitrary_aspect_width_square (K d s : ℕ)
    (hK : K ≤ 3872*d^6*s^2) (hshape : 3*s ≤ d) :
    9*K ≤ 3872*d^8 := by
  have hS2 := Nat.pow_le_pow_left hshape 2
  calc
    9*K ≤ 9*(3872*d^6*s^2) := Nat.mul_le_mul_left 9 hK
    _ = (3872*d^6)*(3*s)^2 := by ring
    _ ≤ (3872*d^6)*d^2 := Nat.mul_le_mul_left _ hS2
    _ = 3872*d^8 := by ring

theorem arbitrary_aspect_width_square_integer (K d : ℕ)
    (hK : 9*K ≤ 3872*d^8) : K ≤ 431*d^8 := by
  omega

end Research.GrowthRefinement

#print axioms Research.GrowthRefinement.doubled_growth_twice
#print axioms Research.GrowthRefinement.shape_gap
#print axioms Research.GrowthRefinement.bounded_aspect_gap_squared
#print axioms Research.GrowthRefinement.shape_gap_width_square
#print axioms Research.GrowthRefinement.bounded_aspect_gap_width_square
#print axioms Research.GrowthRefinement.arbitrary_aspect_width_square
#print axioms Research.GrowthRefinement.arbitrary_aspect_width_square_integer
