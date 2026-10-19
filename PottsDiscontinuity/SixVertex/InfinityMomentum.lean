module

public import Mathlib

/-! # Evaluation of the centered momentum product -/

@[expose] public section

open Finset

namespace PottsDiscontinuity.SixVertex

/-- The product of the `2r` one-particle eigenvalues at consecutive centered momenta. -/
noncomputable def centeredCosineProduct (r : ℕ) (L : ℝ) : ℝ :=
  ∏ a ∈ range (2 * r), 2 * Real.cos (Real.pi * (2 * (a : ℝ) + 1 - 2 * r) / L)

/-- Pairing opposite momenta gives exactly the cosine product in (3.2).
This is a scalar identity; identifying it as a matrix eigenvalue is a separate step. -/
theorem centeredCosineProduct_eq (r : ℕ) (L : ℝ) :
    centeredCosineProduct r L =
      2 ^ r * ∏ j ∈ range r, (1 + Real.cos (2 * Real.pi * (2 * (j : ℝ) + 1) / L)) := by
  let f : ℕ → ℝ := fun j => 2 * Real.cos (Real.pi * (2 * (j : ℝ) + 1) / L)
  have hneg : (∏ a ∈ range r,
      2 * Real.cos (Real.pi * (2 * (a : ℝ) + 1 - 2 * r) / L)) =
      ∏ j ∈ range r, f j := by
    rw [← prod_range_reflect f r]
    apply prod_congr rfl
    intro a ha
    have ha' : a < r := mem_range.mp ha
    have he : ((r - 1 - a : ℕ) : ℝ) = (r : ℝ) - 1 - a := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      norm_num
    dsimp [f]
    rw [he]
    have ht : Real.pi * (2 * (a : ℝ) + 1 - 2 * r) / L =
        -(Real.pi * (2 * ((r : ℝ) - 1 - a) + 1) / L) := by ring
    rw [ht, Real.cos_neg]
  have hpos : (∏ a ∈ range r,
      2 * Real.cos (Real.pi * (2 * ((r + a : ℕ) : ℝ) + 1 - 2 * r) / L)) =
      ∏ j ∈ range r, f j := by
    apply prod_congr rfl
    intro a _
    dsimp [f]
    congr 2
    push_cast
    ring
  unfold centeredCosineProduct
  rw [show 2 * r = r + r by omega, prod_range_add, hneg, hpos, ← prod_mul_distrib]
  have he : ∀ j : ℕ, f j * f j =
      2 * (1 + Real.cos (2 * Real.pi * (2 * (j : ℝ) + 1) / L)) := by
    intro j
    dsimp [f]
    have ht : 2 * Real.pi * (2 * (j : ℝ) + 1) / L =
        2 * (Real.pi * (2 * (j : ℝ) + 1) / L) := by ring
    rw [ht, Real.cos_two_mul]
    ring
  simp_rw [he]
  rw [prod_mul_distrib, prod_const, card_range]

/-- The source's normalization `L = N+2r = 2(n+2r)`. -/
theorem centeredCosineProduct_source (n r : ℕ) :
    centeredCosineProduct r (2 * ((n : ℝ) + 2 * r)) =
      2 ^ r * ∏ j ∈ range r,
        (1 + Real.cos (Real.pi * (2 * (j : ℝ) + 1) / ((n : ℝ) + 2 * r))) := by
  rw [centeredCosineProduct_eq]
  congr 1
  apply prod_congr rfl
  intro j hj
  congr 2
  have hr : 0 < r := (Nat.zero_le j).trans_lt (mem_range.mp hj)
  have hD : (n : ℝ) + 2 * r ≠ 0 := by positivity
  field_simp

end PottsDiscontinuity.SixVertex
