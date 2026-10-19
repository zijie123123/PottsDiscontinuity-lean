module

public import PottsDiscontinuity.Bethe.RatioInteriorQuadrature
public import PottsDiscontinuity.Bethe.RatioLogDifference

/-! # Uniform domination of the actual logarithmic quadrature tests -/

@[expose] public section

open Set Finset
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem ratio_profile_bound_nonneg {c : ℝ} (hc : 2 < c) :
    0 ≤ Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4 := by
  have hc2 : 4 < c ^ 2 := by nlinarith
  exact add_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (sq_nonneg _))
    (by positivity)

/-- The scaled root log difference is bounded even at an exactly zero root:
linear displacement control then forces the aligned root to be zero too. -/
theorem ratio_scaled_root_log_bound {c x y C : ℝ} {N : ℕ}
    (hc : 2 < c) (hN : 0 < N) (hC : 0 ≤ C) (hlarge : 2 * C ≤ N)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hy : y ∈ Ioo (-Real.pi) Real.pi)
    (hshift : |(N : ℝ) * (x - y)| ≤ C * |x|) :
    |(N : ℝ) * (ratioEll c x - ratioEll c y)| ≤
      2 * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4) * C := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  by_cases hx0 : x = 0
  · have heq : (N : ℝ) * (x - y) = 0 := abs_nonpos_iff.mp (by simpa [hx0] using hshift)
    have hxy := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hNp.ne')
    rw [hxy, sub_self, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (ratio_profile_bound_nonneg hc)) hC
  have hsmall : |y - x| ≤ C * |x| / N := by
    apply (le_div_iff₀ hNp).mpr
    rw [abs_mul, abs_of_pos hNp, abs_sub_comm x y] at hshift
    nlinarith only [hshift]
  have hh := ratio_scaled_ell_difference_bound hc hN hlarge hx hy hx0 hsmall
  simpa only [abs_mul, abs_sub_comm (ratioEll c y) (ratioEll c x)] using hh

/-- A single compactly supported majorant for the logarithmic step tests. -/
theorem ratio_log_step_bound {k N : ℕ} {q a : Fin (k + 1) → ℝ}
    {c C M : ℝ} (hc : 2 < c) (hN : 0 < N) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hlarge : 2 * C ≤ N) (hq : q ∈ S_n (k + 1))
    (ha : ∀ j, a j ∈ Ioo (-Real.pi) Real.pi) (hs : 2 * (k + 1) ≤ N)
    (hshift : ∀ j, |(N : ℝ) * (q j - a j)| ≤ C * |q j|)
    (hρ : ∀ x ∈ Icc (-Real.pi) Real.pi,
      rootStepDensity N (k + 1) q hq (by omega) hs x ≤ M) (x : ℝ) :
    |ratioInteriorTest N q hq (fun j => (N : ℝ) * (ratioEll c (q j) - ratioEll c (a j))) x| ≤
      (Icc (-Real.pi) Real.pi).indicator
        (fun _ => (2 * (Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4) * C) * M) x := by
  apply ratio_interiorTest_bound hq hs _
    (mul_nonneg (mul_nonneg (by norm_num) (ratio_profile_bound_nonneg hc)) hC) hM
  · intro j
    exact ratio_scaled_root_log_bound hc hN hC hlarge (hq.1 j) (ha j) (hshift j)
  · exact hρ

end PottsDiscontinuity.Bethe
