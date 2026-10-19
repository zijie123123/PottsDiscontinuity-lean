module

public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# Scalar scattering identities for the coordinate Bethe Ansatz

Companion paper arXiv:1611.09909v1, Lemma `lem:ratios`, equation (6), and equation (19).
The positivity of the real part of `S` makes all scattering factors nonzero for `Δ < -1`.
The Bethe equations and distinctness of the roots are not needed for these identities.
-/

@[expose] public section

open Complex

namespace PottsDiscontinuity.BetheAnsatz

open Bethe

theorem scattering_re (Δ x y : ℝ) :
    (scattering Δ x y).re = Real.cos x + Real.cos y - 2 * Δ := by
  rw [scattering, z, exp_neg_I_mul_ofReal, exp_I_mul_ofReal]
  simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero]
  norm_num

theorem scattering_re_pos {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    0 < (scattering Δ x y).re := by
  rw [scattering_re]
  exact cos_add_cos_sub_pos hΔ x y

theorem scattering_ne_zero {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    scattering Δ x y ≠ 0 := by
  intro h
  have := scattering_re_pos hΔ x y
  rw [h] at this
  exact (lt_irrefl 0) this

/-- On the momentum interval used in Theorem 3.1, only the zero root gives `z = 1`. -/
theorem z_ne_one {p : ℝ} (hp : p ∈ Set.Ioo (-Real.pi) Real.pi) (hp0 : p ≠ 0) :
    z p ≠ 1 := by
  intro h
  have h' : Complex.exp (I * (p : ℂ)) = Complex.exp 0 := by simpa [z] using h
  have heq := (Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by simpa using hp.1) (by simpa using hp.2.le)
    (by simpa using (neg_lt_zero.mpr Real.pi_pos)) (by simpa using Real.pi_pos.le)) h'
  apply hp0
  simpa using congrArg Complex.im heq

theorem scattering_eq_inv_z (Δ x y : ℝ) :
    scattering Δ x y = (z x)⁻¹ + z y - 2 * (Δ : ℂ) := by
  rw [scattering, Complex.exp_neg]
  rfl

theorem z_mul_scattering (Δ x y : ℝ) :
    z x * scattering Δ x y = 1 + z x * z y - 2 * (Δ : ℂ) * z x := by
  rw [scattering_eq_inv_z, mul_sub, mul_add, mul_inv_cancel₀ (z_ne_zero x)]
  ring

/-- The positive-exponent version of the phase identity defining `Θ`. -/
theorem exp_I_theta_eq_scattering {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    Complex.exp (I * (theta Δ x y : ℂ)) =
      z y * scattering Δ y x / (z x * scattering Δ x y) := by
  have h := exp_neg_I_theta hΔ y x
  rw [theta_swap, Complex.ofReal_neg, mul_neg, neg_neg] at h
  rw [h, thetaRhs, mul_sub, Complex.exp_sub]
  change z y / z x * ((scattering Δ y x) /
    (z y + Complex.exp (-(I * (x : ℂ))) - 2 * (Δ : ℂ))) = _
  rw [show z y + Complex.exp (-(I * (x : ℂ))) - 2 * (Δ : ℂ) =
    scattering Δ x y by unfold scattering; ring]
  field_simp

/-- Cancellation of the two simple poles. -/
theorem L_add_M (c : ℝ) {w : ℂ} (hw : w ≠ 1) :
    L c w + M c w = 2 - (c : ℂ) ^ 2 := by
  have hd : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  unfold L M
  field_simp
  ring

theorem M_mul_L_sub_one (c : ℝ) {u v : ℂ} (hu : u ≠ 1) (hv : v ≠ 1) :
    M c u * L c v - 1 =
      -(c : ℂ) ^ 2 * (1 + u * v - 2 * (anisotropy c : ℂ) * v) /
        ((1 - u) * (1 - v)) := by
  have hu' : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  have hv' : 1 - v ≠ 0 := sub_ne_zero.mpr hv.symm
  unfold M L anisotropy
  push_cast
  field_simp
  ring

theorem M_mul_L_sub_one_eq_scattering (c : ℝ) {x y : ℝ}
    (hx : z x ≠ 1) (hy : z y ≠ 1) :
    M c (z x) * L c (z y) - 1 =
      -(c : ℂ) ^ 2 * (z y * scattering (anisotropy c) y x) /
        ((1 - z x) * (1 - z y)) := by
  rw [M_mul_L_sub_one c hx hy, z_mul_scattering]
  ring

theorem M_mul_L_sub_one_ne_zero {c x y : ℝ} (hc : 2 < c)
    (hx : z x ≠ 1) (hy : z y ≠ 1) :
    M c (z x) * L c (z y) - 1 ≠ 0 := by
  rw [M_mul_L_sub_one_eq_scattering c hx hy]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (lt_trans (by norm_num) hc).ne'
  exact div_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hc0))
      (mul_ne_zero (z_ne_zero y) (scattering_ne_zero (anisotropy_lt_neg_one hc) y x)))
    (mul_ne_zero (sub_ne_zero.mpr hx.symm) (sub_ne_zero.mpr hy.symm))

/-- Equation (6) of the companion paper; the roots need not satisfy the Bethe equations. -/
theorem exp_I_theta_eq_M_L_ratio {c x y : ℝ} (hc : 2 < c)
    (hx : z x ≠ 1) (hy : z y ≠ 1) :
    Complex.exp (I * (theta (anisotropy c) x y : ℂ)) =
      (M c (z x) * L c (z y) - 1) / (M c (z y) * L c (z x) - 1) := by
  rw [exp_I_theta_eq_scattering (anisotropy_lt_neg_one hc),
    M_mul_L_sub_one_eq_scattering c hx hy, M_mul_L_sub_one_eq_scattering c hy hx]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (lt_trans (by norm_num) hc).ne'
  have hx0 := z_ne_zero x
  have hs := scattering_ne_zero (anisotropy_lt_neg_one hc) x y
  have hx1 : 1 - z x ≠ 0 := sub_ne_zero.mpr hx.symm
  have hy1 : 1 - z y ≠ 0 := sub_ne_zero.mpr hy.symm
  field_simp

theorem L_eq_scattering_zero (c : ℝ) {y : ℝ} (hy : z y ≠ 1) :
    L c (z y) = z y * scattering (anisotropy c) y 0 / (1 - z y) := by
  rw [z_mul_scattering, z_zero]
  have hy1 : 1 - z y ≠ 0 := sub_ne_zero.mpr hy.symm
  unfold L anisotropy
  push_cast
  field_simp
  ring

theorem M_eq_neg_scattering_zero (c : ℝ) {y : ℝ} (hy : z y ≠ 1) :
    M c (z y) = -scattering (anisotropy c) 0 y / (1 - z y) := by
  rw [scattering_eq_inv_z, z_zero, inv_one]
  have hy1 : 1 - z y ≠ 0 := sub_ne_zero.mpr hy.symm
  unfold M anisotropy
  push_cast
  field_simp
  ring

theorem L_ne_zero {c y : ℝ} (hc : 2 < c) (hy : z y ≠ 1) : L c (z y) ≠ 0 := by
  rw [L_eq_scattering_zero c hy]
  exact div_ne_zero
    (mul_ne_zero (z_ne_zero y) (scattering_ne_zero (anisotropy_lt_neg_one hc) y 0))
    (sub_ne_zero.mpr hy.symm)

theorem M_ne_zero {c y : ℝ} (hc : 2 < c) (hy : z y ≠ 1) : M c (z y) ≠ 0 := by
  rw [M_eq_neg_scattering_zero c hy]
  exact div_ne_zero (neg_ne_zero.mpr (scattering_ne_zero (anisotropy_lt_neg_one hc) 0 y))
    (sub_ne_zero.mpr hy.symm)

/-- Equation (19), the scattering identity when the first root is zero. -/
theorem exp_I_theta_zero_eq_neg_L_div_M {c y : ℝ} (hc : 2 < c) (hy : z y ≠ 1) :
    Complex.exp (I * (theta (anisotropy c) 0 y : ℂ)) = -L c (z y) / M c (z y) := by
  rw [exp_I_theta_eq_scattering (anisotropy_lt_neg_one hc), z_zero, one_mul,
    L_eq_scattering_zero c hy, M_eq_neg_scattering_zero c hy]
  have hy1 : 1 - z y ≠ 0 := sub_ne_zero.mpr hy.symm
  have hs := scattering_ne_zero (anisotropy_lt_neg_one hc) 0 y
  field_simp

theorem exp_I_theta_zero_eq_neg_L_div_M_of_mem {c y : ℝ} (hc : 2 < c)
    (hy : y ∈ Set.Ioo (-Real.pi) Real.pi) (hy0 : y ≠ 0) :
    Complex.exp (I * (theta (anisotropy c) 0 y : ℂ)) = -L c (z y) / M c (z y) :=
  exp_I_theta_zero_eq_neg_L_div_M hc (z_ne_one hy hy0)

end PottsDiscontinuity.BetheAnsatz
