module

public import Mathlib
public import PottsDiscontinuity.SixVertex.InfinityMomentum
public import PottsDiscontinuity.SixVertex.InfinitySlater

/-! # Exact phase of the centered Slater determinant -/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

/-- The projective Vandermonde formula cancels the position-dependent phase exactly. -/
theorem slater_centered_eq_pair_product {k : ℕ} {q : ℂ} (hq : q ≠ 0)
    (x : Fin k → ℤ) :
    slater (centeredMomenta k q) x =
      ∏ a : Fin k, ∏ b ∈ Ioi a, (q ^ (x b - x a) - q ^ (x a - x b)) := by
  have he : planeWaveMatrix (centeredMomenta k q) x =
      Matrix.projVandermonde (fun a => q ^ x a) (fun a => (q ^ x a)⁻¹) := by
    ext b a
    have hr : (a.rev.val : ℤ) = (k : ℤ) - 1 - a.val := by
      have hh : a.rev.val = k - 1 - a.val := by simp only [Fin.val_rev]; omega
      have ha := a.isLt
      omega
    simp only [planeWaveMatrix, centeredMomenta, Matrix.projVandermonde_apply]
    rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_neg_one,
      ← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_mul,
      ← _root_.zpow_mul, ← zpow_add₀ hq, hr]
    congr 1
    ring
  rw [slater, he, Matrix.det_projVandermonde]
  apply prod_congr rfl
  intro a _
  apply prod_congr rfl
  intro b _
  rw [zpow_sub₀ hq, zpow_sub₀ hq]
  rfl

/-- The unit complex wave with real phase. -/
noncomputable def unitWave (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

theorem unitWave_ne_zero (t : ℝ) : unitWave t ≠ 0 := Complex.exp_ne_zero _

theorem unitWave_zpow (t : ℝ) (a : ℤ) : unitWave t ^ a = unitWave (t * a) := by
  rw [unitWave, ← Complex.exp_int_mul]
  unfold unitWave
  congr 1
  push_cast
  ring

theorem unitWave_sub_neg (t : ℝ) :
    unitWave t - unitWave (-t) = 2 * Complex.I * (Real.sin t : ℂ) := by
  unfold unitWave
  rw [show ((-t : ℝ) : ℂ) * Complex.I = -((t : ℂ) * Complex.I) by push_cast; ring]
  rw [Complex.exp_mul_I]
  rw [show -((t : ℂ) * Complex.I) = (- (t : ℂ)) * Complex.I by ring,
    Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_sin]
  ring

theorem unitWave_neg (t : ℝ) : unitWave (-t) = (unitWave t)⁻¹ := by
  unfold unitWave
  rw [show ((-t : ℝ) : ℂ) * Complex.I = -((t : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_neg]

theorem unitWave_add_neg (t : ℝ) :
    unitWave t + unitWave (-t) = 2 * (Real.cos t : ℂ) := by
  unfold unitWave
  rw [show ((-t : ℝ) : ℂ) * Complex.I = (-(t : ℂ)) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  ring

/-- The sine Vandermonde on arbitrary integer lifts. -/
noncomputable def sineLiftWeight {k : ℕ} (L : ℝ) (x : Fin k → ℤ) : ℝ :=
  ∏ a : Fin k, ∏ b ∈ Ioi a,
    Real.sin (Real.pi * ((x b : ℝ) - x a) / L)

/-- The fixed, position-independent phase multiplier. -/
noncomputable def slaterPhase (k : ℕ) : ℂ :=
  ∏ a : Fin k, ∏ _b ∈ Ioi a, (2 * Complex.I)

theorem slaterPhase_ne_zero (k : ℕ) : slaterPhase k ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro a _
  apply prod_ne_zero_iff.mpr
  intro b _
  exact mul_ne_zero (by norm_num) Complex.I_ne_zero

/-- Exact equality with the real sine product; there is no residual position phase. -/
theorem slater_centered_unitWave {k : ℕ} (L : ℝ) (x : Fin k → ℤ) :
    slater (centeredMomenta k (unitWave (Real.pi / L))) x =
      slaterPhase k * (sineLiftWeight L x : ℂ) := by
  rw [slater_centered_eq_pair_product (unitWave_ne_zero _)]
  have he : ∀ a b : Fin k,
      unitWave (Real.pi / L) ^ (x b - x a) -
        unitWave (Real.pi / L) ^ (x a - x b) =
      (2 * Complex.I) * (Real.sin (Real.pi * ((x b : ℝ) - x a) / L) : ℂ) := by
    intro a b
    rw [unitWave_zpow, unitWave_zpow]
    have h1 : Real.pi / L * ((x b - x a : ℤ) : ℝ) =
        Real.pi * ((x b : ℝ) - x a) / L := by push_cast; ring
    have h2 : Real.pi / L * ((x a - x b : ℤ) : ℝ) =
        -(Real.pi * ((x b : ℝ) - x a) / L) := by push_cast; ring
    rw [h1, h2, unitWave_sub_neg]
  simp_rw [he]
  simp only [prod_mul_distrib, slaterPhase, sineLiftWeight, Complex.ofReal_prod]

/-- The complex product of the centered one-particle factors is the real cosine product. -/
theorem centeredMomenta_unitWave_product (r : ℕ) (L : ℝ) :
    (∏ a : Fin (2 * r), (centeredMomenta (2 * r) (unitWave (Real.pi / L)) a +
      (centeredMomenta (2 * r) (unitWave (Real.pi / L)) a)⁻¹)) =
      (centeredCosineProduct r L : ℂ) := by
  have he : ∀ a : Fin (2 * r), centeredMomenta (2 * r) (unitWave (Real.pi / L)) a =
      unitWave (Real.pi * (2 * (a.val : ℝ) + 1 - 2 * r) / L) := by
    intro a
    rw [centeredMomenta, unitWave_zpow]
    congr 1
    push_cast
    ring
  simp_rw [he, ← unitWave_neg, unitWave_add_neg]
  simp only [centeredCosineProduct, Complex.ofReal_prod, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  exact Fin.prod_univ_eq_prod_range
    (fun a => (2 : ℂ) * (Real.cos (Real.pi * (2 * (a : ℝ) + 1 - 2 * r) / L) : ℂ)) (2 * r)

/-- The real sine product satisfies the exact lifted simultaneous-walk eigenvalue identity. -/
theorem sum_sineLiftWeight_stepLift (r : ℕ) (L : ℝ) (x : Fin (2 * r) → ℤ) :
    (∑ d : Fin (2 * r) → Bool, sineLiftWeight L (stepLift x d)) =
      centeredCosineProduct r L * sineLiftWeight L x := by
  have hz : ∀ a : Fin (2 * r), centeredMomenta (2 * r) (unitWave (Real.pi / L)) a ≠ 0 :=
    fun a => zpow_ne_zero _ (unitWave_ne_zero _)
  have hs := sum_slater_stepLift (centeredMomenta (2 * r) (unitWave (Real.pi / L))) hz x
  simp_rw [slater_centered_unitWave] at hs
  rw [centeredMomenta_unitWave_product] at hs
  have hh : slaterPhase (2 * r) *
      ((∑ d : Fin (2 * r) → Bool, sineLiftWeight L (stepLift x d) : ℝ) : ℂ) =
      slaterPhase (2 * r) * ((centeredCosineProduct r L * sineLiftWeight L x : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, mul_sum, hs, Complex.ofReal_mul]
    ring
  exact Complex.ofReal_injective (mul_left_cancel₀ (slaterPhase_ne_zero _) hh)

end PottsDiscontinuity.SixVertex
