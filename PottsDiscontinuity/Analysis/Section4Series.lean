module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.Bethe.Prop21Coeff
public import PottsDiscontinuity.Bethe.RatioProducts

/-!
# Section 4 logarithmic series and identity (4.3)

This module proves the ordered partial-sum expansion of `log (cosh λ)` and then derives
equation (4.3) using the previously proved `identity44`.  The expansion is handled as an ordered
series throughout; no absolute convergence is claimed for its limiting series.
-/

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

/-- The real logarithmic profile in (4.2), with its value at the single singular point
chosen as an `L¹` representative.  Every theorem identifying it with the source profile is
stated away from `α = 0`; its value there does not encode a finite value for the logarithmic
singularity. -/
noncomputable def fourierP (lam α : ℝ) : ℝ :=
  if α = 0 then 0 else
    (1 / 2 : ℝ) * Real.log
      ((Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α))

/-- The Möbius expression for `e^{ik(α)}` in unit-circle coordinates. -/
private theorem exp_I_mul_kMap_fraction {lam α : ℝ} (hlam : 0 < lam) :
    Complex.exp (I * (Bethe.kMap lam α : ℂ)) =
      (Complex.exp (I * (α : ℂ)) * (Real.exp lam : ℂ) - 1) /
        ((Real.exp lam : ℂ) - Complex.exp (I * (α : ℂ))) := by
  rw [Bethe.exp_I_mul_kMap_aux hlam α]
  have hw : Complex.exp (I * (α : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hbar : Complex.exp (-(I * (α : ℂ))) =
      (Complex.exp (I * (α : ℂ)))⁻¹ := by
    exact Complex.exp_neg _
  rw [hbar]
  field_simp [hw]

/-- With `c² = 2 - 2Δ = 2 + 2 cosh λ`, the Bethe factor satisfies the source modulus formula.
This is the explicit algebraic step omitted in the source's phrase “some elementary algebraic
manipulations.” -/
theorem normSq_M_kMap_eq_ratio {lam c α : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hcos : Real.cos α < 1) :
    Complex.normSq (BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))) =
      (Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α) := by
  let E : ℂ := (Real.exp lam : ℂ)
  let w : ℂ := Complex.exp (I * (α : ℂ))
  have hEreal : 1 < Real.exp lam := by simpa using hlam
  have hwNorm : ‖w‖ = 1 := by simp [w]
  have hwNe : w ≠ 0 := Complex.exp_ne_zero _
  have hEw : E - w ≠ 0 := by
    apply Bethe.ofReal_sub_ne_zero hEreal
    simpa [E] using hwNorm
  have h1w : 1 - w ≠ 0 := by
    intro h
    have hw1 : w = 1 := by linear_combination -h
    have hre := congrArg Complex.re hw1
    have : Real.cos α = 1 := by
      change (Complex.exp (I * (α : ℂ))).re = 1 at hre
      rw [Bethe.exp_I_mul_ofReal] at hre
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
      linarith
    linarith
  have hEpos : Real.exp lam ≠ 0 := (Real.exp_pos lam).ne'
  have hcsq : (c : ℂ) ^ 2 = (E + 1) ^ 2 / E := by
    have hreal : c ^ 2 = (Real.exp lam + 1) ^ 2 / Real.exp lam := by
      rw [hc, Real.cosh_eq]
      rw [Real.exp_neg]
      field_simp [hEpos]
      ring
    have hrealC := congrArg (fun x : ℝ => (x : ℂ)) hreal
    simpa [E] using hrealC
  have hz : Complex.exp (I * (Bethe.kMap lam α : ℂ)) = (w * E - 1) / (E - w) := by
    simpa [w, E, mul_comm, mul_left_comm, mul_assoc] using
      exp_I_mul_kMap_fraction hlam
  have hden : 1 - Complex.exp (I * (Bethe.kMap lam α : ℂ)) =
      (E + 1) * (1 - w) / (E - w) := by
    rw [hz]
    field_simp [hEw]
    ring
  have hM : BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ))) =
      (w - E ^ 2) / (E * (1 - w)) := by
    rw [BetheAnsatz.M, hden, hcsq]
    have hEc : E ≠ 0 := by
      change (Real.exp lam : ℂ) ≠ 0
      exact_mod_cast hEpos
    field_simp [hEw, h1w, hEc]
    ring
  rw [hM]
  have hwSq : Complex.normSq w = 1 := by
    rw [Complex.normSq_eq_norm_sq, hwNorm]
    norm_num
  have hESq : Complex.normSq E = Real.exp lam ^ 2 := by
    change Complex.normSq (Real.exp lam : ℂ) = _
    rw [Complex.normSq_ofReal]
    ring
  have hE2Sq : Complex.normSq (E ^ 2) = Real.exp lam ^ 4 := by
    rw [show E ^ 2 = E * E by rw [pow_two], Complex.normSq_mul, hESq]
    ring
  have hwform : w = (Real.cos α : ℂ) + (Real.sin α : ℂ) * I := by
    simpa [w] using Bethe.exp_I_mul_ofReal α
  have hwRe : w.re = Real.cos α := by
    rw [hwform]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hwIm : w.im = Real.sin α := by
    rw [hwform]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, zero_mul, mul_one, add_zero]
    simp
  have hE2re : (E ^ 2).re = Real.exp lam ^ 2 := by
    change (((Real.exp lam : ℂ) ^ 2).re) = _
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hE2im : (E ^ 2).im = 0 := by
    change (((Real.exp lam : ℂ) ^ 2).im) = _
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  have hnum : Complex.normSq (w - E ^ 2) =
      Real.exp lam ^ 4 - 2 * Real.exp lam ^ 2 * Real.cos α + 1 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hwRe, hwIm, hE2re, hE2im]
    nlinarith [Real.sin_sq_add_cos_sq α]
  have h1wSq : Complex.normSq (1 - w) = 2 - 2 * Real.cos α := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hwRe, hwIm]
    simp
    nlinarith [Real.sin_sq_add_cos_sq α]
  have hdenSq : Complex.normSq (E * (1 - w)) =
      Real.exp lam ^ 2 * (2 - 2 * Real.cos α) := by
    rw [Complex.normSq_mul, hESq, h1wSq]
  rw [Complex.normSq_div, hnum, hdenSq]
  have hdiv : Real.exp lam ^ 2 * (2 - 2 * Real.cos α) ≠ 0 := by
    apply mul_ne_zero
    · positivity
    · linarith
  have hcosh : Real.cosh (2 * lam) =
      (Real.exp lam ^ 2 + (Real.exp lam ^ 2)⁻¹) / 2 := by
    rw [Real.cosh_eq]
    have hplus : Real.exp (2 * lam) = Real.exp lam ^ 2 := by
      rw [show 2 * lam = lam + lam by ring, Real.exp_add]
      ring
    have hminus : Real.exp (-(2 * lam)) = (Real.exp lam ^ 2)⁻¹ := by
      rw [Real.exp_neg, hplus]
    rw [hplus, hminus]
  rw [hcosh]
  field_simp [hdiv, hEpos]
  ring

/-- On the punctured circle, the real profile is exactly the logarithm of the modulus of the
Bethe factor `M(e^{ik(α)})`. -/
theorem fourierP_eq_log_norm {lam c α : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hcos : Real.cos α < 1) :
    fourierP lam α = Real.log
      ‖BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))‖ := by
  let z : ℂ := BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))
  have hα : α ≠ 0 := by
    intro h
    subst α
    rw [Real.cos_zero] at hcos
    norm_num at hcos
  have htop : 0 < Real.cosh (2 * lam) - Real.cos α := by
    have h := Real.one_le_cosh (2 * lam)
    linarith
  have hbottom : 0 < 1 - Real.cos α := by linarith
  have hratio : 0 <
      (Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α) :=
    div_pos htop hbottom
  have hnormSq : ‖z‖ ^ 2 =
      (Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normSq_M_kMap_eq_ratio hlam hc hcos
  have hnorm : 0 < ‖z‖ := by
    have hnonneg := norm_nonneg z
    nlinarith
  unfold fourierP
  rw [ite_eq_right hα]
  change (1 / 2 : ℝ) * Real.log
      ((Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α)) = Real.log ‖z‖
  rw [← hnormSq, Real.log_pow]
  ring

/-- Jordan's sine inequality gives a quadratic lower bound for the denominator of `P` on the
fundamental interval. -/
private theorem fourier_one_sub_cos_lower {α : ℝ} (hα : α ∈ Icc (-π) π) :
    2 * α ^ 2 / π ^ 2 ≤ 1 - Real.cos α := by
  have hx : |α / 2| ≤ π / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have habs : |α| ≤ π := abs_le.mpr ⟨by linarith [hα.1], hα.2⟩
    linarith
  have hj := Real.mul_abs_le_abs_sin hx
  have hjSq : ((2 / π) * |α / 2|) ^ 2 ≤ |Real.sin (α / 2)| ^ 2 :=
    (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 hj
  have habshalf : |α / 2| = |α| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [habshalf] at hjSq
  have hsimpl : (2 / π * (|α| / 2)) ^ 2 = α ^ 2 / π ^ 2 := by
    field_simp [Real.pi_ne_zero]
    rw [sq_abs]
  rw [hsimpl, sq_abs] at hjSq
  have hsin := Real.sin_sq_eq_half_sub (α / 2)
  rw [show 2 * (α / 2) = α by ring] at hsin
  calc
    2 * α ^ 2 / π ^ 2 = 2 * (α ^ 2 / π ^ 2) := by ring
    _ ≤ 2 * Real.sin (α / 2) ^ 2 := mul_le_mul_of_nonneg_left hjSq (by norm_num)
    _ = 1 - Real.cos α := by rw [hsin]; ring

/-- The punctured derivative of the logarithmic profile, assigned an irrelevant finite value at
the singular point so that it can be used as an interval-integral representative. -/
noncomputable def fourierPPrime (lam α : ℝ) : ℝ :=
  if α = 0 then 0 else
    (1 / 2 : ℝ) *
      (Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
        Real.sin α / (1 - Real.cos α))

/-- Away from zero, `fourierPPrime` is the classical derivative of `P`. -/
theorem fourierP_hasDerivAt {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Ioo (-π) π) (hα0 : α ≠ 0) :
    HasDerivAt (fourierP lam) (fourierPPrime lam α) α := by
  have hαcc : α ∈ Icc (-π) π := Ioo_subset_Icc_self hα
  have hcosLower := fourier_one_sub_cos_lower hαcc
  have hden : 0 < 1 - Real.cos α := by
    have hαsq : 0 < α ^ 2 := sq_pos_of_ne_zero hα0
    have hbound : 0 < 2 * α ^ 2 / π ^ 2 := by positivity
    exact lt_of_lt_of_le hbound hcosLower
  have hcosh : 1 < Real.cosh (2 * lam) :=
    Real.one_lt_cosh.mpr (by positivity)
  have hnum : 0 < Real.cosh (2 * lam) - Real.cos α := by
    linarith [Real.cos_le_one α]
  let u : ℝ → ℝ := fun x => Real.cosh (2 * lam) - Real.cos x
  let v : ℝ → ℝ := fun x => 1 - Real.cos x
  have hu : HasDerivAt u (Real.sin α) α := by
    dsimp [u]
    simpa using (Real.hasDerivAt_cos α).const_sub (Real.cosh (2 * lam))
  have hv : HasDerivAt v (Real.sin α) α := by
    dsimp [v]
    simpa using (Real.hasDerivAt_cos α).const_sub (1 : ℝ)
  have hratio : 0 < u α / v α := div_pos hnum hden
  have hraw := (hu.div hv hden.ne').log (div_ne_zero hnum.ne' hden.ne')
  have hraw' := hraw.const_mul (1 / 2 : ℝ)
  have hderiv :
      (1 / 2 : ℝ) *
          (((Real.sin α * v α - u α * Real.sin α) / v α ^ 2) / ((u / v) α)) =
        fourierPPrime lam α := by
    simp [fourierPPrime, hα0, u, v]
    field_simp [hden.ne', hnum.ne']
  have hraw'' : HasDerivAt (fun x => (1 / 2 : ℝ) * Real.log (u x / v x))
      (fourierPPrime lam α) α := hraw'.congr_deriv hderiv
  apply hraw''.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hα0] with x hx
  simp [fourierP, u, v, hx]

/-- The product `sin α · sin((n+1)α)/(1-cos α)`, with its removable singularity assigned
the value zero at the origin. -/
noncomputable def fourierCotSin (n : ℕ) (α : ℝ) : ℝ :=
  if α = 0 then 0 else
    Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) / (1 - Real.cos α)

private theorem fourier_sin_recurrence (n : ℕ) (α : ℝ) :
    Real.sin α *
        (Real.sin (((n + 2 : ℕ) : ℝ) * α) -
          Real.sin (((n + 1 : ℕ) : ℝ) * α)) =
      (1 - Real.cos α) *
        (Real.cos (((n + 2 : ℕ) : ℝ) * α) +
          Real.cos (((n + 1 : ℕ) : ℝ) * α)) := by
  have hcast : (((n + 2 : ℕ) : ℝ) * α) = (((n + 1 : ℕ) : ℝ) * α) + α := by
    push_cast
    ring
  rw [hcast, Real.sin_add, Real.cos_add]
  have hsq := Real.sin_sq_add_cos_sq α
  have hsqMul := congrArg
    (fun y : ℝ => Real.cos (((n + 1 : ℕ) : ℝ) * α) * y) hsq
  nlinarith [hsq, hsqMul]

private theorem fourierCotSin_succ_ae (n : ℕ) :
    (fun α => fourierCotSin (n + 1) α) =ᵐ[volume.restrict (uIoc (-π) π)]
      (fun α => fourierCotSin n α +
        Real.cos (((n + 2 : ℕ) : ℝ) * α) +
        Real.cos (((n + 1 : ℕ) : ℝ) * α)) := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hα0
  have hαio : α ∈ Ioc (-π) π := by
    simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
  have hαcc : α ∈ Icc (-π) π := Ioc_subset_Icc_self hαio
  have hdenLower := fourier_one_sub_cos_lower hαcc
  have hαsq : 0 < α ^ 2 := sq_pos_of_ne_zero hα0
  have hden : 0 < 1 - Real.cos α := by
    have hpos : 0 < 2 * α ^ 2 / π ^ 2 := by positivity
    exact lt_of_lt_of_le hpos hdenLower
  have hrec := fourier_sin_recurrence n α
  simp [fourierCotSin, hα0]
  push_cast at hrec ⊢
  have hfreqA : (↑n + 1 + 1) * α = (↑n + 2) * α := by ring
  have hfreqB : α * (↑n + 1) = (↑n + 1) * α := by ring
  rw [hfreqA]
  rw [← hfreqB] at hrec
  field_simp [hden.ne']
  nlinarith [hrec]

private theorem fourierCotSin_integrable_integral (n : ℕ) :
    IntervalIntegrable (fun α => fourierCotSin n α) volume (-π) π ∧
      ∫ α in (-π)..π, fourierCotSin n α = 2 * π := by
  induction n with
  | zero =>
      have hEq : (fun α => fourierCotSin 0 α) =ᵐ[volume.restrict (uIoc (-π) π)]
          (fun α => 1 + Real.cos α) := by
        filter_upwards [ae_restrict_mem measurableSet_uIoc,
          ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hα0
        have hαio : α ∈ Ioc (-π) π := by
          simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
        have hαcc : α ∈ Icc (-π) π := Ioc_subset_Icc_self hαio
        have hdenLower := fourier_one_sub_cos_lower hαcc
        have hαsq : 0 < α ^ 2 := sq_pos_of_ne_zero hα0
        have hpos : 0 < 2 * α ^ 2 / π ^ 2 := by positivity
        have hden : 0 < 1 - Real.cos α := lt_of_lt_of_le hpos hdenLower
        simp [fourierCotSin, hα0]
        field_simp [hden.ne']
        nlinarith [Real.sin_sq_add_cos_sq α]
      have hcosCont : Continuous (fun α : ℝ => 1 + Real.cos α) := by fun_prop
      have hcosInt : IntervalIntegrable (fun α : ℝ => 1 + Real.cos α) volume (-π) π :=
        hcosCont.intervalIntegrable _ _
      refine ⟨(intervalIntegrable_congr_ae hEq).mpr hcosInt, ?_⟩
      calc
        ∫ α in (-π)..π, fourierCotSin 0 α =
            ∫ α in (-π)..π, 1 + Real.cos α :=
              intervalIntegral.integral_congr_ae_restrict hEq
        _ = 2 * π := by
          rw [intervalIntegral.integral_add intervalIntegrable_const
            (Real.continuous_cos.intervalIntegrable _ _)]
          have hcoszero : ∫ α in (-π)..π, Real.cos α = 0 := by
            simp
          rw [intervalIntegral.integral_const, hcoszero]
          ring
  | succ n ih =>
      have hEq := fourierCotSin_succ_ae n
      have hcos1 : Continuous (fun α : ℝ => Real.cos (((n + 2 : ℕ) : ℝ) * α)) := by
        fun_prop
      have hcos2 : Continuous (fun α : ℝ => Real.cos (((n + 1 : ℕ) : ℝ) * α)) := by
        fun_prop
      have hcosInt1 : IntervalIntegrable
          (fun α : ℝ => Real.cos (((n + 2 : ℕ) : ℝ) * α)) volume (-π) π :=
        hcos1.intervalIntegrable _ _
      have hcosInt2 : IntervalIntegrable
          (fun α : ℝ => Real.cos (((n + 1 : ℕ) : ℝ) * α)) volume (-π) π :=
        hcos2.intervalIntegrable _ _
      have hrhsInt : IntervalIntegrable
          (fun α => fourierCotSin n α +
            Real.cos (((n + 2 : ℕ) : ℝ) * α) +
            Real.cos (((n + 1 : ℕ) : ℝ) * α)) volume (-π) π :=
        (ih.1.add hcosInt1).add hcosInt2
      have hnextInt := hrhsInt.congr_ae hEq.symm
      refine ⟨hnextInt, ?_⟩
      calc
        ∫ α in (-π)..π, fourierCotSin (n + 1) α =
            ∫ α in (-π)..π,
              fourierCotSin n α + Real.cos (((n + 2 : ℕ) : ℝ) * α) +
                Real.cos (((n + 1 : ℕ) : ℝ) * α) :=
                  intervalIntegral.integral_congr_ae_restrict hEq
        _ = (∫ α in (-π)..π, fourierCotSin n α) +
              (∫ α in (-π)..π, Real.cos (((n + 2 : ℕ) : ℝ) * α)) +
              (∫ α in (-π)..π, Real.cos (((n + 1 : ℕ) : ℝ) * α)) := by
          rw [intervalIntegral.integral_add (ih.1.add hcosInt1) hcosInt2,
            intervalIntegral.integral_add ih.1 hcosInt1]
        _ = 2 * π := by
          rw [ih.2, Bethe.integral_cos_nat_mul (by omega),
            Bethe.integral_cos_nat_mul (by omega)]
          ring

private theorem fourierXi_cosCoeff {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    Bethe.cosCoeff (Bethe.Xi μ) n = 2 * π * Real.exp (-μ) ^ n := by
  have ha := Bethe.summable_two_mul_exp_pow hμ
  have hb : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  cases n with
  | zero =>
      rw [Bethe.Xi_eq_trigSeries hμ, Bethe.cosCoeff_trigSeries_zero ha hb 1]
      simp
  | succ n =>
      rw [Bethe.Xi_eq_trigSeries hμ,
        Bethe.cosCoeff_trigSeries_succ ha hb 1 n]
      ring

private theorem fourier_sin_product_cos_identity (n : ℕ) (α : ℝ) :
    Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) =
      (Real.cos ((n : ℝ) * α) - Real.cos (((n + 2 : ℕ) : ℝ) * α)) / 2 := by
  have hminus : (((n + 1 : ℕ) : ℝ) * α) - α = (n : ℝ) * α := by
    push_cast
    ring
  have hplus : (((n + 1 : ℕ) : ℝ) * α) + α = ((n + 2 : ℕ) : ℝ) * α := by
    push_cast
    ring
  rw [← hminus, ← hplus]
  have hcosMinus := Real.cos_sub (((n + 1 : ℕ) : ℝ) * α) α
  have hcosPlus := Real.cos_add (((n + 1 : ℕ) : ℝ) * α) α
  nlinarith [hcosMinus, hcosPlus]

private theorem fourier_sin_kernel_integral {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    ∫ α in (-π)..π,
      Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
        (Real.cosh μ - Real.cos α) =
      2 * π * Real.exp (-μ) ^ (n + 1) := by
  let r : ℝ := Real.exp (-μ)
  have hr : 0 < r := Real.exp_pos _
  have hcosCoeff0 := fourierXi_cosCoeff hμ n
  have hcosCoeff2 := fourierXi_cosCoeff hμ (n + 2)
  have hcos0 :
      ∫ α in (-π)..π, Bethe.Xi μ α * Real.cos ((n : ℝ) * α) =
        2 * π * r ^ n := by
    simpa [Bethe.cosCoeff, r] using hcosCoeff0
  have hcos2 :
      ∫ α in (-π)..π,
        Bethe.Xi μ α * Real.cos (((n + 2 : ℕ) : ℝ) * α) =
          2 * π * r ^ (n + 2) := by
    simpa [Bethe.cosCoeff, r] using hcosCoeff2
  have hprod : (fun α : ℝ => Bethe.Xi μ α * Real.sin α *
      Real.sin (((n + 1 : ℕ) : ℝ) * α)) =
      (fun α => (1 / 2 : ℝ) *
          (Bethe.Xi μ α * Real.cos ((n : ℝ) * α)) -
        (1 / 2 : ℝ) *
          (Bethe.Xi μ α * Real.cos (((n + 2 : ℕ) : ℝ) * α))) := by
    funext α
    rw [mul_assoc]
    rw [fourier_sin_product_cos_identity]
    ring
  have hXiCont : Continuous (Bethe.Xi μ) := Bethe.continuous_Xi hμ
  have hcosCont0 : Continuous (fun α : ℝ => Real.cos ((n : ℝ) * α)) := by fun_prop
  have hcosCont2 : Continuous
      (fun α : ℝ => Real.cos (((n + 2 : ℕ) : ℝ) * α)) := by fun_prop
  have hXiCosInt0 : IntervalIntegrable
      (fun α : ℝ => Bethe.Xi μ α * Real.cos ((n : ℝ) * α)) volume (-π) π :=
    (hXiCont.mul hcosCont0).intervalIntegrable _ _
  have hXiCosInt2 : IntervalIntegrable
      (fun α : ℝ => Bethe.Xi μ α * Real.cos (((n + 2 : ℕ) : ℝ) * α)) volume (-π) π :=
    (hXiCont.mul hcosCont2).intervalIntegrable _ _
  have hscaledInt0 : IntervalIntegrable
      (fun α : ℝ => (1 / 2 : ℝ) *
        (Bethe.Xi μ α * Real.cos ((n : ℝ) * α))) volume (-π) π := by
    simpa [mul_comm] using hXiCosInt0.const_mul (1 / 2 : ℝ)
  have hscaledInt2 : IntervalIntegrable
      (fun α : ℝ => (1 / 2 : ℝ) *
        (Bethe.Xi μ α * Real.cos (((n + 2 : ℕ) : ℝ) * α))) volume (-π) π := by
    simpa [mul_comm] using hXiCosInt2.const_mul (1 / 2 : ℝ)
  have hprodInt :
      ∫ α in (-π)..π, Bethe.Xi μ α * Real.sin α *
          Real.sin (((n + 1 : ℕ) : ℝ) * α) =
        π * (r ^ n - r ^ (n + 2)) := by
    calc
      ∫ α in (-π)..π, Bethe.Xi μ α * Real.sin α *
          Real.sin (((n + 1 : ℕ) : ℝ) * α) =
          ∫ α in (-π)..π, (1 / 2 : ℝ) *
            (Bethe.Xi μ α * Real.cos ((n : ℝ) * α)) -
              (1 / 2 : ℝ) *
                (Bethe.Xi μ α * Real.cos (((n + 2 : ℕ) : ℝ) * α)) := by rw [hprod]
      _ = (∫ α in (-π)..π, (1 / 2 : ℝ) *
              (Bethe.Xi μ α * Real.cos ((n : ℝ) * α))) -
            ∫ α in (-π)..π, (1 / 2 : ℝ) *
              (Bethe.Xi μ α * Real.cos (((n + 2 : ℕ) : ℝ) * α)) :=
          intervalIntegral.integral_sub hscaledInt0 hscaledInt2
      _ = (1 / 2 : ℝ) * (2 * π * r ^ n) - (1 / 2 : ℝ) * (2 * π * r ^ (n + 2)) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
            hcos0, hcos2]
      _ = π * (r ^ n - r ^ (n + 2)) := by ring
  have hsinh : 1 - r ^ 2 = 2 * r * Real.sinh μ := by
    dsimp [r]
    rw [Real.sinh_eq, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  have hpowdiff : r ^ n - r ^ (n + 2) = r ^ n * (1 - r ^ 2) := by
    rw [pow_add]
    ring
  have hdenPos (α : ℝ) : 0 < Real.cosh μ - Real.cos α := by
    have hcosh : 1 < Real.cosh μ := Real.one_lt_cosh.mpr hμ.ne'
    linarith [Real.cos_le_one α]
  have hkernel : ∀ α : ℝ,
      Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
        (Real.cosh μ - Real.cos α) =
      (Real.sinh μ)⁻¹ *
        (Bethe.Xi μ α * Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α)) := by
    intro α
    rw [Bethe.Xi]
    have hsinhPos : 0 < Real.sinh μ := Real.sinh_pos_iff.mpr hμ
    field_simp [hsinhPos.ne', (hdenPos α).ne']
  have hfun :
      (fun α : ℝ => Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
        (Real.cosh μ - Real.cos α)) =
      (fun α => (Real.sinh μ)⁻¹ *
        (Bethe.Xi μ α * Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α))) := by
    funext α
    exact hkernel α
  rw [hfun, intervalIntegral.integral_const_mul, hprodInt]
  have hsinhNe : Real.sinh μ ≠ 0 := (Real.sinh_pos_iff.mpr hμ).ne'
  rw [hpowdiff, hsinh]
  rw [pow_succ]
  field_simp [hsinhNe]
  ring

/-- The sine coefficient of the classical derivative of `P`, including the harmless value at
the singular point, is the value used in §4. -/
theorem fourierP_prime_sine_integral {lam : ℝ} (hlam : 0 < lam)
    (m : ℕ) (hm : 0 < m) :
    (1 / π) * ∫ α in (-π)..π,
      fourierPPrime lam α * Real.sin ((m : ℝ) * α) =
      Real.exp (-2 * lam * (m : ℝ)) - 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  let μ : ℝ := 2 * lam
  have hμ : 0 < μ := by dsimp [μ]; linarith
  have hfirst := fourier_sin_kernel_integral hμ n
  have hcot := fourierCotSin_integrable_integral n
  have hdenPos (α : ℝ) : 0 < Real.cosh μ - Real.cos α := by
    have hcosh : 1 < Real.cosh μ := Real.one_lt_cosh.mpr hμ.ne'
    linarith [Real.cos_le_one α]
  have hdenCont : Continuous (fun α : ℝ => Real.cosh μ - Real.cos α) := by fun_prop
  have hnumCont : Continuous (fun α : ℝ => Real.sin α *
      Real.sin (((n + 1 : ℕ) : ℝ) * α)) := by fun_prop
  have hratioCont : Continuous (fun α : ℝ =>
      Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
        (Real.cosh μ - Real.cos α)) :=
    hnumCont.div hdenCont (fun α => (hdenPos α).ne')
  have hratioInt : IntervalIntegrable (fun α : ℝ =>
      Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
        (Real.cosh μ - Real.cos α)) volume (-π) π :=
    hratioCont.intervalIntegrable _ _
  have hEq :
      (fun α => fourierPPrime lam α *
        Real.sin (((n + 1 : ℕ) : ℝ) * α)) =ᵐ[volume.restrict (uIoc (-π) π)]
      (fun α => (1 / 2 : ℝ) *
        (Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
            (Real.cosh μ - Real.cos α) - fourierCotSin n α)) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα0
    simp [fourierPPrime, fourierCotSin, μ, hα0]
    ring
  have hprimeInt : IntervalIntegrable
      (fun α => fourierPPrime lam α * Real.sin (((n + 1 : ℕ) : ℝ) * α))
      volume (-π) π := by
    have hrhs : IntervalIntegrable (fun α => (1 / 2 : ℝ) *
        (Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
            (Real.cosh μ - Real.cos α) - fourierCotSin n α)) volume (-π) π := by
      exact ((hratioInt.sub hcot.1).const_mul (1 / 2 : ℝ))
    exact hrhs.congr_ae hEq.symm
  have hprimeIntegral :
      ∫ α in (-π)..π, fourierPPrime lam α *
          Real.sin (((n + 1 : ℕ) : ℝ) * α) =
        (1 / 2 : ℝ) * (2 * π * Real.exp (-μ) ^ (n + 1) - 2 * π) := by
    calc
      ∫ α in (-π)..π, fourierPPrime lam α *
          Real.sin (((n + 1 : ℕ) : ℝ) * α) =
          ∫ α in (-π)..π, (1 / 2 : ℝ) *
            (Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
                (Real.cosh μ - Real.cos α) - fourierCotSin n α) :=
          intervalIntegral.integral_congr_ae_restrict hEq
      _ = (1 / 2 : ℝ) *
            ((∫ α in (-π)..π,
                Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
                  (Real.cosh μ - Real.cos α)) -
              ∫ α in (-π)..π, fourierCotSin n α) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_sub hratioInt hcot.1]
      _ = (1 / 2 : ℝ) * (2 * π * Real.exp (-μ) ^ (n + 1) - 2 * π) := by
          rw [hfirst, hcot.2]
  have hExp : Real.exp (-2 * lam * ((n + 1 : ℕ) : ℝ)) =
      Real.exp (-μ) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [μ]
    push_cast
    ring
  rw [hprimeIntegral, hExp]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp [hπ]

/-- The `m`-th summand in the expansion of `log (cosh λ)`, with `m ≥ 1`. -/
noncomputable def logCoshExpTerm (lam : ℝ) (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m / (m : ℝ) * (Real.exp (-2 * lam * m) - 1)

/-- The ordered partial sum of the expansion of `log (cosh λ)`, indexed from `m = 1`. -/
noncomputable def logCoshExpPartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, logCoshExpTerm lam m

/-- The `n`-th summand after reindexing `m = n + 1`. -/
noncomputable def logCoshExpRangeTerm (lam : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) *
    (Real.exp (-2 * lam * ((n : ℝ) + 1)) - 1)

/-- The same ordered partial sums, expressed as a range starting at zero. -/
noncomputable def logCoshExpRangePartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, logCoshExpRangeTerm lam n

/-- The exponential ratio used in the integral representation of the partial sums. -/
noncomputable def logCoshExpRatio (lam : ℝ) : ℝ := Real.exp (-2 * lam)

private theorem alternating_geom_partial (N : ℕ) (x : ℝ) (hx : 1 + x ≠ 0) :
    (∑ n ∈ Finset.range N, (-x) ^ n) = (1 - (-x) ^ N) / (1 + x) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      field_simp
      ring

private theorem logCoshExpRangeTerm_eq_integral (lam : ℝ) (n : ℕ) :
    logCoshExpRangeTerm lam n =
      ∫ x in logCoshExpRatio lam..1, (-x) ^ n := by
  unfold logCoshExpRangeTerm logCoshExpRatio
  rw [show (fun x : ℝ => (-x) ^ n) = fun x => (-1 : ℝ) ^ n * x ^ n by
    funext x
    rw [neg_pow]]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have hexp : Real.exp (-2 * lam * ((n : ℝ) + 1)) =
      Real.exp (-2 * lam) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  rw [pow_succ]
  ring

private theorem logCoshExpRangePartial_eq_integral {lam : ℝ} (hlam : 0 < lam) (N : ℕ) :
    logCoshExpRangePartial lam N =
      ∫ x in logCoshExpRatio lam..1, (1 - (-x) ^ N) / (1 + x) := by
  unfold logCoshExpRangePartial
  have hsum :
      (∫ x in logCoshExpRatio lam..1, ∑ n ∈ Finset.range N, (-x) ^ n) =
        ∑ n ∈ Finset.range N, ∫ x in logCoshExpRatio lam..1, (-x) ^ n := by
    rw [intervalIntegral.integral_finsetSum]
    intro n hn
    exact (continuous_id.neg.pow n).intervalIntegrable _ _
  calc
    ∑ n ∈ Finset.range N, logCoshExpRangeTerm lam n =
        ∑ n ∈ Finset.range N, ∫ x in logCoshExpRatio lam..1, (-x) ^ n := by
          refine Finset.sum_congr rfl fun n hn => ?_
          exact logCoshExpRangeTerm_eq_integral lam n
    _ = ∫ x in logCoshExpRatio lam..1, ∑ n ∈ Finset.range N, (-x) ^ n := hsum.symm
    _ = ∫ x in logCoshExpRatio lam..1, (1 - (-x) ^ N) / (1 + x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hratio : 0 < logCoshExpRatio lam := Real.exp_pos _
          have hratio_lt_one : logCoshExpRatio lam < 1 := by
            unfold logCoshExpRatio
            rw [Real.exp_lt_one_iff]
            linarith
          have hmem : x ∈ Icc (logCoshExpRatio lam) 1 := by
            simpa [uIcc_of_le hratio_lt_one.le] using hx
          have hx0 : 0 ≤ x := le_trans hratio.le hmem.1
          have hden : 1 + x ≠ 0 := by linarith
          exact alternating_geom_partial N x hden

private theorem logCoshExpTarget_eq_integral {lam : ℝ} (hlam : 0 < lam) :
    ∫ x in logCoshExpRatio lam..1, (1 + x)⁻¹ =
      Real.log 2 - Real.log (1 + logCoshExpRatio lam) := by
  have hratio : 0 < logCoshExpRatio lam := Real.exp_pos _
  have hratio_lt_one : logCoshExpRatio lam < 1 := by
    unfold logCoshExpRatio
    rw [Real.exp_lt_one_iff]
    linarith
  calc
    ∫ x in logCoshExpRatio lam..1, (1 + x)⁻¹ =
        ∫ x in logCoshExpRatio lam..1, (x + 1)⁻¹ := by congr 1; funext x; ring
    _ = ∫ x in logCoshExpRatio lam + 1..1 + 1, x⁻¹ := by
        rw [intervalIntegral.integral_comp_add_right]
    _ = Real.log (2 / (1 + logCoshExpRatio lam)) := by
        rw [integral_inv_of_pos (by linarith) (by norm_num)]
        congr 1; ring
    _ = Real.log 2 - Real.log (1 + logCoshExpRatio lam) := by
        rw [Real.log_div (by norm_num) (by positivity)]

private theorem logCoshExpRemainder_bound {lam : ℝ} (hlam : 0 < lam) (N : ℕ) :
    |logCoshExpRangePartial lam N -
        (Real.log 2 - Real.log (1 + logCoshExpRatio lam))| ≤ 1 / ((N : ℝ) + 1) := by
  let q := logCoshExpRatio lam
  have hq : 0 < q := by simp [q, logCoshExpRatio, Real.exp_pos]
  have hq1 : q < 1 := by
    dsimp [q, logCoshExpRatio]
    rw [Real.exp_lt_one_iff]
    linarith
  have hqle : q ≤ 1 := hq1.le
  have hxmem (x : ℝ) (hx : x ∈ uIcc q 1) : x ∈ Icc q 1 := by
    simpa [uIcc_of_le hqle] using hx
  have hdom : ∀ x ∈ Icc q 1, 0 < 1 + x := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans hq.le hx.1
    linarith
  have hJint : IntervalIntegrable (fun x : ℝ => x ^ N / (1 + x)) volume q 1 := by
    apply ContinuousOn.intervalIntegrable
    refine (continuousOn_id.pow N).div (continuousOn_const.add continuousOn_id) ?_
    intro x hx
    exact (hdom x (hxmem x hx)).ne'
  have hInvInt : IntervalIntegrable (fun x : ℝ => (1 + x)⁻¹) volume q 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.add continuousOn_id).inv₀
      (fun x hx => (hdom x (hxmem x hx)).ne')
  have hKernelInt :
      IntervalIntegrable (fun x : ℝ => (1 - (-x) ^ N) / (1 + x)) volume q 1 := by
    apply ContinuousOn.intervalIntegrable
    refine (continuousOn_const.sub (continuousOn_id.neg.pow N)).div
      (continuousOn_const.add continuousOn_id) ?_
    intro x hx
    exact (hdom x (hxmem x hx)).ne'
  have hJnonneg : 0 ≤ ∫ x in q..1, x ^ N / (1 + x) :=
    intervalIntegral.integral_nonneg hqle fun x hx => by
      have hx0 : 0 ≤ x := le_trans hq.le hx.1
      exact div_nonneg (pow_nonneg hx0 _) (le_of_lt (hdom x hx))
  have hJbound : ∫ x in q..1, x ^ N / (1 + x) ≤ 1 / ((N : ℝ) + 1) := by
    calc
      ∫ x in q..1, x ^ N / (1 + x) ≤ ∫ x in q..1, x ^ N := by
        have hPowInt : IntervalIntegrable (fun x : ℝ => x ^ N) volume q 1 :=
          (continuous_id.pow N).intervalIntegrable _ _
        apply intervalIntegral.integral_mono_on hqle hJint hPowInt
        intro x hx
        have hx0 : 0 ≤ x := le_trans hq.le hx.1
        have hxden : 1 ≤ 1 + x := by linarith
        exact div_le_self (pow_nonneg hx0 _) hxden
      _ = (1 - q ^ (N + 1)) / ((N : ℝ) + 1) := by
        rw [integral_pow]
        simp
      _ ≤ 1 / ((N : ℝ) + 1) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [pow_nonneg hq.le (N + 1)]
  have herror :
      logCoshExpRangePartial lam N -
          (Real.log 2 - Real.log (1 + q)) =
        -((-1 : ℝ) ^ N) * (∫ x in q..1, x ^ N / (1 + x)) := by
    rw [logCoshExpRangePartial_eq_integral hlam N]
    have htarget : Real.log 2 - Real.log (1 + q) = ∫ x in q..1, (1 + x)⁻¹ := by
      simpa [q] using (logCoshExpTarget_eq_integral hlam).symm
    rw [htarget]
    rw [← intervalIntegral.integral_sub hKernelInt hInvInt]
    have hfun : (fun x : ℝ => (1 - (-x) ^ N) / (1 + x) - (1 + x)⁻¹) =
        fun x => -((-1 : ℝ) ^ N) * (x ^ N / (1 + x)) := by
      funext x
      rw [neg_pow]
      field_simp
      ring
    rw [hfun, intervalIntegral.integral_const_mul]
  calc
    |logCoshExpRangePartial lam N -
        (Real.log 2 - Real.log (1 + q))| =
        ∫ x in q..1, x ^ N / (1 + x) := by
          rw [herror]
          simp [abs_of_nonneg hJnonneg]
    _ ≤ 1 / ((N : ℝ) + 1) := hJbound

private theorem tendsto_logCoshExpRangePartial {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (logCoshExpRangePartial lam) atTop
      (𝓝 (Real.log 2 - Real.log (1 + logCoshExpRatio lam))) := by
  have hsmall : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have habs : Tendsto (fun N : ℕ =>
      |logCoshExpRangePartial lam N -
        (Real.log 2 - Real.log (1 + logCoshExpRatio lam))|) atTop (𝓝 0) :=
    squeeze_zero (fun N => abs_nonneg _) (fun N => logCoshExpRemainder_bound hlam N) hsmall
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

private theorem logCoshExpTarget_eq_lambda_sub_log_cosh {lam : ℝ} (hlam : 0 < lam) :
    Real.log 2 - Real.log (1 + logCoshExpRatio lam) =
      lam - Real.log (Real.cosh lam) := by
  have hq : 0 < logCoshExpRatio lam := Real.exp_pos _
  have hq1 : logCoshExpRatio lam < 1 := by
    unfold logCoshExpRatio
    rw [Real.exp_lt_one_iff]
    linarith
  have hfactor : Real.cosh lam = Real.exp lam * ((1 + logCoshExpRatio lam) / 2) := by
    rw [Real.cosh_eq]
    have hExp : Real.exp (-lam) = Real.exp lam * logCoshExpRatio lam := by
      unfold logCoshExpRatio
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hExp]
    ring
  have hlogfactor : Real.log (Real.cosh lam) =
      lam + Real.log ((1 + logCoshExpRatio lam) / 2) := by
    rw [hfactor, Real.log_mul (Real.exp_ne_zero _) (by positivity)]
    simp only [Real.log_exp]
  have hlogdiv : Real.log ((1 + logCoshExpRatio lam) / 2) =
      Real.log (1 + logCoshExpRatio lam) - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num)]
  rw [hlogfactor, hlogdiv]
  ring

/-- The ordered partial sums in the paper's logarithmic expansion converge to
`λ - log (cosh λ)`, so `log (cosh λ) = λ - ∑_{m>0} (-1)^m (e^{-2λm}-1)/m`. -/
theorem tendsto_logCoshExpPartial {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (logCoshExpPartial lam) atTop (𝓝 (lam - Real.log (Real.cosh lam))) := by
  have hEq : ∀ N : ℕ, logCoshExpPartial lam N = logCoshExpRangePartial lam N := by
    intro N
    unfold logCoshExpPartial logCoshExpRangePartial
    rw [sum_Icc_one_eq_sum_range]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp [logCoshExpTerm, logCoshExpRangeTerm]
  rw [show lam - Real.log (Real.cosh lam) =
      Real.log 2 - Real.log (1 + logCoshExpRatio lam) from
        (logCoshExpTarget_eq_lambda_sub_log_cosh hlam).symm]
  exact (tendsto_logCoshExpRangePartial hlam).congr'
    (Filter.Eventually.of_forall fun N => (hEq N).symm)

/-! ### The algebra of (4.3) and its ordered partial sums -/

/-- The ordered partial sums of `∑ (-1)^m tanh(λm)/m`. -/
noncomputable def altTanhPartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam)

/-- The ordered partial sums of the correction term in (4.3). -/
noncomputable def logCoshTauCorrectionPartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam) *
      (Real.exp (-2 * lam * m) - 1)

private theorem tanh_exp_identity (x : ℝ) :
    (1 + Real.tanh x) * (Real.exp (-2 * x) - 1) = -2 * Real.tanh x := by
  rw [Real.tanh_eq]
  have he : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have he' : Real.exp (-x) ≠ 0 := (Real.exp_pos (-x)).ne'
  have hexp : Real.exp (-2 * x) = Real.exp (-x) / Real.exp x := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hexp]
  field_simp [he, he']
  ring

private theorem logCosh_tanh_term_identity (lam : ℝ) (m : ℕ) :
    logCoshExpTerm lam m +
        (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam) *
          (Real.exp (-2 * lam * m) - 1) =
      -2 * ((-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam)) := by
  unfold logCoshExpTerm
  have h := tanh_exp_identity ((m : ℝ) * lam)
  have hexp' : Real.exp (-2 * lam * (m : ℝ)) = Real.exp (-2 * ((m : ℝ) * lam)) := by
    congr 1
    ring
  rw [hexp'] at ⊢
  calc
    (-1 : ℝ) ^ m / (m : ℝ) * (Real.exp (-2 * ((m : ℝ) * lam)) - 1) +
        (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam) *
          (Real.exp (-2 * ((m : ℝ) * lam)) - 1) =
      ((-1 : ℝ) ^ m / (m : ℝ)) *
        ((1 + Real.tanh ((m : ℝ) * lam)) *
          (Real.exp (-2 * ((m : ℝ) * lam)) - 1)) := by ring
    _ = _ := by rw [h]; ring

private theorem finite_logCosh_tanh_identity (lam : ℝ) (N : ℕ) :
    logCoshExpPartial lam N + logCoshTauCorrectionPartial lam N =
      -2 * altTanhPartial lam N := by
  unfold logCoshExpPartial logCoshTauCorrectionPartial altTanhPartial
  calc
    (∑ m ∈ Finset.Icc 1 N, logCoshExpTerm lam m) +
        ∑ m ∈ Finset.Icc 1 N,
          (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam) *
            (Real.exp (-2 * lam * m) - 1) =
      ∑ m ∈ Finset.Icc 1 N,
        (logCoshExpTerm lam m +
          (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam) *
            (Real.exp (-2 * lam * m) - 1)) := by rw [← Finset.sum_add_distrib]
    _ = ∑ m ∈ Finset.Icc 1 N,
        (-2 * ((-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam))) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          exact logCosh_tanh_term_identity lam m
    _ = -2 * ∑ m ∈ Finset.Icc 1 N,
        ((-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam)) := by rw [Finset.mul_sum]

/-- **Equation (4.3)** in ordered-partial-sum form. The left series converges as a consequence
of the identity with the convergent expansion of `log(cosh λ)` and the convergence in `identity44`.
The right-hand convergence and the value relation are included. -/
theorem identity43 (lam : ℝ) (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (fun N => Real.log (Real.cosh lam) - logCoshTauCorrectionPartial lam N)
        atTop (𝓝 (lam + 2 * S)) := by
  obtain ⟨S, _T, hS, _hT, _hpos, _hval⟩ := identity44 lam hlam
  have hS' : Tendsto (altTanhPartial lam) atTop (𝓝 S) := by
    change Tendsto (fun N : ℕ =>
      ∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam))
      atTop (𝓝 S)
    exact hS
  have hA : Tendsto (logCoshExpPartial lam) atTop
      (𝓝 (lam - Real.log (Real.cosh lam))) := tendsto_logCoshExpPartial hlam
  have hConst : Tendsto (fun _ : ℕ => Real.log (Real.cosh lam)) atTop
      (𝓝 (Real.log (Real.cosh lam))) := tendsto_const_nhds
  have hTwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have h1 : Tendsto (fun N : ℕ => Real.log (Real.cosh lam) + logCoshExpPartial lam N)
      atTop (𝓝 (Real.log (Real.cosh lam) + (lam - Real.log (Real.cosh lam)))) :=
    hConst.add hA
  have h2 : Tendsto (fun N : ℕ => 2 * altTanhPartial lam N) atTop (𝓝 (2 * S)) := hTwo.mul hS'
  have hsum : Tendsto (fun N : ℕ =>
      Real.log (Real.cosh lam) + logCoshExpPartial lam N + 2 * altTanhPartial lam N)
      atTop (𝓝 (Real.log (Real.cosh lam) + (lam - Real.log (Real.cosh lam)) + 2 * S)) := by
    simpa [add_assoc] using h1.add h2
  have hpoint (N : ℕ) :
      Real.log (Real.cosh lam) - logCoshTauCorrectionPartial lam N =
        Real.log (Real.cosh lam) + logCoshExpPartial lam N + 2 * altTanhPartial lam N := by
    have h := finite_logCosh_tanh_identity lam N
    linarith
  refine ⟨S, hS', ?_⟩
  have hsum' : Tendsto
      (fun N : ℕ => Real.log (Real.cosh lam) - logCoshTauCorrectionPartial lam N) atTop
      (𝓝 (Real.log (Real.cosh lam) + (lam - Real.log (Real.cosh lam)) + 2 * S)) :=
    hsum.congr' (Filter.Eventually.of_forall fun N => (hpoint N).symm)
  have hlim : Real.log (Real.cosh lam) + (lam - Real.log (Real.cosh lam)) + 2 * S =
      lam + 2 * S := by ring
  rw [hlim] at hsum'
  exact hsum'

end PottsDiscontinuity

