module

public import Mathlib
public import PottsDiscontinuity.Analysis.Section4TauIntegral

/-!
# The source-coordinate logarithmic derivative integral

This file transports the Abel-summed Fourier computation from the `α` coordinate to the
source coordinate `x = k(α)`.  The logarithmic point is handled by splitting the substitution
at zero; the literal and continuous representatives of `τ` agree almost everywhere.
-/

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

/-- The source profile `ℓ(x) = log |M(e^{ix})|`, pulled back from the explicit `P` profile. -/
noncomputable def fourierEll (lam : ℝ) (x : ℝ) : ℝ :=
  fourierP lam (Bethe.kInv lam x)

/-- The source derivative representative obtained by differentiating `P = ℓ ∘ k` away from zero.
Its value at the logarithmic point is immaterial to interval integrals. -/
noncomputable def fourierEllPrime (lam : ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    fourierPPrime lam (Bethe.kInv lam x) / Bethe.Xi lam (Bethe.kInv lam x)

/-- The ordered partial sums of the explicit Section 4 series for `τ(k(α))`. -/
noncomputable def fourierTauPartial (lam α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (-1 : ℝ) ^ (n + 1) / (π * ((n : ℝ) + 1)) *
      Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) *
      Real.sin (((n + 1 : ℕ) : ℝ) * α)

/-- The literal ordered series for `τ(k(α))`, expressed as the limit of its partial sums. -/
noncomputable def fourierTauSeries (lam α : ℝ) : ℝ :=
  limUnder atTop (fourierTauPartial lam α)

/-- This local ordered-series definition is the same representative as Proposition 2.1. -/
theorem fourierTauSeries_eq_Bethe_tauSeries (lam α : ℝ) :
    fourierTauSeries lam α = Bethe.tauSeries lam α := by
  rfl

/-- The continuous representative of τ(k(α)) on the circle. -/
noncomputable def fourierTauAlphaCont (lam α : ℝ) : ℝ :=
  Bethe.TcontFn lam α / (2 * π)

/-- The continuous representative of source τ(x), expressed through k⁻¹. -/
noncomputable def fourierTauXCont (lam x : ℝ) : ℝ :=
  fourierTauAlphaCont lam (Bethe.kInv lam x)

/-- The actual ordered series representative of source τ(x). -/
noncomputable def fourierTauXSeries (lam x : ℝ) : ℝ :=
  fourierTauSeries lam (Bethe.kInv lam x)

/-- The continuous source-coordinate integrand used at the single removable point. -/
noncomputable def fourierEllTauCont (lam x : ℝ) : ℝ :=
  fourierEllPrime lam x * fourierTauXCont lam x

private theorem continuous_fourierTauAlphaCont {lam : ℝ} (hlam : 0 < lam) :
    Continuous (fourierTauAlphaCont lam) := by
  change Continuous (fun α => Bethe.TcontFn lam α / (2 * π))
  exact (Bethe.continuous_TcontFn hlam).div_const (2 * π)

private theorem continuous_fourierTauXCont {lam : ℝ} (hlam : 0 < lam) :
    Continuous (fourierTauXCont lam) := by
  exact (continuous_fourierTauAlphaCont hlam).comp (Bethe.continuous_kInv hlam)

private theorem kInv_mem_Ioo {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) : Bethe.kInv lam x ∈ Ioo (-π) π := by
  have hIcc := Bethe.kInv_mem_Icc hlam (Ioo_subset_Icc_self hx)
  have hαnePi : Bethe.kInv lam x ≠ π := by
    intro h
    have hx' := Bethe.kMap_kInv hlam x
    rw [h, Bethe.kMap_pi] at hx'
    linarith [hx.2]
  have hαneNegPi : Bethe.kInv lam x ≠ -π := by
    intro h
    have hx' := Bethe.kMap_kInv hlam x
    rw [h, Bethe.kMap_neg_pi] at hx'
    linarith [hx.1]
  exact ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hαneNegPi),
    lt_of_le_of_ne hIcc.2 hαnePi⟩

private theorem fourierTauXSeries_eq_cont {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) : fourierTauXSeries lam x = fourierTauXCont lam x := by
  unfold fourierTauXSeries
  rw [fourierTauSeries_eq_Bethe_tauSeries]
  unfold fourierTauXCont fourierTauAlphaCont
  exact Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨
    (kInv_mem_Ioo hlam hx).1, (kInv_mem_Ioo hlam hx).2⟩)

private theorem kInv_ne_zero {lam x : ℝ} (hlam : 0 < lam) (hx : x ≠ 0) :
    Bethe.kInv lam x ≠ 0 := by
  intro h
  have := Bethe.kMap_kInv hlam x
  rw [h, Bethe.kMap_zero] at this
  exact hx this.symm

/-- The inverse map has derivative `1 / Ξ_λ(k⁻¹(x))`. -/
private theorem hasDerivAt_kInv_of_kMap {lam x : ℝ} (hlam : 0 < lam) :
    HasDerivAt (Bethe.kInv lam)
      ((Bethe.Xi lam (Bethe.kInv lam x))⁻¹) x := by
  let α := Bethe.kInv lam x
  have hα : Bethe.kInv lam x = α := rfl
  have hk := Bethe.hasDerivAt_kMap hlam α
  have hki : DifferentiableAt ℝ (Bethe.kInv lam) x :=
    (Bethe.analyticAt_kInv hlam x).differentiableAt
  have hc := hk.comp x (hki.hasDerivAt)
  have hcomp : HasDerivAt (fun y : ℝ => y)
      (Bethe.Xi lam α * deriv (Bethe.kInv lam) x) x := by
    have hfun : (fun y : ℝ => Bethe.kMap lam (Bethe.kInv lam y)) = fun y => y :=
      funext (Bethe.kMap_kInv hlam)
    change HasDerivAt (fun y : ℝ => Bethe.kMap lam (Bethe.kInv lam y))
      (Bethe.Xi lam α * deriv (Bethe.kInv lam) x) x at hc
    simpa only [← hfun] using hc
  have hprod : Bethe.Xi lam α * deriv (Bethe.kInv lam) x = 1 := by
    have := hcomp.deriv
    simpa using this.symm
  have hXi : Bethe.Xi lam α ≠ 0 := (Bethe.Xi_pos hlam α).ne'
  have hderiv : deriv (Bethe.kInv lam) x = (Bethe.Xi lam α)⁻¹ := by
    calc
      deriv (Bethe.kInv lam) x =
          deriv (Bethe.kInv lam) x *
            (Bethe.Xi lam α * (Bethe.Xi lam α)⁻¹) := by rw [mul_inv_cancel₀ hXi, mul_one]
      _ = (Bethe.Xi lam α * deriv (Bethe.kInv lam) x) *
            (Bethe.Xi lam α)⁻¹ := by ring
      _ = 1 * (Bethe.Xi lam α)⁻¹ := by rw [hprod]
      _ = (Bethe.Xi lam α)⁻¹ := one_mul _
  convert hki.hasDerivAt.congr_deriv hderiv using 1

/-- Away from the logarithmic singularity, `fourierEll` has the source derivative. -/
theorem fourierEll_hasDerivAt {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) (hx0 : x ≠ 0) :
    HasDerivAt (fourierEll lam) (fourierEllPrime lam x) x := by
  have hα := kInv_mem_Ioo hlam hx
  have hα0 := kInv_ne_zero hlam hx0
  have hP := fourierP_hasDerivAt hlam hα hα0
  have hki := hasDerivAt_kInv_of_kMap (lam := lam) (x := x) hlam
  have hcomp := hP.comp x hki
  have hderiv : fourierPPrime lam (Bethe.kInv lam x) *
      (Bethe.Xi lam (Bethe.kInv lam x))⁻¹ = fourierEllPrime lam x := by
    simp [fourierEllPrime, hx0, div_eq_mul_inv]
  change HasDerivAt (fourierP lam ∘ Bethe.kInv lam) (fourierEllPrime lam x) x
  convert hcomp.congr_deriv hderiv using 1

/-- The profile fourierEll is the source logarithm log |M(e^(ix))| on the punctured
fundamental interval, with c² = 2 - 2Δ = 2 + 2 cosh λ. -/
theorem fourierEll_eq_log_norm {lam c x : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hx : x ∈ Ioo (-π) π)
    (hx0 : x ≠ 0) :
    fourierEll lam x = Real.log ‖BetheAnsatz.M c (Complex.exp (I * (x : ℂ)))‖ := by
  have hα := kInv_mem_Ioo hlam hx
  have hα0 := kInv_ne_zero hlam hx0
  have hcos : Real.cos (Bethe.kInv lam x) < 1 := by
    have hne : Real.cos (Bethe.kInv lam x) ≠ 1 := by
      intro h
      have hαbounds : -(2 * π) < Bethe.kInv lam x ∧ Bethe.kInv lam x < 2 * π := by
        constructor <;> nlinarith [Real.pi_pos, hα.1, hα.2]
      have hperiod := (Real.cos_eq_one_iff_of_lt_of_lt hαbounds.1 hαbounds.2).mp h
      exact hα0 (by omega)
    exact lt_of_le_of_ne (Real.cos_le_one _) hne
  calc
    fourierEll lam x = fourierP lam (Bethe.kInv lam x) := rfl
    _ = Real.log ‖BetheAnsatz.M c
        (Complex.exp (I * (Bethe.kMap lam (Bethe.kInv lam x) : ℂ)))‖ :=
      fourierP_eq_log_norm hlam hc hcos
    _ = Real.log ‖BetheAnsatz.M c (Complex.exp (I * (x : ℂ)))‖ := by
      rw [Bethe.kMap_kInv hlam]

private theorem fourier_cos_lt_one_of_mem_Ioo {α : ℝ} (hα : α ∈ Ioo (-π) π)
    (hα0 : α ≠ 0) : Real.cos α < 1 := by
  have hne : Real.cos α ≠ 1 := by
    intro h
    have hbounds : -(2 * π) < α ∧ α < 2 * π := by
      constructor <;> nlinarith [Real.pi_pos, hα.1, hα.2]
    have hperiod := (Real.cos_eq_one_iff_of_lt_of_lt hbounds.1 hbounds.2).mp h
    exact hα0 (by omega)
  exact lt_of_le_of_ne (Real.cos_le_one α) hne

private theorem continuousAt_fourierPPrime_of_mem_Ioo {lam α : ℝ}
    (hα : α ∈ Ioo (-π) π) (hα0 : α ≠ 0) :
    ContinuousAt (fourierPPrime lam) α := by
  have hcos := fourier_cos_lt_one_of_mem_Ioo hα hα0
  have hden1 : 0 < Real.cosh (2 * lam) - Real.cos α := by
    have hcosh : 1 ≤ Real.cosh (2 * lam) := Real.one_le_cosh _
    linarith [Real.cos_le_one α]
  have hden2 : 0 < 1 - Real.cos α := by linarith
  let q : ℝ → ℝ := fun x => (1 / 2 : ℝ) *
    (Real.sin x / (Real.cosh (2 * lam) - Real.cos x) -
      Real.sin x / (1 - Real.cos x))
  have hq : ContinuousAt q α := by
    have hc1 := Real.continuous_sin.continuousAt.div
      (continuousAt_const.sub Real.continuous_cos.continuousAt) hden1.ne'
    have hc2 := Real.continuous_sin.continuousAt.div
      (continuousAt_const.sub Real.continuous_cos.continuousAt) hden2.ne'
    exact continuousAt_const.mul (hc1.sub hc2)
  have hEq : fourierPPrime lam =ᶠ[𝓝 α] q := by
    filter_upwards [eventually_ne_nhds hα0] with x hx
    simp [fourierPPrime, q, hx]
  exact hq.congr hEq.symm

private theorem continuous_Xi_lambda {lam : ℝ} (hlam : 0 < lam) :
    Continuous (Bethe.Xi lam) := by
  unfold Bethe.Xi
  refine continuous_const.div (continuous_const.sub Real.continuous_cos) ?_
  intro α
  have hcosh : 1 < Real.cosh lam := Real.one_lt_cosh.mpr hlam.ne'
  linarith [Real.cos_le_one α]

private theorem measurable_fourierEllPrime {lam : ℝ} (hlam : 0 < lam) :
    Measurable (fourierEllPrime lam) := by
  have hprime : Measurable (fourierPPrime lam) := by
    unfold fourierPPrime
    exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
  unfold fourierEllPrime
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (Measurable.div (hprime.comp (Bethe.continuous_kInv hlam).measurable)
      ((continuous_Xi_lambda hlam).measurable.comp
        (Bethe.continuous_kInv hlam).measurable))

private theorem continuousAt_fourierEllPrime {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) (hx0 : x ≠ 0) :
    ContinuousAt (fourierEllPrime lam) x := by
  have hα := kInv_mem_Ioo hlam hx
  have hα0 := kInv_ne_zero hlam hx0
  have hnum : ContinuousAt (fun y => fourierPPrime lam (Bethe.kInv lam y)) x :=
    (continuousAt_fourierPPrime_of_mem_Ioo hα hα0).comp
      (Bethe.continuous_kInv hlam).continuousAt
  have hden : ContinuousAt (fun y => Bethe.Xi lam (Bethe.kInv lam y)) x :=
    (continuous_Xi_lambda hlam).continuousAt.comp
      (Bethe.continuous_kInv hlam).continuousAt
  have hXi0 : Bethe.Xi lam (Bethe.kInv lam x) ≠ 0 :=
    (Bethe.Xi_pos hlam _).ne'
  have hquot : ContinuousAt
      (fun y => fourierPPrime lam (Bethe.kInv lam y) /
        Bethe.Xi lam (Bethe.kInv lam y)) x := hnum.div hden hXi0
  have hEq : fourierEllPrime lam =ᶠ[𝓝 x]
      (fun y => fourierPPrime lam (Bethe.kInv lam y) /
        Bethe.Xi lam (Bethe.kInv lam y)) := by
    filter_upwards [eventually_ne_nhds hx0] with y hy
    simp [fourierEllPrime, hy]
  exact hquot.congr hEq.symm

private theorem continuousAt_fourierEllTauCont {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) (hx0 : x ≠ 0) :
    ContinuousAt (fourierEllTauCont lam) x := by
  exact (continuousAt_fourierEllPrime hlam hx hx0).mul
    ((continuous_fourierTauXCont hlam).continuousAt)

noncomputable def fourierXiLower (lam : ℝ) : ℝ :=
  Real.sinh lam / (Real.cosh lam + 1)

private theorem fourierXiLower_pos {lam : ℝ} (hlam : 0 < lam) :
    0 < fourierXiLower lam := by
  dsimp [fourierXiLower]
  exact div_pos (Real.sinh_pos_iff.mpr hlam) (by positivity)

private theorem fourierEllTauCont_bound {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) :
    |fourierEllTauCont lam x| ≤
      fourierTauProductControl lam / fourierXiLower lam := by
  have hC0 := fourierTauProductControl_nonneg hlam
  by_cases hx0 : x = 0
  · subst x
    simp [fourierEllTauCont, fourierEllPrime]
    exact div_nonneg hC0 (fourierXiLower_pos hlam).le
  have hα := kInv_mem_Ioo hlam hx
  have hα0 := kInv_ne_zero hlam hx0
  have hαcc : Bethe.kInv lam x ∈ Icc (-π) π := Ioo_subset_Icc_self hα
  have htaueq := Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨hα.1, hα.2⟩)
  have hxiPos := Bethe.Xi_pos hlam (Bethe.kInv lam x)
  have hxiLower : fourierXiLower lam ≤ Bethe.Xi lam (Bethe.kInv lam x) :=
    (Bethe.Xi_bounds hlam (Bethe.kInv lam x)).1
  have hrewrite :
      fourierEllTauCont lam x =
        (fourierPPrime lam (Bethe.kInv lam x) /
          Bethe.Xi lam (Bethe.kInv lam x)) *
          Bethe.tauSeries lam (Bethe.kInv lam x) := by
    simp [fourierEllTauCont, fourierEllPrime, fourierTauXCont,
      fourierTauAlphaCont, hx0, ← htaueq]
  rw [hrewrite]
  have hnum : |fourierPPrime lam (Bethe.kInv lam x) *
      Bethe.tauSeries lam (Bethe.kInv lam x)| ≤ fourierTauProductControl lam :=
    fourierPPrime_tauSeries_abs_bound hlam hαcc
  have hdiv :
      |(fourierPPrime lam (Bethe.kInv lam x) /
          Bethe.Xi lam (Bethe.kInv lam x)) *
          Bethe.tauSeries lam (Bethe.kInv lam x)| =
        |fourierPPrime lam (Bethe.kInv lam x) *
          Bethe.tauSeries lam (Bethe.kInv lam x)| /
          Bethe.Xi lam (Bethe.kInv lam x) := by
    have heq : (fourierPPrime lam (Bethe.kInv lam x) /
        Bethe.Xi lam (Bethe.kInv lam x)) *
        Bethe.tauSeries lam (Bethe.kInv lam x) =
        (fourierPPrime lam (Bethe.kInv lam x) *
          Bethe.tauSeries lam (Bethe.kInv lam x)) /
          Bethe.Xi lam (Bethe.kInv lam x) := by
      field_simp [hxiPos.ne']
    rw [heq, abs_div, abs_of_pos hxiPos]
  rw [hdiv]
  calc
    |fourierPPrime lam (Bethe.kInv lam x) *
        Bethe.tauSeries lam (Bethe.kInv lam x)| /
        Bethe.Xi lam (Bethe.kInv lam x) ≤ fourierTauProductControl lam /
          Bethe.Xi lam (Bethe.kInv lam x) :=
      div_le_div_of_nonneg_right hnum hxiPos.le
    _ ≤ fourierTauProductControl lam / fourierXiLower lam :=
      div_le_div_of_nonneg_left hC0 (fourierXiLower_pos hlam) hxiLower

private theorem kMap_mem_Ioo {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Ioo (-π) π) : Bethe.kMap lam α ∈ Ioo (-π) π := by
  have hIcc := Bethe.mapsTo_kMap hlam (Ioo_subset_Icc_self hα)
  have hinj := (Bethe.strictMono_kMap hlam).injective
  have hnePi : Bethe.kMap lam α ≠ π := by
    intro h
    have heq : Bethe.kMap lam α = Bethe.kMap lam π := by rw [Bethe.kMap_pi]; exact h
    have := hinj heq
    linarith [hα.2]
  have hneNegPi : Bethe.kMap lam α ≠ -π := by
    intro h
    have heq : Bethe.kMap lam α = Bethe.kMap lam (-π) := by rw [Bethe.kMap_neg_pi]; exact h
    have := hinj heq
    linarith [hα.1]
  exact ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hneNegPi),
    lt_of_le_of_ne hIcc.2 hnePi⟩

private theorem fourierEllTauCont_comp_mul_Xi {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Ioo (-π) π) (hα0 : α ≠ 0) :
    fourierEllTauCont lam (Bethe.kMap lam α) * Bethe.Xi lam α =
      fourierPPrime lam α * Bethe.tauSeries lam α := by
  have hk0 : Bethe.kMap lam α ≠ 0 := by
    intro h
    have hinj := (Bethe.strictMono_kMap hlam).injective
    have heq : Bethe.kMap lam α = Bethe.kMap lam 0 := by rw [Bethe.kMap_zero]; exact h
    exact hα0 (hinj heq)
  have htaueq := Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨hα.1, hα.2⟩)
  unfold fourierEllTauCont fourierEllPrime fourierTauXCont fourierTauAlphaCont
  rw [ite_eq_right hk0, Bethe.kInv_kMap hlam, ← htaueq]
  field_simp [(Bethe.Xi_pos hlam α).ne']

private theorem measurable_fourierPPrime {lam : ℝ} :
    Measurable (fourierPPrime lam) := by
  unfold fourierPPrime
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

private theorem fourierTauAlphaCont_ae {lam : ℝ} (hlam : 0 < lam) :
    Bethe.tauSeries lam =ᵐ[volume.restrict (Icc (-π) π)]
      fourierTauAlphaCont lam := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume π),
    ae_restrict_of_ae (Measure.ae_ne volume (-π))] with α hα hαp hαm
  have hαoo : α ∈ Ioo (-π) π :=
    ⟨lt_of_le_of_ne hα.1 (Ne.symm hαm), lt_of_le_of_ne hα.2 hαp⟩
  exact Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨hαoo.1, hαoo.2⟩)

private theorem fourierSourceTau_eq_cont {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) :
    Bethe.tau (-Real.cosh lam) x = fourierTauXCont lam x := by
  have hparam : Bethe.lamOf (-Real.cosh lam) = lam :=
    (Bethe.eq_lamOf hlam (by simp)).symm
  change Bethe.tauSeries (Bethe.lamOf (-Real.cosh lam))
    (Bethe.kInv (Bethe.lamOf (-Real.cosh lam)) x) = _
  rw [hparam]
  exact fourierTauXSeries_eq_cont hlam hx

private theorem fourierAlphaSourceIntegrand_ae {lam : ℝ} (hlam : 0 < lam) :
    (fun α => fourierEllTauCont lam (Bethe.kMap lam α) * Bethe.Xi lam α) =ᵐ[
      volume.restrict (Icc (-π) π)]
      (fun α => fourierPPrime lam α * Bethe.tauSeries lam α) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume π),
    ae_restrict_of_ae (Measure.ae_ne volume (-π)),
    ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hαp hαm hα0
  have hαoo : α ∈ Ioo (-π) π :=
    ⟨lt_of_le_of_ne hα.1 (Ne.symm hαm), lt_of_le_of_ne hα.2 hαp⟩
  exact fourierEllTauCont_comp_mul_Xi hlam hαoo hα0

private theorem fourierAlphaSourceIntegrand_integrableOnIcc {lam : ℝ}
    (hlam : 0 < lam) :
    IntegrableOn (fun α => fourierPPrime lam α * Bethe.tauSeries lam α)
      (Icc (-π) π) volume := by
  let C := fourierTauProductControl lam
  have hC0 : 0 ≤ C := fourierTauProductControl_nonneg hlam
  have hC : ∀ α ∈ Icc (-π) π,
      |fourierPPrime lam α * Bethe.tauSeries lam α| ≤ C := by
    intro α hα
    exact fourierPPrime_tauSeries_abs_bound hlam hα
  let μ : Measure ℝ := volume.restrict (Icc (-π) π)
  have hcont : Measurable
      (fun α => fourierPPrime lam α * fourierTauAlphaCont lam α) :=
    (measurable_fourierPPrime (lam := lam)).mul
      (continuous_fourierTauAlphaCont hlam).measurable
  have hmeas : AEStronglyMeasurable
      (fun α => fourierPPrime lam α * Bethe.tauSeries lam α) μ := by
    have hae := fourierTauAlphaCont_ae hlam
    have hprod : (fun α => fourierPPrime lam α * Bethe.tauSeries lam α) =ᵐ[μ]
        (fun α => fourierPPrime lam α * fourierTauAlphaCont lam α) :=
      hae.mono fun α h => congrArg (fun y => fourierPPrime lam α * y) h
    exact hcont.aestronglyMeasurable.congr hprod.symm
  have hbound : ∀ᵐ α ∂μ,
      ‖fourierPPrime lam α * Bethe.tauSeries lam α‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with α hα
    rw [Real.norm_eq_abs]
    exact hC α hα
  have hfinite : μ univ ≠ ⊤ := by simp [μ]
  have hbound' : ∀ᵐ α ∂(μ.restrict univ),
      ‖fourierPPrime lam α * Bethe.tauSeries lam α‖ ≤ C := by
    simpa only [Measure.restrict_univ] using hbound
  have hIntUniv : IntegrableOn
      (fun α => fourierPPrime lam α * Bethe.tauSeries lam α) univ μ := by
    exact Measure.integrableOn_of_bounded (μ := μ) (s := univ) hfinite hmeas
      (M := C) hbound'
  have hInt : IntegrableOn
      (fun α => fourierPPrime lam α * Bethe.tauSeries lam α)
      (Icc (-π) π) volume := by
    change Integrable (fun α => fourierPPrime lam α * Bethe.tauSeries lam α)
      (volume.restrict (Icc (-π) π))
    simpa [μ] using hIntUniv
  exact hInt

private theorem fourierEllTauCont_integrableOnIcc {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn (fourierEllTauCont lam) (Icc (-π) π) volume := by
  have hfinite : volume (Icc (-π) π) ≠ ⊤ := by simp
  have hmeas : Measurable (fourierEllTauCont lam) :=
    (measurable_fourierEllPrime hlam).mul
      (continuous_fourierTauXCont hlam).measurable
  have hbound : ∀ᵐ x ∂(volume.restrict (Icc (-π) π)),
      ‖fourierEllTauCont lam x‖ ≤
        fourierTauProductControl lam / fourierXiLower lam := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume π),
      ae_restrict_of_ae (Measure.ae_ne volume (-π))] with x hx hxp hxm
    have hxoo : x ∈ Ioo (-π) π :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxm), lt_of_le_of_ne hx.2 hxp⟩
    rw [Real.norm_eq_abs]
    exact fourierEllTauCont_bound hlam hxoo
  have hInt : IntegrableOn (fourierEllTauCont lam) (Icc (-π) π) volume :=
    Measure.integrableOn_of_bounded hfinite hmeas.aestronglyMeasurable hbound
  exact hInt

private theorem fourierSourceIntegrand_ae {lam : ℝ} (hlam : 0 < lam) :
    (fun x => fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =ᵐ[
      volume.restrict (uIoc (-π) π)] (fourierEllTauCont lam) := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume π)] with x hx hxp
  have hxIoc : x ∈ Ioc (-π) π := by
    simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hx
  have hxIoo : x ∈ Ioo (-π) π :=
    ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxp⟩
  have htau := fourierSourceTau_eq_cont hlam hxIoo
  exact congrArg (fun y => fourierEllPrime lam x * y) htau

private theorem kMap_left_image_subset {lam : ℝ} (hlam : 0 < lam) :
    Bethe.kMap lam '' Icc (-π) 0 ⊆ Icc (-π) π := by
  intro x hx
  rcases hx with ⟨α, hα, rfl⟩
  apply Bethe.mapsTo_kMap hlam
  exact ⟨hα.1, le_trans hα.2 (by linarith [Real.pi_pos])⟩

private theorem kMap_right_image_subset {lam : ℝ} (hlam : 0 < lam) :
    Bethe.kMap lam '' Icc 0 π ⊆ Icc (-π) π := by
  intro x hx
  rcases hx with ⟨α, hα, rfl⟩
  apply Bethe.mapsTo_kMap hlam
  exact ⟨le_trans (by linarith [Real.pi_pos]) hα.1, hα.2⟩

private theorem fourier_source_substitution_left {lam : ℝ} (hlam : 0 < lam)
    (q : ℝ → ℝ) (hq : ∀ α, q α =
      fourierEllTauCont lam (Bethe.kMap lam α) * Bethe.Xi lam α)
    (hg : IntegrableOn (fourierEllTauCont lam) (Icc (-π) π) volume)
    (hqInt : IntegrableOn q (Icc (-π) π) volume) :
    ∫ α in (-π)..0, q α = ∫ x in Bethe.kMap lam (-π)..0, fourierEllTauCont lam x := by
  have hle : (-π : ℝ) ≤ 0 := by linarith [Real.pi_pos]
  have hf : ContinuousOn (Bethe.kMap lam) (uIcc (-π) 0) :=
    (Bethe.continuous_kMap hlam).continuousOn.mono (Set.subset_univ _)
  have hff' : ∀ α ∈ Ioo (min (-π) (0 : ℝ)) (max (-π) 0),
      HasDerivWithinAt (Bethe.kMap lam) (Bethe.Xi lam α) (Ioi α) α := by
    intro α hα
    exact (Bethe.hasDerivAt_kMap hlam α).hasDerivWithinAt
  have hgcont : ContinuousOn (fourierEllTauCont lam)
      (Bethe.kMap lam '' Ioo (min (-π) (0 : ℝ)) (max (-π) 0)) := by
    intro x hx
    rcases hx with ⟨α, hα, rfl⟩
    have hαleft : α ∈ Ioo (-π) 0 := by
      simpa [min_eq_left hle, max_eq_right hle] using hα
    have hαfull : α ∈ Ioo (-π) π := by
      exact ⟨hαleft.1, lt_trans hαleft.2 Real.pi_pos⟩
    have hxIoo := kMap_mem_Ioo hlam hαfull
    have hx0 : Bethe.kMap lam α ≠ 0 := by
      intro hx0
      have hinj := (Bethe.strictMono_kMap hlam).injective
      have heq : Bethe.kMap lam α = Bethe.kMap lam 0 := by
        rw [Bethe.kMap_zero]
        exact hx0
      have hαzero := hinj heq
      exact (ne_of_lt hαleft.2) hαzero
    exact (continuousAt_fourierEllTauCont hlam hxIoo hx0).continuousWithinAt
  have hG1 : IntegrableOn (fourierEllTauCont lam)
      (Bethe.kMap lam '' uIcc (-π) 0) volume := by
    have hG1' := hg.mono_set (kMap_left_image_subset hlam)
    simpa [uIcc_of_le hle] using hG1'
  have hG2 : IntegrableOn
      (fun α => (fourierEllTauCont lam ∘ Bethe.kMap lam) α * Bethe.Xi lam α)
      (uIcc (-π) 0) volume := by
    have hIcc : IntegrableOn q (Icc (-π) 0) volume :=
      hqInt.mono_set (by
        intro α hα
        exact ⟨hα.1, le_trans hα.2 (by linarith [Real.pi_pos])⟩)
    have hEq : q = fun α =>
        (fourierEllTauCont lam ∘ Bethe.kMap lam) α * Bethe.Xi lam α := by
      funext α
      exact hq α
    simpa [hEq, uIcc_of_le hle] using hIcc
  have hsub := intervalIntegral.integral_comp_mul_deriv'''
    (a := -π) (b := 0) (f := Bethe.kMap lam) (f' := Bethe.Xi lam)
    (g := fourierEllTauCont lam) hf hff' hgcont hG1 hG2
  have hαInt : IntervalIntegrable q volume (-π) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
    exact hqInt.mono_set (by
      intro α hα
      exact ⟨le_of_lt hα.1, le_trans hα.2 (by linarith [Real.pi_pos])⟩)
  have hqToAlpha :
      ∫ α in (-π)..0, q α =
        ∫ α in (-π)..0,
          (fourierEllTauCont lam ∘ Bethe.kMap lam) α * Bethe.Xi lam α :=
    intervalIntegral.integral_congr (fun α _ => hq α)
  have hsub' :
      ∫ α in (-π)..0,
          (fourierEllTauCont lam ∘ Bethe.kMap lam) α * Bethe.Xi lam α =
        ∫ x in Bethe.kMap lam (-π)..0, fourierEllTauCont lam x := by
    simpa [Bethe.kMap_zero] using hsub
  exact hqToAlpha.trans hsub'

private theorem fourier_source_substitution_right {lam : ℝ} (hlam : 0 < lam)
    (q : ℝ → ℝ) (hq : ∀ α, q α =
      fourierEllTauCont lam (Bethe.kMap lam α) * Bethe.Xi lam α)
    (hg : IntegrableOn (fourierEllTauCont lam) (Icc (-π) π) volume)
    (hqInt : IntegrableOn q (Icc (-π) π) volume) :
    ∫ α in 0..π, q α = ∫ x in 0..Bethe.kMap lam π, fourierEllTauCont lam x := by
  have hle : (0 : ℝ) ≤ π := by linarith [Real.pi_pos]
  have hf : ContinuousOn (Bethe.kMap lam) (uIcc 0 π) :=
    (Bethe.continuous_kMap hlam).continuousOn.mono (Set.subset_univ _)
  have hff' : ∀ α ∈ Ioo (min (0 : ℝ) π) (max 0 π),
      HasDerivWithinAt (Bethe.kMap lam) (Bethe.Xi lam α) (Ioi α) α := by
    intro α hα
    exact (Bethe.hasDerivAt_kMap hlam α).hasDerivWithinAt
  have hgcont : ContinuousOn (fourierEllTauCont lam)
      (Bethe.kMap lam '' Ioo (min (0 : ℝ) π) (max 0 π)) := by
    intro x hx
    rcases hx with ⟨α, hα, rfl⟩
    have hαright : α ∈ Ioo 0 π := by
      simpa [min_eq_left hle, max_eq_right hle] using hα
    have hαfull : α ∈ Ioo (-π) π := by
      exact ⟨lt_trans (by linarith [Real.pi_pos]) hαright.1, hαright.2⟩
    have hxIoo := kMap_mem_Ioo hlam hαfull
    have hx0 : Bethe.kMap lam α ≠ 0 := by
      intro hx0
      have hinj := (Bethe.strictMono_kMap hlam).injective
      have heq : Bethe.kMap lam α = Bethe.kMap lam 0 := by
        rw [Bethe.kMap_zero]
        exact hx0
      have hαzero := hinj heq
      exact (ne_of_gt hαright.1) hαzero
    exact (continuousAt_fourierEllTauCont hlam hxIoo hx0).continuousWithinAt
  have hG1 : IntegrableOn (fourierEllTauCont lam)
      (Bethe.kMap lam '' uIcc 0 π) volume := by
    have hG1' := hg.mono_set (kMap_right_image_subset hlam)
    simpa [uIcc_of_le hle] using hG1'
  have hG2 : IntegrableOn
      (fun α => (fourierEllTauCont lam ∘ Bethe.kMap lam) α * Bethe.Xi lam α)
      (uIcc 0 π) volume := by
    have hIcc : IntegrableOn q (Icc 0 π) volume :=
      hqInt.mono_set (by
        intro α hα
        exact ⟨le_trans (by linarith [Real.pi_pos]) hα.1, hα.2⟩)
    have hEq : q = fun α =>
        (fourierEllTauCont lam ∘ Bethe.kMap lam) α * Bethe.Xi lam α := by
      funext α
      exact hq α
    simpa [hEq, uIcc_of_le hle] using hIcc
  have hsub := intervalIntegral.integral_comp_mul_deriv'''
    (a := 0) (b := π) (f := Bethe.kMap lam) (f' := Bethe.Xi lam)
    (g := fourierEllTauCont lam) hf hff' hgcont hG1 hG2
  have hαInt : IntervalIntegrable q volume 0 π := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
    exact hqInt.mono_set (by
      intro α hα
      exact ⟨le_trans (by linarith [Real.pi_pos]) (le_of_lt hα.1), hα.2⟩)
  have hqToAlpha :
      ∫ α in 0..π, q α =
        ∫ α in 0..π,
          (fourierEllTauCont lam ∘ Bethe.kMap lam) α * Bethe.Xi lam α :=
    intervalIntegral.integral_congr (fun α _ => hq α)
  have hsub' :
      ∫ α in 0..π,
          (fourierEllTauCont lam ∘ Bethe.kMap lam) α * Bethe.Xi lam α =
        ∫ x in 0..Bethe.kMap lam π, fourierEllTauCont lam x := by
    simpa [Bethe.kMap_zero] using hsub
  exact hqToAlpha.trans hsub'

/-- Change of variables from the source coordinate to α identifies the original integral
of ℓ′τ with the explicitly regularized α-integral.  The literal series values at the endpoints
are retained; replacing τ by its continuous representative changes the integrand only on a
null set. -/
theorem fourierEllPrime_tau_integral_eq_fourierPPrime {lam : ℝ} (hlam : 0 < lam) :
    ∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x =
      ∫ α in (-π)..π, fourierPPrime lam α * fourierTauSeries lam α := by
  let q : ℝ → ℝ := fun α =>
    fourierEllTauCont lam (Bethe.kMap lam α) * Bethe.Xi lam α
  have hq : ∀ α, q α =
      fourierEllTauCont lam (Bethe.kMap lam α) * Bethe.Xi lam α := by
    intro α
    rfl
  have hfInt := fourierAlphaSourceIntegrand_integrableOnIcc hlam
  have hqf : q =ᵐ[volume.restrict (Icc (-π) π)]
      (fun α => fourierPPrime lam α * Bethe.tauSeries lam α) := by
    simpa [q] using fourierAlphaSourceIntegrand_ae hlam
  have hqInt : IntegrableOn q (Icc (-π) π) volume :=
    hfInt.congr_fun_ae hqf.symm
  have hgInt := fourierEllTauCont_integrableOnIcc hlam
  have hsubL := fourier_source_substitution_left hlam q hq hgInt hqInt
  have hsubR := fourier_source_substitution_right hlam q hq hgInt hqInt
  have hqL : IntervalIntegrable q volume (-π) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
    exact hqInt.mono_set (by
      intro α hα
      exact ⟨le_of_lt hα.1, le_trans hα.2 (by linarith [Real.pi_pos])⟩)
  have hqR : IntervalIntegrable q volume 0 π := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
    exact hqInt.mono_set (by
      intro α hα
      exact ⟨le_trans (by linarith [Real.pi_pos]) (le_of_lt hα.1), hα.2⟩)
  have hgL : IntervalIntegrable (fourierEllTauCont lam) volume
      (Bethe.kMap lam (-π)) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by
      rw [Bethe.kMap_neg_pi]
      linarith [Real.pi_pos])]
    exact hgInt.mono_set (by
      intro x hx
      exact ⟨le_of_lt (by simpa only [Bethe.kMap_neg_pi] using hx.1),
        le_trans hx.2 (by linarith [Real.pi_pos])⟩)
  have hgR : IntervalIntegrable (fourierEllTauCont lam) volume
      0 (Bethe.kMap lam π) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by
      rw [Bethe.kMap_pi]
      exact Real.pi_pos.le)]
    have hsubset : Ioc 0 (Bethe.kMap lam π) ⊆ Icc (-π) π := by
      intro x hx
      constructor
      · linarith [hx.1, Real.pi_pos]
      · simpa only [Bethe.kMap_pi] using hx.2
    exact hgInt.mono_set hsubset
  have hqAlphaAE : q =ᵐ[volume.restrict (uIoc (-π) π)]
      (fun α => fourierPPrime lam α * Bethe.tauSeries lam α) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume π),
      ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hαpi hα0
    have hαIoc : α ∈ Ioc (-π) π := by
      simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
    have hαfull : α ∈ Ioo (-π) π :=
      ⟨hαIoc.1, lt_of_le_of_ne hαIoc.2 hαpi⟩
    simpa [q] using
      fourierEllTauCont_comp_mul_Xi hlam hαfull hα0
  have hqAlpha : ∫ α in (-π)..π, q α =
      ∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α :=
    intervalIntegral.integral_congr_ae_restrict hqAlphaAE
  have hgSplit := intervalIntegral.integral_add_adjacent_intervals hgL hgR
  have hqSplit := intervalIntegral.integral_add_adjacent_intervals hqL hqR
  calc
    ∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x =
        ∫ x in (-π)..π, fourierEllTauCont lam x :=
      intervalIntegral.integral_congr_ae_restrict (fourierSourceIntegrand_ae hlam)
    _ = (∫ x in Bethe.kMap lam (-π)..0, fourierEllTauCont lam x) +
        ∫ x in 0..Bethe.kMap lam π, fourierEllTauCont lam x := by
      simpa only [Bethe.kMap_neg_pi, Bethe.kMap_pi] using hgSplit.symm
    _ = (∫ α in (-π)..0, q α) + ∫ α in 0..π, q α := by
      rw [← hsubL, ← hsubR]
    _ = ∫ α in (-π)..π, q α := hqSplit
    _ = ∫ α in (-π)..π, fourierPPrime lam α * fourierTauSeries lam α := by
      simpa only [fourierTauSeries_eq_Bethe_tauSeries] using hqAlpha

/-- The source-coordinate integral is exactly the correction term in (4.3), in the
ordered-partial-sum sense.  The limit `S` is the one from the alternating tanh series. -/
theorem fourierEllPrime_tau_integral_value {lam : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      (Real.log (abs (-Real.cosh lam)) -
        (∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =
        lam + 2 * S) := by
  obtain ⟨S, hS, hCorr⟩ := fourierPPrime_tauSeries_integral hlam
  obtain ⟨S', hS', hIdentity⟩ := identity43 lam hlam
  have hSS' : S = S' := tendsto_nhds_unique hS hS'
  refine ⟨S, hS, ?_⟩
  have hSource := fourierEllPrime_tau_integral_eq_fourierPPrime hlam
  have hlog : Real.log (abs (-Real.cosh lam)) = Real.log (Real.cosh lam) := by
    rw [abs_neg, abs_of_pos (Real.cosh_pos lam)]
  rw [hSource, hlog]
  have hLocalInt :
      ∫ α in (-π)..π, fourierPPrime lam α * fourierTauSeries lam α =
        ∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α := by
    apply intervalIntegral.integral_congr
    intro α hα
    change fourierPPrime lam α * fourierTauSeries lam α =
      fourierPPrime lam α * Bethe.tauSeries lam α
    rw [fourierTauSeries_eq_Bethe_tauSeries]
  rw [hLocalInt]
  have hLeft : Tendsto
      (fun N => Real.log (Real.cosh lam) - logCoshTauCorrectionPartial lam N)
      atTop (𝓝 (Real.log (Real.cosh lam) -
        ∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α)) :=
    tendsto_const_nhds.sub hCorr
  have hRight : Tendsto
      (fun N => Real.log (Real.cosh lam) - logCoshTauCorrectionPartial lam N)
      atTop (𝓝 (lam + 2 * S')) := hIdentity
  have hEq := tendsto_nhds_unique hLeft hRight
  rw [← hSS'] at hEq
  linarith

/-- The analytic exponent in the eigenvalue-ratio formula, with the source parameter
`Δ = -cosh λ` and positive real mode `r`. -/
theorem fourierRatioExponent {lam r : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      -r * Real.log (abs (-Real.cosh lam)) +
          r * (∫ x in (-π)..π,
            fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =
        -r * (lam + 2 * S) := by
  obtain ⟨S, hS, hvalue⟩ := fourierEllPrime_tau_integral_value hlam
  refine ⟨S, hS, ?_⟩
  calc
    -r * Real.log (abs (-Real.cosh lam)) +
        r * (∫ x in (-π)..π,
          fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =
        -r * (Real.log (abs (-Real.cosh lam)) -
          ∫ x in (-π)..π,
            fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) := by ring
    _ = -r * (lam + 2 * S) := by rw [hvalue]

/-- Exponentiating the ratio identity gives the corresponding `|Δ|^(-r)` form. -/
theorem fourierRatioExponent_exp {lam r : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Real.rpow (abs (-Real.cosh lam)) (-r) *
          Real.exp (r * (∫ x in (-π)..π,
            fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x)) =
        Real.exp (-r * (lam + 2 * S)) := by
  obtain ⟨S, hS, hExponent⟩ := fourierRatioExponent hlam
  have hDeltaPos : 0 < abs (-Real.cosh lam) :=
    abs_pos.mpr (neg_ne_zero.mpr (Real.cosh_pos lam).ne')
  refine ⟨S, hS, ?_⟩
  calc
    Real.rpow (abs (-Real.cosh lam)) (-r) *
        Real.exp (r * (∫ x in (-π)..π,
          fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x)) =
        Real.exp ((-r) * Real.log (abs (-Real.cosh lam))) *
          Real.exp (r * (∫ x in (-π)..π,
            fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x)) := by
              have hpow : Real.rpow (abs (-Real.cosh lam)) (-r) =
                  Real.exp ((-r) * Real.log (abs (-Real.cosh lam))) := by
                calc
                  Real.rpow (abs (-Real.cosh lam)) (-r) =
                      Real.exp (Real.log (abs (-Real.cosh lam)) * (-r)) :=
                    Real.rpow_def_of_pos hDeltaPos (-r)
                  _ = Real.exp ((-r) * Real.log (abs (-Real.cosh lam))) := by
                    congr 1
                    ring
              rw [hpow]
    _ = Real.exp (-r * Real.log (abs (-Real.cosh lam)) +
          r * (∫ x in (-π)..π,
            fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x)) := by
          rw [← Real.exp_add]
    _ = Real.exp (-r * (lam + 2 * S)) := by rw [hExponent]

end PottsDiscontinuity
