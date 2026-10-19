module

public import Mathlib

/-!
# The hyperbolic secant: Fourier transform and Poisson summation

Source: arXiv:1611.09877v2, §4 (Fourier computations), the identity
`1 / cosh(λ m) = (1 / (2 λ)) ∫_ℝ e^{-i m α} / cosh(π α / (2 λ)) dα` and the periodisation
`R(α) = (π / (2 λ)) ∑_{j ∈ ℤ} 1 / cosh(π (2 π j + α) / (2 λ))` of `\hat R(m) = 1 / (2 cosh(λ m))`.

The paper obtains the sech transform from the residue theorem.  Here it is obtained from the Beta
integral: for `s = (1 - i ω) / 2`, `B(s, 1 - s) = Γ(s) Γ(1 - s) = π / sin (π s) = π / cosh (π ω / 2)`
(Mathlib: `Complex.Gamma_mul_Gamma_eq_betaIntegral`, `Complex.Gamma_mul_Gamma_one_sub`), and the
substitution `x = 1 / (1 + e^{-2 t})` turns the Beta integral into `∫_ℝ e^{-i ω t} / cosh t dt`.

* `integral_cexp_div_cosh`, `integral_cos_div_cosh`: `∫_ℝ cos(ω t) / cosh t dt = π / cosh(π ω / 2)`;
* `summable_sech_periodic`;
* `periodic_sech_eq_cos_series`: Poisson summation (Mathlib's
  `Real.tsum_eq_tsum_fourier_of_rpow_decay`) gives
  `(π / (2 λ)) ∑_{j ∈ ℤ} 1 / cosh (π (2 π j + α) / (2 λ)) = 1 / 2 + ∑_{n ≥ 1} cos (n α) / cosh (λ n)`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set

namespace PottsDiscontinuity.Bethe

theorem cosh_ge_quarter (t : ℝ) : (1 + t ^ 2) / 4 ≤ Real.cosh t := by
  have h1 : Real.cosh t = Real.cosh |t| := (Real.cosh_abs t).symm
  have h2 := Real.quadratic_le_exp_of_nonneg (abs_nonneg t)
  have h3 : 0 < Real.exp (-|t|) := Real.exp_pos _
  have h4 : Real.cosh |t| = (Real.exp |t| + Real.exp (-|t|)) / 2 := Real.cosh_eq _
  rw [h1, h4]
  have h5 : |t| ^ 2 = t ^ 2 := sq_abs t
  nlinarith [abs_nonneg t, sq_nonneg (|t| - 1)]

theorem continuous_inv_cosh_mul (k : ℝ) : Continuous (fun t : ℝ => 1 / Real.cosh (k * t)) :=
  continuous_const.div (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
    fun _ => (Real.cosh_pos _).ne'

theorem one_div_cosh_le (t : ℝ) : 1 / Real.cosh t ≤ 4 * (1 + t ^ 2)⁻¹ := by
  have h := cosh_ge_quarter t
  have hp : 0 < (1 + t ^ 2) / 4 := by positivity
  calc 1 / Real.cosh t ≤ 1 / ((1 + t ^ 2) / 4) := one_div_le_one_div_of_le hp h
    _ = 4 * (1 + t ^ 2)⁻¹ := by field_simp

theorem integrable_inv_cosh : Integrable (fun t : ℝ => 1 / Real.cosh t) := by
  have h := (integrable_inv_one_add_sq).const_mul 4
  refine h.mono' (by simpa using (continuous_inv_cosh_mul 1).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_of_pos (by positivity [Real.cosh_pos t])]
  exact one_div_cosh_le t

/-- The logistic map `σ(t) = 1 / (1 + e^{-2t})`, a smooth increasing bijection `ℝ → (0,1)`. -/
noncomputable def logistic2 (t : ℝ) : ℝ := (1 + Real.exp (-2 * t))⁻¹

theorem logistic2_pos (t : ℝ) : 0 < logistic2 t := by
  unfold logistic2; positivity

theorem logistic2_lt_one (t : ℝ) : logistic2 t < 1 := by
  unfold logistic2
  have := Real.exp_pos (-2 * t)
  rw [inv_lt_one₀ (by positivity)]
  linarith

theorem hasDerivAt_logistic2 (t : ℝ) :
    HasDerivAt logistic2 (2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => -2 * t) (-2) t := by
    simpa using (hasDerivAt_id t).const_mul (-2 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => 1 + Real.exp (-2 * t)) (Real.exp (-2 * t) * (-2)) t := by
    simpa using (h1.exp).const_add 1
  have h3 := h2.inv (by positivity)
  have e : logistic2 = (fun t : ℝ => 1 + Real.exp (-2 * t))⁻¹ := by funext t; rfl
  rw [e]
  exact h3.congr_deriv (by ring)

theorem strictMono_logistic2 : StrictMono logistic2 := by
  refine strictMono_of_hasDerivAt_pos hasDerivAt_logistic2 fun t => ?_
  positivity

theorem image_logistic2 : logistic2 '' (univ : Set ℝ) = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩
    exact ⟨logistic2_pos t, logistic2_lt_one t⟩
  · rintro ⟨h0, h1⟩
    refine ⟨Real.log ((1 - x) / x) / (-2), mem_univ _, ?_⟩
    unfold logistic2
    have hq : 0 < (1 - x) / x := div_pos (by linarith) h0
    have : -2 * (Real.log ((1 - x) / x) / (-2)) = Real.log ((1 - x) / x) := by field_simp
    rw [this, Real.exp_log hq]
    field_simp
    ring

theorem cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (y : ℂ) :
    ((x : ℂ)) ^ y = Complex.exp (Real.log x * y) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]

theorem logistic2_integrand (ω t : ℝ) :
    ((2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2 : ℝ) : ℂ) *
      (((logistic2 t : ℝ) : ℂ) ^ ((1 - Complex.I * ω) / 2 - 1) *
        (1 - ((logistic2 t : ℝ) : ℂ)) ^ ((1 - (1 - Complex.I * ω) / 2) - 1)) =
      Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  set a : ℝ := 1 + Real.exp (-2 * t) with ha
  have ha0 : 0 < a := by positivity
  have hea : 0 < Real.exp (-2 * t) := Real.exp_pos _
  have hσ : logistic2 t = a⁻¹ := rfl
  have h1σ : 1 - logistic2 t = Real.exp (-2 * t) * a⁻¹ := by
    rw [hσ, ha]; field_simp; ring
  have hpos1 : 0 < logistic2 t := logistic2_pos t
  have hpos2 : 0 < 1 - logistic2 t := by have := logistic2_lt_one t; linarith
  have e1 : (1 - ((logistic2 t : ℝ) : ℂ)) = (((1 - logistic2 t : ℝ)) : ℂ) := by push_cast; ring
  rw [e1, cpow_ofReal_pos hpos1, cpow_ofReal_pos hpos2, ← Complex.exp_add]
  have hl1 : Real.log (logistic2 t) = -Real.log a := by rw [hσ, Real.log_inv]
  have hl2 : Real.log (1 - logistic2 t) = -2 * t - Real.log a := by
    rw [h1σ, Real.log_mul hea.ne' (inv_ne_zero ha0.ne'), Real.log_exp, Real.log_inv]; ring
  rw [hl1, hl2]
  have hexp : Complex.exp (((-Real.log a : ℝ) : ℂ) * (s - 1) + ((-2 * t - Real.log a : ℝ) : ℂ) *
      (1 - s - 1)) = (a : ℂ) * Complex.exp (2 * t * s) := by
    have : ((-Real.log a : ℝ) : ℂ) * (s - 1) + ((-2 * t - Real.log a : ℝ) : ℂ) * (1 - s - 1) =
        (Real.log a : ℂ) + 2 * t * s := by push_cast; ring
    rw [this, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ha0]
  rw [hexp]
  have hX : Complex.exp t ≠ 0 := Complex.exp_ne_zero t
  have hY : Complex.exp (-(Complex.I * ω * t)) ≠ 0 := Complex.exp_ne_zero _
  have e2' : Complex.exp (-2 * (t : ℂ)) = (Complex.exp t)⁻¹ ^ 2 := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have e3 : Complex.exp (2 * t * s) = Complex.exp t * Complex.exp (-(Complex.I * ω * t)) := by
    rw [← Complex.exp_add]; congr 1; rw [hs]; ring
  have e4 : (Real.cosh t : ℂ) = (Complex.exp t + (Complex.exp t)⁻¹) / 2 := by
    rw [Complex.ofReal_cosh, Complex.cosh, Complex.exp_neg]
  have e5 : (a : ℂ) = 1 + (Complex.exp t)⁻¹ ^ 2 := by rw [ha]; push_cast; rw [e2']
  have e6 : (((2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2 : ℝ)) : ℂ) =
      2 * (Complex.exp t)⁻¹ ^ 2 / (1 + (Complex.exp t)⁻¹ ^ 2) ^ 2 := by
    push_cast; rw [e2']
  have hc : ((Real.cosh t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos t).ne'
  have hne : 1 + (Complex.exp t)⁻¹ ^ 2 ≠ 0 := by
    rw [← e5]; exact_mod_cast ha0.ne'
  rw [e4] at hc
  have hne2 : Complex.exp t + (Complex.exp t)⁻¹ ≠ 0 := by
    intro h; apply hc; rw [h]; simp
  rw [e6, e3, e5, e4]
  field_simp

theorem betaIntegral_eq_integral_cexp_div_cosh (ω : ℝ) :
    Complex.betaIntegral ((1 - Complex.I * ω) / 2) (1 - (1 - Complex.I * ω) / 2) =
      ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) * (1 - (x : ℂ)) ^ ((1 - s) - 1) with hg
  have h1 : ∫ x in (0:ℝ)..1, g x = ∫ x in Ioo (0:ℝ) 1, g x := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have h2 : ∫ x in logistic2 '' (univ : Set ℝ), g x =
      ∫ t in (univ : Set ℝ), |2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2| • g (logistic2 t) :=
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun t _ => (hasDerivAt_logistic2 t).hasDerivWithinAt)
      strictMono_logistic2.injective.injOn g
  rw [image_logistic2] at h2
  have h3 : ∀ t : ℝ, |2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2| • g (logistic2 t) =
      Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by
    intro t
    rw [abs_of_pos (by positivity), Complex.real_smul, hg]
    exact logistic2_integrand ω t
  simp_rw [h3] at h2
  unfold Complex.betaIntegral
  rw [h1, h2, setIntegral_univ]

theorem integral_cexp_div_cosh (ω : ℝ) :
    ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) =
      ((π / Real.cosh (π * ω / 2) : ℝ) : ℂ) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  have hsre : 0 < s.re := by simp [hs]
  have hs1re : 0 < (1 - s).re := by simp [hs]; norm_num
  rw [← betaIntegral_eq_integral_cexp_div_cosh]
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral hsre hs1re
  rw [show s + (1 - s) = 1 by ring, Complex.Gamma_one, one_mul,
    Complex.Gamma_mul_Gamma_one_sub] at h
  rw [← h]
  have hsin : Complex.sin (π * s) = (Real.cosh (π * ω / 2) : ℂ) := by
    have : (π : ℂ) * s = (π : ℂ) / 2 - ((π * ω / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hs]; push_cast; ring
    rw [this, Complex.sin_pi_div_two_sub, Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [hsin]
  push_cast
  ring

theorem continuous_cexp_div_cosh (ω : ℝ) :
    Continuous (fun t : ℝ => Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ)) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun t => ?_
  exact_mod_cast (Real.cosh_pos t).ne'

theorem integrable_cexp_div_cosh (ω : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ)) := by
  refine integrable_inv_cosh.mono' (continuous_cexp_div_cosh ω).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.cosh_pos t).le]
  have : ‖Complex.exp (-(Complex.I * ω * t))‖ = 1 := by
    rw [show -(Complex.I * ω * t) = ((-(ω * t) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [this]

theorem re_cexp_div_cosh (ω t : ℝ) :
    (Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ)).re = Real.cos (ω * t) / Real.cosh t := by
  rw [Complex.div_ofReal_re,
    show -(Complex.I * ω * t) = ((-(ω * t) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- The Fourier transform of the hyperbolic secant:
`∫_ℝ cos(ω t) / cosh t dt = π / cosh(π ω / 2)`. -/
theorem integral_cos_div_cosh (ω : ℝ) :
    ∫ t : ℝ, Real.cos (ω * t) / Real.cosh t = π / Real.cosh (π * ω / 2) := by
  have h := congrArg Complex.re (integral_cexp_div_cosh ω)
  have h2 : ∫ t : ℝ, (Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ)).re =
      (∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ)).re := by
    simpa using integral_re (integrable_cexp_div_cosh ω)
  simp_rw [re_cexp_div_cosh] at h2
  rw [h2, h, Complex.ofReal_re]


/-! ### Fourier transform of a rescaled secant -/

open scoped FourierTransform

/-- The (unitary, `e^{-2πi x ξ}`) Fourier transform of `y ↦ c / cosh (b y)` is
`ξ ↦ (c / b) · π / cosh (π² ξ / b)`. -/
theorem fourier_sech (b : ℝ) (hb : 0 < b) (c ξ : ℝ) :
    𝓕 (fun y : ℝ => ((c / Real.cosh (b * y) : ℝ) : ℂ)) ξ =
      (((c / b) * (π / Real.cosh (π ^ 2 * ξ / b)) : ℝ) : ℂ) := by
  rw [fourier_real_eq_integral_exp_smul]
  set ω : ℝ := 2 * π * ξ / b with hω
  have h1 : ∀ v : ℝ, Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I) •
      ((c / Real.cosh (b * v) : ℝ) : ℂ) =
      (c : ℂ) * (fun t : ℝ => Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ)) (b * v) := by
    intro v
    simp only [smul_eq_mul]
    have : (((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I) = -(Complex.I * ω * ((b * v : ℝ) : ℂ)) := by
      have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
      rw [hω]; push_cast; field_simp
    rw [this]; push_cast; ring
  simp_rw [h1]
  have key := Measure.integral_comp_mul_left
    (fun t : ℝ => Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ)) b
  beta_reduce at key
  rw [integral_const_mul, key, integral_cexp_div_cosh ω]
  have hπ : π * ω / 2 = π ^ 2 * ξ / b := by rw [hω]; field_simp
  rw [hπ]
  rw [abs_of_pos (inv_pos.mpr hb), Complex.real_smul]
  push_cast
  ring


/-! ### Decay -/

theorem isBigO_cocompact_sech {k : ℝ} (hk : 0 < k) (C : ℝ) :
    (fun y : ℝ => ((C / Real.cosh (k * y) : ℝ) : ℂ)) =O[cocompact ℝ]
      (fun y : ℝ => |y| ^ (-(2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (4 * |C| / k ^ 2) ?_
  filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_gt_atTop 0] with y hy
  have hy0 : 0 < |y| := by simpa using hy
  have hyne : y ≠ 0 := abs_pos.mp hy0
  have hy2 : 0 < y ^ 2 := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg hy0.le, Real.rpow_two, sq_abs,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy2), abs_div,
    abs_of_pos (Real.cosh_pos _)]
  have h1 := one_div_cosh_le (k * y)
  have h2 : (1 + (k * y) ^ 2)⁻¹ ≤ (k ^ 2 * y ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    rw [mul_pow]; linarith
  calc |C| / Real.cosh (k * y) = |C| * (1 / Real.cosh (k * y)) := by ring
    _ ≤ |C| * (4 * (k ^ 2 * y ^ 2)⁻¹) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = 4 * |C| / k ^ 2 * (y ^ 2)⁻¹ := by field_simp


theorem isBigO_cocompact_sech_real {k : ℝ} (hk : 0 < k) (C : ℝ) :
    (fun y : ℝ => C / Real.cosh (k * y)) =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-(2 : ℝ))) := by
  have := isBigO_cocompact_sech hk C
  exact Complex.isBigO_ofReal_left.mp this

/-- The terms `1 / cosh (π (2 π j + α) / (2 λ))` are summable over `j ∈ ℤ`. -/
theorem summable_sech_periodic {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Summable (fun j : ℤ => 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) := by
  have hk : 0 < π ^ 2 / lam := by positivity
  set a : ℝ := α / (2 * π) with ha
  have hpi := Real.pi_pos
  have hb := isBigO_cocompact_sech_real hk 1
  have hT : Tendsto (fun n : ℤ => a + (n : ℝ)) cofinite (cocompact ℝ) :=
    (Homeomorph.addLeft a).isClosedEmbedding.tendsto_cocompact.comp Int.tendsto_coe_cofinite
  have hg : Summable (fun n : ℤ => |a + (n : ℝ)| ^ (-(2 : ℝ))) := by
    have := (Real.summable_one_div_int_add_rpow a 2).2 one_lt_two
    refine this.congr fun n => ?_
    rw [Real.rpow_neg (abs_nonneg _), add_comm, one_div]
  refine summable_of_isBigO hg ?_
  have := hb.comp_tendsto hT
  refine this.congr_left fun n => ?_
  simp only [Function.comp_apply]
  congr 2
  rw [ha]
  field_simp
  ring


/-! ### Poisson summation -/

theorem summable_inv_cosh_int {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    Summable (fun n : ℤ => C / Real.cosh (lam * (n : ℝ))) := by
  have hb := isBigO_cocompact_sech_real hlam C
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    (hb.comp_tendsto Int.tendsto_coe_cofinite)

theorem fourier_sech_periodic_aux {lam : ℝ} (hlam : 0 < lam) (ξ : ℝ) :
    𝓕 (fun y : ℝ => ((π / (2 * lam) / Real.cosh (π ^ 2 / lam * y) : ℝ) : ℂ)) ξ =
      (((1 / 2) / Real.cosh (lam * ξ) : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  rw [fourier_sech (π ^ 2 / lam) (by positivity)]
  congr 1
  have : π ^ 2 * ξ / (π ^ 2 / lam) = lam * ξ := by field_simp
  rw [this]
  field_simp


/-- Poisson summation for the hyperbolic secant:
`(π / (2 λ)) ∑_{j ∈ ℤ} 1 / cosh (π (2 π j + α) / (2 λ)) = 1 / 2 + ∑_{n ≥ 1} cos (n α) / cosh (λ n)`. -/
theorem periodic_sech_eq_cos_series {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    HasSum (fun n : ℕ => Real.cos (((n + 1 : ℕ) : ℝ) * α) / Real.cosh (lam * ((n + 1 : ℕ) : ℝ)))
      ((π / (2 * lam)) * (∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) - 1 / 2) := by
  have hpi := Real.pi_pos
  have hb : 0 < π ^ 2 / lam := by positivity
  set b : ℝ := π ^ 2 / lam with hbdef
  set c : ℝ := π / (2 * lam) with hcdef
  set f : ℝ → ℂ := fun y => ((c / Real.cosh (b * y) : ℝ) : ℂ) with hfdef
  have hc : Continuous f := by
    refine Complex.continuous_ofReal.comp ?_
    exact continuous_const.div (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
      fun y => (Real.cosh_pos _).ne'
  have hf : f =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-(2 : ℝ))) := isBigO_cocompact_sech hb c
  have hF : 𝓕 f = fun ξ => (((1 / 2) / Real.cosh (lam * ξ) : ℝ) : ℂ) := by
    funext ξ
    exact fourier_sech_periodic_aux hlam ξ
  have hFf : 𝓕 f =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-(2 : ℝ))) := by
    rw [hF]; exact isBigO_cocompact_sech hlam (1 / 2)
  set x : ℝ := α / (2 * π) with hx
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay hc one_lt_two hf hFf x
  -- left side
  have hL : ∑' n : ℤ, f (x + n) =
      ((c * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam)) : ℝ) : ℂ) := by
    rw [← tsum_mul_left, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    simp only [hfdef]
    have : b * (x + (n : ℝ)) = π * (2 * π * n + α) / (2 * lam) := by
      rw [hbdef, hx]; field_simp; ring
    rw [this, mul_one_div]
  -- right side: real parts
  have hterm : ∀ n : ℤ, (𝓕 f n * fourier n (x : UnitAddCircle)).re =
      (1 / 2) / Real.cosh (lam * n) * Real.cos (n * α) := by
    intro n
    rw [congrFun hF (n : ℝ)]
    have : fourier n (x : UnitAddCircle) = Complex.exp (((n * α : ℝ) : ℂ) * Complex.I) := by
      rw [fourier_coe_apply]
      congr 1
      rw [hx]; push_cast
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
      field_simp
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  set F : ℤ → ℝ := fun n => (1 / 2) / Real.cosh (lam * n) * Real.cos (n * α) with hFdef
  have hsumF : Summable F := by
    refine Summable.of_norm_bounded (summable_inv_cosh_int hlam (1 / 2)) fun n => ?_
    rw [hFdef]
    simp only [norm_mul, Real.norm_eq_abs]
    have h1 : |(1 / 2) / Real.cosh (lam * n)| = (1 / 2) / Real.cosh (lam * n) :=
      abs_of_pos (by have := Real.cosh_pos (lam * n); positivity)
    rw [h1]
    calc (1 / 2) / Real.cosh (lam * n) * |Real.cos (n * α)|
        ≤ (1 / 2) / Real.cosh (lam * n) * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ = _ := mul_one _
  have hsumC : Summable (fun n : ℤ => 𝓕 f n * fourier n (x : UnitAddCircle)) := by
    refine Summable.of_norm_bounded (summable_inv_cosh_int hlam (1 / 2)) fun n => ?_
    rw [norm_mul, congrFun hF (n : ℝ), Complex.norm_real, Real.norm_eq_abs]
    have : ‖fourier n (x : UnitAddCircle)‖ = 1 := by
      rw [fourier_apply]; exact Circle.norm_coe _
    rw [this, mul_one, abs_of_pos (by have := Real.cosh_pos (lam * n); positivity)]
  have hRe := congrArg Complex.re hP
  rw [hL, Complex.ofReal_re, Complex.re_tsum hsumC] at hRe
  simp_rw [hterm] at hRe
  have hHas : HasSum F (c * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) := by
    rw [hRe]; exact hsumF.hasSum
  have h1 := hHas.nat_add_neg
  have h2 := (hasSum_nat_add_iff' 1).mpr h1
  convert h2 using 1
  · funext n
    simp only [hFdef]
    push_cast
    rw [mul_neg, Real.cosh_neg, neg_mul, Real.cos_neg]
    ring
  · simp [hFdef]

end PottsDiscontinuity.Bethe
