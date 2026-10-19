module

public import Mathlib
public import PottsDiscontinuity.Bethe.Prop21Defs
public import PottsDiscontinuity.Bethe.FourierTrig
public import PottsDiscontinuity.Bethe.FourierSech

/-!
# Proposition 2.1 for `ρ`: the explicit solution of (cBE_Δ) and its uniqueness

Source: arXiv:1611.09877v2, Proposition 2.1 and its proof (§2.1), with the Fourier computations of
§4 (`R̂(m) = 1/(2 cosh(λ m))`).

* `Rsech lam α = (π/(2λ)) ∑_{j∈ℤ} 1/cosh(π(2πj+α)/(2λ))` is `R = 2πρ(k)k'`;
* `rho Δ x`: the explicit density of (2.1) (`x = k(α)`, `α = kInv x`);
* `Rsech_add_xiConv`: `R + (1/2π) Ξ_{2λ} * R = Ξ_λ` (existence half: the hyperbolic-secant
  transform / Poisson summation gives the cosine series of `R` with coefficients `1/cosh(λ m)`);
* `rho_isCBESolution`: `ρ` solves (cBE_Δ) at every `x ∈ [-π, π]`;
* `eq_rho_of_isCBESolution_of_integrableOn`, `eq_rho_of_isCBESolution`: every integrable
  (in particular every `L²`) solution of (cBE_Δ) equals `ρ` on `[-π, π]` (uniqueness half: the
  positive definiteness of the Poisson kernel replaces the division by `1 + Ξ̂_{2λ}(m)`).
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- The periodised hyperbolic secant `R(α) = (π/(2λ)) ∑_{j∈ℤ} 1/cosh(π(2πj+α)/(2λ))`
(the function `𝓡` of §4, equal to `2π ρ(k(α)) k'(α)`). -/
noncomputable def Rsech (lam α : ℝ) : ℝ :=
  (π / (2 * lam)) * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))

/-- The cosine-coefficient sequence `1/cosh(λ m)`, `m = n + 1`. -/
noncomputable def secCoeff (lam : ℝ) (n : ℕ) : ℝ := 1 / Real.cosh (lam * ((n + 1 : ℕ) : ℝ))

theorem secCoeff_pos (lam : ℝ) (n : ℕ) : 0 < secCoeff lam n := by
  unfold secCoeff; positivity

theorem secCoeff_le {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    secCoeff lam n ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
  unfold secCoeff
  have hx : 0 ≤ lam * ((n + 1 : ℕ) : ℝ) := by positivity
  have h1 : Real.exp (lam * ((n + 1 : ℕ) : ℝ)) ≤ 2 * Real.cosh (lam * ((n + 1 : ℕ) : ℝ)) := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-(lam * ((n + 1 : ℕ) : ℝ)))
    linarith
  have h2 : Real.exp (-lam) ^ (n + 1) = Real.exp (-(lam * ((n + 1 : ℕ) : ℝ))) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h2, one_div, Real.exp_neg]
  have hc : 0 < Real.cosh (lam * ((n + 1 : ℕ) : ℝ)) := Real.cosh_pos _
  have he : 0 < Real.exp (lam * ((n + 1 : ℕ) : ℝ)) := Real.exp_pos _
  rw [inv_eq_one_div, div_le_iff₀ hc]
  rw [show 2 * (Real.exp (lam * ((n + 1 : ℕ) : ℝ)))⁻¹ * Real.cosh (lam * ((n + 1 : ℕ) : ℝ)) =
    2 * Real.cosh (lam * ((n + 1 : ℕ) : ℝ)) / Real.exp (lam * ((n + 1 : ℕ) : ℝ)) by ring]
  rw [le_div_iff₀ he]
  linarith

theorem summable_secCoeff {lam : ℝ} (hlam : 0 < lam) : Summable (secCoeff lam) := by
  have hr : 0 < Real.exp (-lam) := Real.exp_pos _
  have hr1 : Real.exp (-lam) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hs : Summable (fun n : ℕ => 2 * Real.exp (-lam) ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-lam))
    exact this.congr fun n => by ring
  exact Summable.of_nonneg_of_le (fun n => (secCoeff_pos lam n).le) (secCoeff_le hlam) hs

theorem Rsech_eq_trigSeries {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Rsech lam α = trigSeries (1 / 2) (secCoeff lam) (fun _ => 0) α := by
  have h := (periodic_sech_eq_cos_series hlam α).tsum_eq
  unfold trigSeries Rsech
  have : ∀ n : ℕ, secCoeff lam n * Real.cos (((n + 1 : ℕ) : ℝ) * α) + 0 * Real.sin (((n + 1 : ℕ) : ℝ) * α) =
      Real.cos (((n + 1 : ℕ) : ℝ) * α) / Real.cosh (lam * ((n + 1 : ℕ) : ℝ)) := by
    intro n; unfold secCoeff; ring
  simp_rw [this]
  linarith


theorem one_add_exp_two_mul_div_cosh {lam : ℝ} (n : ℕ) :
    (1 + Real.exp (-(2 * lam)) ^ (n + 1)) * secCoeff lam n = 2 * Real.exp (-lam) ^ (n + 1) := by
  unfold secCoeff
  set q : ℝ := Real.exp (-lam) ^ (n + 1) with hq
  have hq0 : 0 < q := by positivity
  have h1 : Real.exp (-(2 * lam)) ^ (n + 1) = q ^ 2 := by
    have e : Real.exp (-(2 * lam)) = Real.exp (-lam) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hq, e, ← pow_mul, mul_comm 2 (n + 1), pow_mul]
  have h2 : Real.exp (-(lam * ((n + 1 : ℕ) : ℝ))) = q := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Real.cosh (lam * ((n + 1 : ℕ) : ℝ)) = (q⁻¹ + q) / 2 := by
    have e : Real.exp (lam * ((n + 1 : ℕ) : ℝ)) = q⁻¹ := by
      rw [← h2, Real.exp_neg, inv_inv]
    rw [Real.cosh_eq, h2, e]
  rw [h1, h3]
  field_simp


/-- The key identity of the existence half for `ρ`:
`R + (1/2π) Ξ_{2λ} * R = Ξ_λ` for the periodised sech `R` (equation (cBE') of the source). -/
theorem Rsech_add_xiConv {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Rsech lam α + xiConv (2 * lam) (Rsech lam) α = Xi lam α := by
  have hlam2 : 0 < 2 * lam := by linarith
  have hr : 0 < Real.exp (-(2 * lam)) := Real.exp_pos _
  have hr1 : Real.exp (-(2 * lam)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hc := summable_secCoeff hlam
  have hz : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  have hRfun : Rsech lam = trigSeries (1 / 2) (secCoeff lam) (fun _ => 0) :=
    funext (Rsech_eq_trigSeries hlam)
  have hX : xiConv (2 * lam) (Rsech lam) α =
      trigSeries (1 / 2) (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * secCoeff lam n)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0) α := by
    rw [hRfun]; exact xiConv_trigSeries hlam2 hc hz (1 / 2) α
  have hc2 : Summable (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * secCoeff lam n) :=
    summable_pow_succ_mul hc hr.le hr1.le
  have hz2 : Summable (fun n : ℕ => Real.exp (-(2 * lam)) ^ (n + 1) * 0) := by simp
  have h1 := (hasSum_trigTerm hc hz α)
  have h2 := (hasSum_trigTerm hc2 hz2 α)
  have h3 := h1.add h2
  have h4 := hasSum_Xi_cos hlam α
  have e1 : Rsech lam α = 1 / 2 + ∑' n, trigTerm (secCoeff lam) (fun _ => 0) n α := by
    rw [Rsech_eq_trigSeries hlam]; rfl
  have e2 : xiConv (2 * lam) (Rsech lam) α = 1 / 2 +
      ∑' n, trigTerm (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * secCoeff lam n)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0) n α := by
    rw [hX]; rfl
  have h5 : (fun n => trigTerm (secCoeff lam) (fun _ => 0) n α +
      trigTerm (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * secCoeff lam n)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0) n α) =
      fun n : ℕ => 2 * Real.exp (-lam) ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * α) := by
    funext n
    unfold trigTerm
    rw [← one_add_exp_two_mul_div_cosh (lam := lam) n]
    ring
  rw [h5] at h3
  have h6 := h3.unique h4
  rw [e1, e2]
  linarith


/-! ### The explicit density `ρ_Δ` of (2.1) -/

/-- The explicit solution of (cBE_Δ) given by (2.1): for `x = k(α)`,
`ρ(x) = (1/(4 λ k'(α))) ∑_{j∈ℤ} 1/cosh(π(2πj+α)/(2λ))`, with `λ = λ(Δ)` and `α = k^{-1}(x)`. -/
noncomputable def rho (Δ x : ℝ) : ℝ :=
  1 / (4 * lamOf Δ * deriv (kMap (lamOf Δ)) (kInv (lamOf Δ) x)) *
    ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + kInv (lamOf Δ) x) / (2 * lamOf Δ))

theorem rho_eq {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) :
    rho Δ x = Rsech (lamOf Δ) (kInv (lamOf Δ) x) / (2 * π * Xi (lamOf Δ) (kInv (lamOf Δ) x)) := by
  have hlam := lamOf_pos hΔ
  have hpi := Real.pi_pos
  have hX := Xi_pos hlam (kInv (lamOf Δ) x)
  unfold rho Rsech
  rw [deriv_kMap hlam]
  generalize (∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + kInv (lamOf Δ) x) / (2 * lamOf Δ))) = S
  field_simp
  ring

theorem Rtrans_rho {Δ : ℝ} (hΔ : Δ < -1) (α : ℝ) :
    Rtrans Δ (rho Δ) α = Rsech (lamOf Δ) α := by
  have hlam := lamOf_pos hΔ
  have hpi := Real.pi_pos
  have hX := Xi_pos hlam α
  rw [Rtrans_eq hΔ, rho_eq hΔ, kInv_kMap hlam]
  field_simp

/-- **Proposition 2.1, existence for `ρ`**: the explicit `ρ` of (2.1) solves (cBE_Δ) for every
`x ∈ [-π, π]`. -/
theorem rho_isCBESolution {Δ : ℝ} (hΔ : Δ < -1) : IsCBESolution Δ (rho Δ) := by
  rw [isCBESolution_iff hΔ]
  intro α _
  have hR : Rtrans Δ (rho Δ) = Rsech (lamOf Δ) := funext (Rtrans_rho hΔ)
  rw [hR]
  exact Rsech_add_xiConv (lamOf_pos hΔ) α


/-! ### Uniqueness: transfer between the variables `x` and `α` -/

theorem integrableOn_Xi_mul_comp {lam : ℝ} (hlam : 0 < lam) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (-π) π) volume) :
    IntegrableOn (fun β => Xi lam β * f (kMap lam β)) (Icc (-π) π) volume := by
  have himg : kMap lam '' Icc (-π) π = Icc (-π) π := (bijOn_kMap hlam).image_eq
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Icc (-π) π) (f := kMap lam)
    (f' := Xi lam) measurableSet_Icc (fun x _ => (hasDerivAt_kMap hlam x).hasDerivWithinAt)
    (strictMono_kMap hlam).injective.injOn f).1 (by rwa [himg])
  refine h.congr_fun (fun β _ => ?_) measurableSet_Icc
  simp only [smul_eq_mul]
  rw [abs_of_pos (Xi_pos hlam β)]

theorem integrableOn_comp_kMap_of_Xi {lam : ℝ} (hlam : 0 < lam) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (-π) π) volume) :
    IntegrableOn (fun β => f (kMap lam β)) (Icc (-π) π) volume := by
  have h := integrableOn_Xi_mul_comp hlam hf
  have hc : ContinuousOn (fun β => (Xi lam β)⁻¹) (Icc (-π) π) :=
    ((continuous_Xi (μ := lam) hlam).inv₀ (fun β => (Xi_pos hlam β).ne')).continuousOn
  have := h.mul_continuousOn hc isCompact_Icc
  refine this.congr_fun (fun β _ => ?_) measurableSet_Icc
  have := (Xi_pos hlam β).ne'
  simp only
  field_simp

/-- If `f ∘ k = g ∘ k` a.e. on `[-π, π]` for integrable `f, g`, then `f = g` a.e. on `[-π, π]`. -/
theorem ae_eq_of_comp_kMap {lam : ℝ} (hlam : 0 < lam) {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (-π) π) volume) (hg : IntegrableOn g (Icc (-π) π) volume)
    (h : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)), f (kMap lam β) = g (kMap lam β)) :
    f =ᵐ[volume.restrict (Icc (-π) π)] g := by
  have himg : kMap lam '' Icc (-π) π = Icc (-π) π := (bijOn_kMap hlam).image_eq
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Icc (-π) π) (f := kMap lam)
    (f' := Xi lam) measurableSet_Icc (fun x _ => (hasDerivAt_kMap hlam x).hasDerivWithinAt)
    (strictMono_kMap hlam).injective.injOn (fun x => |f x - g x|)
  rw [himg] at hcov
  have h0 : ∫ x in Icc (-π) π, |f x - g x| = 0 := by
    rw [hcov]
    have : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)), |Xi lam β| • |f (kMap lam β) - g (kMap lam β)| = 0 := by
      filter_upwards [h] with β hβ
      rw [hβ, sub_self, abs_zero, smul_zero]
    rw [integral_congr_ae this]; simp
  have hi : Integrable (fun x => |f x - g x|) (volume.restrict (Icc (-π) π)) :=
    (hf.sub hg).abs
  have := (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg _) hi).1 h0
  filter_upwards [this] with x hx
  simp only [Pi.zero_apply, abs_eq_zero] at hx
  linarith

/-- Linearity of the Poisson convolution. -/
theorem xiConv_sub {μ : ℝ} (hμ : 0 < μ) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume (-π) π) (hg : IntervalIntegrable g volume (-π) π) (α : ℝ) :
    xiConv μ (fun β => f β - g β) α = xiConv μ f α - xiConv μ g α := by
  have hc : Continuous (fun β : ℝ => Xi μ (α - β)) := (continuous_Xi hμ).comp (by fun_prop)
  unfold xiConv
  have : ∀ β : ℝ, Xi μ (α - β) * (f β - g β) = Xi μ (α - β) * f β - Xi μ (α - β) * g β :=
    fun β => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_sub (hf.continuousOn_mul hc.continuousOn)
    (hg.continuousOn_mul hc.continuousOn)]
  ring

theorem xiConv_add {μ : ℝ} (hμ : 0 < μ) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume (-π) π) (hg : IntervalIntegrable g volume (-π) π) (α : ℝ) :
    xiConv μ (fun β => f β + g β) α = xiConv μ f α + xiConv μ g α := by
  have hc : Continuous (fun β : ℝ => Xi μ (α - β)) := (continuous_Xi hμ).comp (by fun_prop)
  unfold xiConv
  have : ∀ β : ℝ, Xi μ (α - β) * (f β + g β) = Xi μ (α - β) * f β + Xi μ (α - β) * g β :=
    fun β => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_add (hf.continuousOn_mul hc.continuousOn)
    (hg.continuousOn_mul hc.continuousOn)]
  ring


theorem continuous_Rsech {lam : ℝ} (hlam : 0 < lam) : Continuous (Rsech lam) := by
  have : Rsech lam = trigSeries (1 / 2) (secCoeff lam) (fun _ => 0) :=
    funext (Rsech_eq_trigSeries hlam)
  rw [this]
  exact continuous_trigSeries (summable_secCoeff hlam) summable_zero _

theorem continuous_rho {Δ : ℝ} (hΔ : Δ < -1) : Continuous (rho Δ) := by
  have hlam := lamOf_pos hΔ
  have : rho Δ = fun x => Rsech (lamOf Δ) (kInv (lamOf Δ) x) /
      (2 * π * Xi (lamOf Δ) (kInv (lamOf Δ) x)) := funext (rho_eq hΔ)
  rw [this]
  have hk := continuous_kInv hlam
  refine ((continuous_Rsech hlam).comp hk).div
    (continuous_const.mul ((continuous_Xi hlam).comp hk)) (fun x => ?_)
  have := Xi_pos hlam (kInv (lamOf Δ) x)
  positivity

theorem integrableOn_Icc_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f (Icc (-π) π) volume :=
  hf.continuousOn.integrableOn_Icc

theorem intervalIntegrable_of_integrableOn_Icc {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (-π) π) volume) : IntervalIntegrable f volume (-π) π := by
  have hpi := Real.pi_pos
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  exact hf.mono_set Ioc_subset_Icc_self

/-- **Proposition 2.1, uniqueness for `ρ`** (integrable version): every integrable solution of
(cBE_Δ) on `[-π, π]` coincides with the explicit `ρ` at every point of `[-π, π]`. -/
theorem eq_rho_of_isCBESolution_of_integrableOn {Δ : ℝ} (hΔ : Δ < -1) {ρ' : ℝ → ℝ}
    (hρ' : IntegrableOn ρ' (Icc (-π) π) volume) (h : IsCBESolution Δ ρ') :
    ∀ x ∈ Icc (-π) π, ρ' x = rho Δ x := by
  have hlam := lamOf_pos hΔ
  have hlam2 : 0 < 2 * lamOf Δ := by linarith
  have hpi := Real.pi_pos
  -- the transformed functions
  have hR'eq := (isCBESolution_iff hΔ ρ').1 h
  have hReq := (isCBESolution_iff hΔ (rho Δ)).1 (rho_isCBESolution hΔ)
  have hRrho : Rtrans Δ (rho Δ) = Rsech (lamOf Δ) := funext (Rtrans_rho hΔ)
  rw [hRrho] at hReq
  -- integrability of `R'`
  have hR'int : IntegrableOn (Rtrans Δ ρ') (Icc (-π) π) volume := by
    have this : IntegrableOn (fun β => 2 * π * (Xi (lamOf Δ) β * ρ' (kMap (lamOf Δ) β)))
        (Icc (-π) π) volume := (integrableOn_Xi_mul_comp hlam hρ').const_mul (2 * π)
    refine this.congr_fun (fun β _ => ?_) measurableSet_Icc
    rw [Rtrans_eq hΔ]; ring
  have hR'ii := intervalIntegrable_of_integrableOn_Icc hR'int
  have hRii : IntervalIntegrable (Rsech (lamOf Δ)) volume (-π) π :=
    ((continuous_Rsech hlam).intervalIntegrable _ _)
  -- the difference solves `D = -(Ξ * D)`
  have hD : ∀ α ∈ Ioc (-π) π,
      (fun β => Rtrans Δ ρ' β - Rsech (lamOf Δ) β) α =
        -xiConv (2 * lamOf Δ) (fun β => Rtrans Δ ρ' β - Rsech (lamOf Δ) β) α := by
    intro α hα
    have hα' : α ∈ Icc (-π) π := Ioc_subset_Icc_self hα
    rw [xiConv_sub hlam2 hR'ii hRii]
    have h1 := hR'eq α hα'
    have h2 := hReq α hα'
    simp only
    linarith
  have hD0 := eq_zero_of_eq_neg_xiConv hlam2 (hR'ii.sub hRii) hD
  -- hence `R' = R` a.e. on `[-π, π]`
  have hae : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)), ρ' (kMap (lamOf Δ) β) = rho Δ (kMap (lamOf Δ) β) := by
    have h1 : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)), Rtrans Δ ρ' β - Rsech (lamOf Δ) β = 0 := by
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
      exact hD0
    filter_upwards [h1] with β hβ
    have hX := Xi_pos hlam β
    have : Rtrans Δ ρ' β = Rtrans Δ (rho Δ) β := by
      rw [hRrho]; linarith
    rw [Rtrans_eq hΔ, Rtrans_eq hΔ] at this
    have h2 : 2 * π * Xi (lamOf Δ) β ≠ 0 := by positivity
    have : (2 * π * Xi (lamOf Δ) β) * ρ' (kMap (lamOf Δ) β) =
        (2 * π * Xi (lamOf Δ) β) * rho Δ (kMap (lamOf Δ) β) := by linarith
    exact mul_left_cancel₀ h2 this
  have hrho : IntegrableOn (rho Δ) (Icc (-π) π) volume :=
    integrableOn_Icc_of_continuous (continuous_rho hΔ)
  have hae2 := ae_eq_of_comp_kMap hlam hρ' hrho hae
  intro x hx
  have h3 := h x hx
  have h4 := rho_isCBESolution hΔ x hx
  have h5 : cBEop Δ ρ' x = cBEop Δ (rho Δ) x := by
    unfold cBEop
    congr 1
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    refine integral_congr_ae ?_
    have : ∀ᵐ y ∂(volume.restrict (Ioc (-π) π)), ρ' y = rho Δ y := by
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
      exact hae2
    filter_upwards [this] with y hy
    rw [hy]
  have h6 : 2 * π * ρ' x = 2 * π * rho Δ x := by rw [h3, h4, h5]
  have h7 : 2 * π ≠ 0 := by positivity
  exact mul_left_cancel₀ h7 h6


/-- **Uniqueness for `ρ`, almost-everywhere form**: an integrable function satisfying (cBE_Δ)
for almost every `x ∈ [-π, π]` coincides with `ρ` almost everywhere on `[-π, π]`. -/
theorem ae_eq_rho_of_ae_cBE {Δ : ℝ} (hΔ : Δ < -1) {ρ' : ℝ → ℝ}
    (hρ' : IntegrableOn ρ' (Icc (-π) π) volume)
    (h : ∀ᵐ x ∂(volume.restrict (Icc (-π) π)), 2 * π * ρ' x = cBEop Δ ρ' x) :
    ρ' =ᵐ[volume.restrict (Icc (-π) π)] rho Δ := by
  have hlam := lamOf_pos hΔ
  have hlam2 : 0 < 2 * lamOf Δ := by linarith
  have hpi := Real.pi_pos
  have hReq := (isCBESolution_iff hΔ (rho Δ)).1 (rho_isCBESolution hΔ)
  have hRrho : Rtrans Δ (rho Δ) = Rsech (lamOf Δ) := funext (Rtrans_rho hΔ)
  rw [hRrho] at hReq
  have hR'int : IntegrableOn (Rtrans Δ ρ') (Icc (-π) π) volume := by
    have this : IntegrableOn (fun β => 2 * π * (Xi (lamOf Δ) β * ρ' (kMap (lamOf Δ) β)))
        (Icc (-π) π) volume := (integrableOn_Xi_mul_comp hlam hρ').const_mul (2 * π)
    refine this.congr_fun (fun β _ => ?_) measurableSet_Icc
    rw [Rtrans_eq hΔ]; ring
  have hR'ii := intervalIntegrable_of_integrableOn_Icc hR'int
  have hRii : IntervalIntegrable (Rsech (lamOf Δ)) volume (-π) π :=
    ((continuous_Rsech hlam).intervalIntegrable _ _)
  have h1 := ae_comp_kMap hlam h
  have h2 : ∀ᵐ α ∂(volume.restrict (Ioc (-π) π)),
      (fun β => Rtrans Δ ρ' β - Rsech (lamOf Δ) β) α =
        -xiConv (2 * lamOf Δ) (fun β => Rtrans Δ ρ' β - Rsech (lamOf Δ) β) α := by
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    rw [ae_restrict_iff' measurableSet_Icc] at h1 ⊢
    filter_upwards [h1] with α hα hαI
    rw [xiConv_sub hlam2 hR'ii hRii]
    have e1 := (cBE_at_iff hΔ ρ' α).1 (hα hαI)
    have e2 := hReq α hαI
    linarith
  have hD0 := eq_zero_of_ae_eq_neg_xiConv hlam2 (hR'ii.sub hRii) h2
  have hae : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)), ρ' (kMap (lamOf Δ) β) = rho Δ (kMap (lamOf Δ) β) := by
    have h3 : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)), Rtrans Δ ρ' β - Rsech (lamOf Δ) β = 0 := by
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
      exact hD0
    filter_upwards [h3] with β hβ
    have hX := Xi_pos hlam β
    have : Rtrans Δ ρ' β = Rtrans Δ (rho Δ) β := by
      rw [hRrho]; linarith
    rw [Rtrans_eq hΔ, Rtrans_eq hΔ] at this
    have h4 : 2 * π * Xi (lamOf Δ) β ≠ 0 := by positivity
    have : (2 * π * Xi (lamOf Δ) β) * ρ' (kMap (lamOf Δ) β) =
        (2 * π * Xi (lamOf Δ) β) * rho Δ (kMap (lamOf Δ) β) := by linarith
    exact mul_left_cancel₀ h4 this
  exact ae_eq_of_comp_kMap hlam hρ' (integrableOn_Icc_of_continuous (continuous_rho hΔ)) hae

end PottsDiscontinuity.Bethe
