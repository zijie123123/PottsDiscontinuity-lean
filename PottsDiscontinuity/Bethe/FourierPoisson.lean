module

public import Mathlib
public import PottsDiscontinuity.Bethe.KMap

/-!
# Fourier analysis of the Poisson kernel `Ξ_μ` on `[-π, π]`

Source: arXiv:1611.09877v2, §2.1 (proof of Proposition 2.1) and §4 (Fourier computations).
This file replaces the residue computation `Ξ̂_μ(m) = e^{-μ|m|}` of §4 by the elementary geometric
series for the Poisson kernel

  `Ξ_μ(α) = sinh μ / (cosh μ - cos α) = 1 + 2 ∑_{m ≥ 1} e^{-μ m} cos (m α)`   (`hasSum_Xi_cos`),

which is absolutely and uniformly convergent for `μ > 0`.  Everything is phrased with real cosine
and sine coefficients.  The main results are:

* `hasSum_xiConv`: for `g` integrable on `[-π, π]`, the convolution operator
  `xiConv μ g α = (1/2π) ∫_{-π}^{π} Ξ_μ(α - β) g(β) dβ` has the absolutely convergent expansion
  `(1/2π) ∫ g + (1/π) ∑_{m≥1} e^{-μ m} (cos(mα) ∫ g cos(m·) + sin(mα) ∫ g sin(m·))`
  (this is the Fourier-coefficient statement `\widehat{Ξ_μ * g}(m) = e^{-μ|m|} ĝ(m)`);
* `integral_mul_xiConv_nonneg`: `∫_{-π}^{π} g · (Ξ_μ * g) ≥ 0` (positive definiteness of `Ξ_μ`);
* `eq_zero_of_eq_neg_xiConv`: an integrable `D` with `D = -(Ξ_μ * D)` on `[-π, π]` vanishes a.e.
  (this is the uniqueness half of Proposition 2.1: `(1 + e^{-μ|m|}) D̂(m) = 0` for all `m`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-! ### The Poisson kernel series -/

theorem Xi_sub_one_eq {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    Xi μ α - 1 = 2 * (Real.exp (-μ) * Real.cos α - Real.exp (-μ) ^ 2) /
      (1 - 2 * Real.exp (-μ) * Real.cos α + Real.exp (-μ) ^ 2) := by
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hr1 : Real.exp (-μ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hc := Real.cos_le_one α
  set r := Real.exp (-μ) with hrdef
  have hden : 0 < 1 - 2 * r * Real.cos α + r ^ 2 := by nlinarith [sq_nonneg (1 - r), mul_pos hr hr]
  have hsinh : Real.sinh μ = (r⁻¹ - r) / 2 := by
    rw [Real.sinh_eq, hrdef, Real.exp_neg, inv_inv]
  have hcosh : Real.cosh μ = (r⁻¹ + r) / 2 := by
    rw [Real.cosh_eq, hrdef, Real.exp_neg, inv_inv]
  unfold Xi
  rw [hsinh, hcosh]
  have e : (r⁻¹ + r) / 2 - Real.cos α = (1 - 2 * r * Real.cos α + r ^ 2) / (2 * r) := by
    field_simp
    ring
  rw [e]
  have h2 : 1 - 2 * r * Real.cos α + r ^ 2 ≠ 0 := hden.ne'
  have h3 : (r⁻¹ - r) / 2 / ((1 - 2 * r * Real.cos α + r ^ 2) / (2 * r)) =
      (1 - r ^ 2) / (1 - 2 * r * Real.cos α + r ^ 2) := by
    field_simp
  rw [h3, div_sub_one h2]
  congr 1
  ring

theorem re_geom_Xi (r α : ℝ) (hr : 0 < r) (hr1 : r < 1) (z : ℂ)
    (hz : z = (r : ℂ) * Complex.exp (α * Complex.I)) :
    (z * (1 - z)⁻¹).re = (r * Real.cos α - r ^ 2) / (1 - 2 * r * Real.cos α + r ^ 2) := by
  have hzre : z.re = r * Real.cos α := by
    rw [hz, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hzim : z.im = r * Real.sin α := by
    rw [hz, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hs := Real.sin_sq_add_cos_sq α
  have hc := Real.cos_le_one α
  have hden : 0 < 1 - 2 * r * Real.cos α + r ^ 2 := by nlinarith [sq_nonneg (1 - r), mul_pos hr hr]
  have hns : Complex.normSq (1 - z) = 1 - 2 * r * Real.cos α + r ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hzre, hzim]
    simp
    nlinarith [hs]
  rw [Complex.mul_re, Complex.inv_re, Complex.inv_im, hns]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hzre, hzim]
  have hD : (1 - r * Real.cos α * 2 + r ^ 2) ≠ 0 := by nlinarith
  rw [← sub_eq_zero]
  field_simp
  linear_combination (-(r^2)) * hs

/-- Poisson kernel series: `Ξ_μ(α) = 1 + 2 ∑_{m ≥ 1} e^{-μ m} cos(m α)` for `μ > 0`. -/
theorem hasSum_Xi_cos {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    HasSum (fun n : ℕ => 2 * Real.exp (-μ) ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * α))
      (Xi μ α - 1) := by
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hr1 : Real.exp (-μ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  set r := Real.exp (-μ) with hrdef
  set z : ℂ := (r : ℂ) * Complex.exp (α * Complex.I) with hz
  have hznorm : ‖z‖ = r := by
    rw [hz, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hr]
  have hz1 : ‖z‖ < 1 := by rw [hznorm]; exact hr1
  have hg := (hasSum_geometric_of_norm_lt_one hz1).mul_left z
  have hre := ((Complex.hasSum_iff _ _).1 hg).1
  have hterm : ∀ n : ℕ, (z * z ^ n).re = r ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * α) := by
    intro n
    rw [← pow_succ', hz, mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul]
    rw [show ((n + 1 : ℕ) : ℂ) * (α * Complex.I) = (((n + 1 : ℕ) : ℝ) * α : ℝ) * Complex.I by
      push_cast; ring]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  simp only [hterm] at hre
  rw [re_geom_Xi r α hr hr1 z hz] at hre
  have := hre.mul_left 2
  convert this using 1
  · funext n; ring
  · rw [Xi_sub_one_eq hμ α]; ring

theorem continuous_Xi {μ : ℝ} (hμ : 0 < μ) : Continuous (Xi μ) := by
  unfold Xi
  refine continuous_const.div (continuous_const.sub Real.continuous_cos) fun α => ?_
  have h2 : 1 < Real.cosh μ := Real.one_lt_cosh.mpr hμ.ne'
  have := Real.cos_le_one α
  linarith

/-! ### Orthogonality on `[-π, π]` -/

theorem integral_cos_int_mul {k : ℤ} (hk : k ≠ 0) : ∫ x in (-π)..π, Real.cos (k * x) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk', integral_cos]
  have h1 : Real.sin (k * π) = 0 := by exact_mod_cast Real.sin_int_mul_pi k
  have h2 : Real.sin (k * -π) = 0 := by
    rw [mul_neg, Real.sin_neg, h1, neg_zero]
  rw [h1, h2]; simp

theorem integral_sin_int_mul (k : ℤ) : ∫ x in (-π)..π, Real.sin (k * x) = 0 := by
  by_cases hk : k = 0
  · simp [hk]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hk', integral_sin]
  have h1 : Real.cos (k * -π) = Real.cos (k * π) := by rw [mul_neg, Real.cos_neg]
  rw [h1]; simp

theorem cos_mul_cos_nat (m n : ℕ) (x : ℝ) : Real.cos (m * x) * Real.cos (n * x) =
      (Real.cos (((m : ℤ) - n : ℤ) * x) + Real.cos (((m : ℤ) + n : ℤ) * x)) / 2 := by
  push_cast
  have := two_mul_cos_mul_cos (m * x) (n * x)
  rw [show ((m:ℝ) - n) * x = m * x - n * x by ring, show ((m:ℝ) + n) * x = m * x + n * x by ring]
  linarith

theorem sin_mul_sin_nat (m n : ℕ) (x : ℝ) : Real.sin (m * x) * Real.sin (n * x) =
      (Real.cos (((m : ℤ) - n : ℤ) * x) - Real.cos (((m : ℤ) + n : ℤ) * x)) / 2 := by
  push_cast
  rw [show ((m:ℝ) - n) * x = m * x - n * x by ring, show ((m:ℝ) + n) * x = m * x + n * x by ring,
    Real.cos_sub, Real.cos_add]
  ring

theorem sin_mul_cos_nat (m n : ℕ) (x : ℝ) : Real.sin (m * x) * Real.cos (n * x) =
      (Real.sin (((m : ℤ) + n : ℤ) * x) + Real.sin (((m : ℤ) - n : ℤ) * x)) / 2 := by
  push_cast
  rw [show ((m:ℝ) - n) * x = m * x - n * x by ring, show ((m:ℝ) + n) * x = m * x + n * x by ring,
    Real.sin_sub, Real.sin_add]
  ring

theorem intervalIntegrable_cos_mul (k : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.cos (k * x)) volume (-π) π :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

theorem intervalIntegrable_sin_mul (k : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.sin (k * x)) volume (-π) π :=
  (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- Orthogonality: `∫_{-π}^{π} cos(m x) cos(n x) dx = π δ_{mn}` for `m, n ≥ 1`. -/
theorem integral_cos_mul_cos_pos {m n : ℕ} (_hm : m ≠ 0) (hn : n ≠ 0) :
    ∫ x in (-π)..π, Real.cos (m * x) * Real.cos (n * x) = if m = n then π else 0 := by
  simp_rw [cos_mul_cos_nat]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by simpa using intervalIntegrable_cos_mul (((m : ℤ) - n : ℤ) : ℝ))
    (by simpa using intervalIntegrable_cos_mul (((m : ℤ) + n : ℤ) : ℝ))]
  have h2 : ∫ x in (-π)..π, Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * x) = 0 :=
    integral_cos_int_mul (by omega)
  rw [h2]
  by_cases h : m = n
  · subst h
    simp only [ite_true, sub_self, Int.cast_zero, zero_mul, Real.cos_zero]
    simp
  · have h1 : ∫ x in (-π)..π, Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * x) = 0 :=
      integral_cos_int_mul (by omega)
    rw [h1]; simp [h]

theorem integral_sin_mul_sin_pos {m n : ℕ} (_hm : m ≠ 0) (hn : n ≠ 0) :
    ∫ x in (-π)..π, Real.sin (m * x) * Real.sin (n * x) = if m = n then π else 0 := by
  simp_rw [sin_mul_sin_nat]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (by simpa using intervalIntegrable_cos_mul (((m : ℤ) - n : ℤ) : ℝ))
    (by simpa using intervalIntegrable_cos_mul (((m : ℤ) + n : ℤ) : ℝ))]
  have h2 : ∫ x in (-π)..π, Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * x) = 0 :=
    integral_cos_int_mul (by omega)
  rw [h2]
  by_cases h : m = n
  · subst h
    simp only [ite_true, sub_self, Int.cast_zero, zero_mul, Real.cos_zero]
    simp
  · have h1 : ∫ x in (-π)..π, Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * x) = 0 :=
      integral_cos_int_mul (by omega)
    rw [h1]; simp [h]

theorem integral_sin_mul_cos_nat (m n : ℕ) :
    ∫ x in (-π)..π, Real.sin (m * x) * Real.cos (n * x) = 0 := by
  simp_rw [sin_mul_cos_nat]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by simpa using intervalIntegrable_sin_mul (((m : ℤ) + n : ℤ) : ℝ))
    (by simpa using intervalIntegrable_sin_mul (((m : ℤ) - n : ℤ) : ℝ)),
    integral_sin_int_mul, integral_sin_int_mul]
  simp

theorem integral_cos_nat_mul {m : ℕ} (hm : m ≠ 0) : ∫ x in (-π)..π, Real.cos (m * x) = 0 := by
  simpa using integral_cos_int_mul (k := (m : ℤ)) (by exact_mod_cast hm)

theorem integral_sin_nat_mul (m : ℕ) : ∫ x in (-π)..π, Real.sin (m * x) = 0 := by
  simpa using integral_sin_int_mul (m : ℤ)

/-! ### The convolution operator `g ↦ Ξ_μ * g / 2π` and its coefficient expansion -/

/-- `xiConv μ g α = (1/2π) ∫_{-π}^{π} Ξ_μ(α - β) g(β) dβ`. -/
noncomputable def xiConv (μ : ℝ) (g : ℝ → ℝ) (α : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ β in (-π)..π, Xi μ (α - β) * g β

/-- Cosine coefficient `∫_{-π}^{π} g(β) cos(m β) dβ` (unnormalised). -/
noncomputable def cosCoeff (g : ℝ → ℝ) (m : ℕ) : ℝ := ∫ β in (-π)..π, g β * Real.cos (m * β)

/-- Sine coefficient `∫_{-π}^{π} g(β) sin(m β) dβ` (unnormalised). -/
noncomputable def sinCoeff (g : ℝ → ℝ) (m : ℕ) : ℝ := ∫ β in (-π)..π, g β * Real.sin (m * β)

theorem hasSum_xiConv {μ : ℝ} (hμ : 0 < μ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-π) π) (α : ℝ) :
    HasSum (fun n : ℕ => π⁻¹ * Real.exp (-μ) ^ (n + 1) *
        (Real.cos (((n + 1 : ℕ) : ℝ) * α) * cosCoeff g (n + 1) +
          Real.sin (((n + 1 : ℕ) : ℝ) * α) * sinCoeff g (n + 1)))
      (xiConv μ g α - (2 * π)⁻¹ * cosCoeff g 0) := by
  have hpi := Real.pi_pos
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hr1 : Real.exp (-μ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  set r := Real.exp (-μ) with hrdef
  -- termwise functions
  let F : ℕ → ℝ → ℝ := fun n β => 2 * r ^ (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * (α - β)) * g β
  have hgi : IntegrableOn g (Ioc (-π) π) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 hg
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (uIoc (-π) π)) := by
    intro n
    have hc : Continuous (fun β : ℝ => 2 * r ^ (n + 1) *
        Real.cos (((n + 1 : ℕ) : ℝ) * (α - β))) := by fun_prop
    rw [uIoc_of_le (by linarith)]
    exact (hc.aestronglyMeasurable).mul hgi.aestronglyMeasurable
  have hgeo : Summable (fun n : ℕ => 2 * r ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one hr.le hr1).mul_left (2 * r)
    refine this.congr fun n => ?_
    ring
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π) (F := F) (f := fun β => (Xi μ (α - β) - 1) * g β)
    (fun n β => 2 * r ^ (n + 1) * ‖g β‖) hmeas ?_ ?_ ?_ ?_
  · -- identify the integrals
    have hI : ∀ n : ℕ, ∫ β in (-π)..π, F n β =
        2 * r ^ (n + 1) * (Real.cos (((n + 1 : ℕ) : ℝ) * α) * cosCoeff g (n + 1) +
          Real.sin (((n + 1 : ℕ) : ℝ) * α) * sinCoeff g (n + 1)) := by
      intro n
      have h1 : ∀ β : ℝ, F n β = 2 * r ^ (n + 1) *
          (Real.cos (((n + 1 : ℕ) : ℝ) * α) * (g β * Real.cos (((n + 1 : ℕ) : ℝ) * β)) +
            Real.sin (((n + 1 : ℕ) : ℝ) * α) * (g β * Real.sin (((n + 1 : ℕ) : ℝ) * β))) := by
        intro β
        simp only [F]
        rw [mul_sub, Real.cos_sub]
        ring
      simp_rw [h1]
      have hi1 : IntervalIntegrable (fun β => g β * Real.cos (((n + 1 : ℕ) : ℝ) * β)) volume (-π) π :=
        hg.mul_continuousOn (by fun_prop)
      have hi2 : IntervalIntegrable (fun β => g β * Real.sin (((n + 1 : ℕ) : ℝ) * β)) volume (-π) π :=
        hg.mul_continuousOn (by fun_prop)
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hi1.const_mul _)
        (hi2.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rfl
    simp_rw [hI] at hsum
    have hXg : IntervalIntegrable (fun β => Xi μ (α - β) * g β) volume (-π) π := by
      have hc : Continuous (fun β : ℝ => Xi μ (α - β)) := (continuous_Xi hμ).comp (by fun_prop)
      exact hg.continuousOn_mul hc.continuousOn
    have hsplit : ∫ β in (-π)..π, (Xi μ (α - β) - 1) * g β =
        (∫ β in (-π)..π, Xi μ (α - β) * g β) - cosCoeff g 0 := by
      have : (fun β => (Xi μ (α - β) - 1) * g β) =
          fun β => Xi μ (α - β) * g β - g β * Real.cos (((0 : ℕ) : ℝ) * β) := by
        funext β; simp; ring
      rw [this, intervalIntegral.integral_sub hXg (by simpa using hg)]
      rfl
    rw [hsplit] at hsum
    have := hsum.mul_left (2 * π)⁻¹
    convert this using 1
    · funext n
      field_simp
    · unfold xiConv
      ring
  · intro n
    refine Filter.Eventually.of_forall fun β _ => ?_
    have hF : F n β = (2 * r ^ (n + 1)) * (Real.cos (((n + 1 : ℕ) : ℝ) * (α - β)) * g β) := by
      simp only [F]; ring
    rw [hF, norm_mul (2 * r ^ (n + 1)) _, norm_mul (Real.cos _) _, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * r ^ (n + 1)),
      Real.norm_eq_abs (Real.cos _)]
    have h3 : |Real.cos (((n + 1 : ℕ) : ℝ) * (α - β))| ≤ 1 := Real.abs_cos_le_one _
    have h4 : 0 ≤ 2 * r ^ (n + 1) := by positivity
    calc 2 * r ^ (n + 1) * (|Real.cos (((n + 1 : ℕ) : ℝ) * (α - β))| * ‖g β‖)
        ≤ 2 * r ^ (n + 1) * (1 * ‖g β‖) := by gcongr
      _ = 2 * r ^ (n + 1) * ‖g β‖ := by rw [one_mul]
  · refine Filter.Eventually.of_forall fun β _ => ?_
    exact hgeo.mul_right _
  · have : (fun β : ℝ => ∑' n : ℕ, 2 * r ^ (n + 1) * ‖g β‖) =
        fun β => (∑' n : ℕ, 2 * r ^ (n + 1)) * ‖g β‖ := by
      funext β; rw [tsum_mul_right]
    rw [this]
    exact hg.norm.const_mul _
  · refine Filter.Eventually.of_forall fun β _ => ?_
    exact (hasSum_Xi_cos hμ (α - β)).mul_right (g β)


theorem abs_cosCoeff_le {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-π) π) (m : ℕ) :
    |cosCoeff g m| ≤ ∫ β in (-π)..π, |g β| := by
  have hpi := Real.pi_pos
  unfold cosCoeff
  have h1 := intervalIntegral.abs_integral_le_integral_abs (f := fun β => g β * Real.cos (m * β))
    (a := -π) (b := π) (μ := volume) (by linarith)
  refine le_trans h1 ?_
  refine intervalIntegral.integral_mono_on (by linarith) ?_ hg.abs ?_
  · have := (hg.mul_continuousOn (g := fun β => Real.cos (m * β)) (by fun_prop))
    exact this.abs
  · intro β _
    rw [abs_mul]
    calc |g β| * |Real.cos (m * β)| ≤ |g β| * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ = |g β| := mul_one _

theorem abs_sinCoeff_le {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-π) π) (m : ℕ) :
    |sinCoeff g m| ≤ ∫ β in (-π)..π, |g β| := by
  have hpi := Real.pi_pos
  unfold sinCoeff
  have h1 := intervalIntegral.abs_integral_le_integral_abs (f := fun β => g β * Real.sin (m * β))
    (a := -π) (b := π) (μ := volume) (by linarith)
  refine le_trans h1 ?_
  refine intervalIntegral.integral_mono_on (by linarith) ?_ hg.abs ?_
  · have := (hg.mul_continuousOn (g := fun β => Real.sin (m * β)) (by fun_prop))
    exact this.abs
  · intro β _
    rw [abs_mul]
    calc |g β| * |Real.sin (m * β)| ≤ |g β| * 1 := by
          gcongr; exact Real.abs_sin_le_one _
      _ = |g β| := mul_one _

/-- the `n`-th term of the expansion of `xiConv`. -/
noncomputable def xiConvTerm (μ : ℝ) (g : ℝ → ℝ) (n : ℕ) (α : ℝ) : ℝ :=
  π⁻¹ * Real.exp (-μ) ^ (n + 1) *
    (Real.cos (((n + 1 : ℕ) : ℝ) * α) * cosCoeff g (n + 1) +
      Real.sin (((n + 1 : ℕ) : ℝ) * α) * sinCoeff g (n + 1))

theorem abs_xiConvTerm_le {μ : ℝ} {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-π) π)
    (n : ℕ) (α : ℝ) :
    |xiConvTerm μ g n α| ≤ π⁻¹ * Real.exp (-μ) ^ (n + 1) * (2 * ∫ β in (-π)..π, |g β|) := by
  unfold xiConvTerm
  have hpi := Real.pi_pos
  have hr := Real.exp_pos (-μ)
  set L := ∫ β in (-π)..π, |g β|
  have h1 := abs_cosCoeff_le hg (n + 1)
  have h2 := abs_sinCoeff_le hg (n + 1)
  have hc := Real.abs_cos_le_one (((n + 1 : ℕ) : ℝ) * α)
  have hs := Real.abs_sin_le_one (((n + 1 : ℕ) : ℝ) * α)
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ π⁻¹ * Real.exp (-μ) ^ (n + 1))]
  gcongr
  calc |Real.cos (((n + 1 : ℕ) : ℝ) * α) * cosCoeff g (n + 1) +
        Real.sin (((n + 1 : ℕ) : ℝ) * α) * sinCoeff g (n + 1)|
      ≤ |Real.cos (((n + 1 : ℕ) : ℝ) * α) * cosCoeff g (n + 1)| +
        |Real.sin (((n + 1 : ℕ) : ℝ) * α) * sinCoeff g (n + 1)| := abs_add_le _ _
    _ ≤ L + L := by
        rw [abs_mul, abs_mul]
        have := abs_nonneg (cosCoeff g (n + 1))
        have := abs_nonneg (sinCoeff g (n + 1))
        gcongr
        · calc |Real.cos (((n + 1 : ℕ) : ℝ) * α)| * |cosCoeff g (n + 1)|
              ≤ 1 * |cosCoeff g (n + 1)| := by gcongr
            _ ≤ L := by rw [one_mul]; exact h1
        · calc |Real.sin (((n + 1 : ℕ) : ℝ) * α)| * |sinCoeff g (n + 1)|
              ≤ 1 * |sinCoeff g (n + 1)| := by gcongr
            _ ≤ L := by rw [one_mul]; exact h2
    _ = 2 * L := by ring

theorem continuous_xiConvTerm (μ : ℝ) (g : ℝ → ℝ) (n : ℕ) : Continuous (xiConvTerm μ g n) := by
  unfold xiConvTerm; fun_prop

theorem xiConv_eq_const_add_tsum {μ : ℝ} (hμ : 0 < μ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-π) π) (α : ℝ) :
    xiConv μ g α = (2 * π)⁻¹ * cosCoeff g 0 + ∑' n : ℕ, xiConvTerm μ g n α := by
  have := (hasSum_xiConv hμ hg α).tsum_eq
  unfold xiConvTerm
  linarith

theorem summable_xiConvTerm_bound {μ : ℝ} (hμ : 0 < μ) (C : ℝ) :
    Summable (fun n : ℕ => π⁻¹ * Real.exp (-μ) ^ (n + 1) * C) := by
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hr1 : Real.exp (-μ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have := (summable_geometric_of_lt_one hr.le hr1).mul_left (π⁻¹ * Real.exp (-μ) * C)
  refine this.congr fun n => ?_
  ring

theorem continuous_xiConv {μ : ℝ} (hμ : 0 < μ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-π) π) : Continuous (xiConv μ g) := by
  have hc : Continuous (fun α => ∑' n : ℕ, xiConvTerm μ g n α) :=
    continuous_tsum (continuous_xiConvTerm μ g)
      (summable_xiConvTerm_bound hμ (2 * ∫ β in (-π)..π, |g β|))
      (fun n α => abs_xiConvTerm_le hg n α)
  have : xiConv μ g = fun α => (2 * π)⁻¹ * cosCoeff g 0 + ∑' n : ℕ, xiConvTerm μ g n α :=
    funext fun α => xiConv_eq_const_add_tsum hμ hg α
  rw [this]
  exact continuous_const.add hc


theorem cosCoeff_zero (g : ℝ → ℝ) : cosCoeff g 0 = ∫ β in (-π)..π, g β := by
  simp [cosCoeff]

/-- Positive definiteness of the Poisson kernel: `∫ g · (Ξ_μ * g) ≥ 0`. -/
theorem integral_mul_xiConv_nonneg {μ : ℝ} (hμ : 0 < μ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-π) π) :
    0 ≤ ∫ α in (-π)..π, g α * xiConv μ g α := by
  have hpi := Real.pi_pos
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  set L := ∫ β in (-π)..π, |g β| with hL
  set A := (2 * π)⁻¹ * cosCoeff g 0 with hA
  have hgi : IntegrableOn g (Ioc (-π) π) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 hg
  have hcont := continuous_xiConv hμ hg
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π) (F := fun n α => g α * xiConvTerm μ g n α)
    (f := fun α => g α * (xiConv μ g α - A))
    (fun n α => |g α| * (π⁻¹ * Real.exp (-μ) ^ (n + 1) * (2 * L))) ?_ ?_ ?_ ?_ ?_
  · -- each term is nonnegative
    have hterm : ∀ n : ℕ, ∫ α in (-π)..π, g α * xiConvTerm μ g n α =
        π⁻¹ * Real.exp (-μ) ^ (n + 1) *
          (cosCoeff g (n + 1) ^ 2 + sinCoeff g (n + 1) ^ 2) := by
      intro n
      have h1 : ∀ α : ℝ, g α * xiConvTerm μ g n α = π⁻¹ * Real.exp (-μ) ^ (n + 1) *
          (cosCoeff g (n + 1) * (g α * Real.cos (((n + 1 : ℕ) : ℝ) * α)) +
            sinCoeff g (n + 1) * (g α * Real.sin (((n + 1 : ℕ) : ℝ) * α))) := by
        intro α; unfold xiConvTerm; ring
      simp_rw [h1]
      have hi1 : IntervalIntegrable (fun β => g β * Real.cos (((n + 1 : ℕ) : ℝ) * β)) volume (-π) π :=
        hg.mul_continuousOn (by fun_prop)
      have hi2 : IntervalIntegrable (fun β => g β * Real.sin (((n + 1 : ℕ) : ℝ) * β)) volume (-π) π :=
        hg.mul_continuousOn (by fun_prop)
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hi1.const_mul _)
        (hi2.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      change π⁻¹ * Real.exp (-μ) ^ (n + 1) * (cosCoeff g (n + 1) * cosCoeff g (n + 1) +
        sinCoeff g (n + 1) * sinCoeff g (n + 1)) = _
      ring
    simp_rw [hterm] at hsum
    have hnn : 0 ≤ ∫ α in (-π)..π, g α * (xiConv μ g α - A) :=
      hsum.nonneg fun n => by positivity
    have hgA : IntervalIntegrable (fun α => g α * A) volume (-π) π := hg.mul_const _
    have hgx : IntervalIntegrable (fun α => g α * (xiConv μ g α - A)) volume (-π) π :=
      hg.mul_continuousOn (hcont.sub continuous_const).continuousOn
    have hsplit : ∫ α in (-π)..π, g α * xiConv μ g α =
        (∫ α in (-π)..π, g α * A) + ∫ α in (-π)..π, g α * (xiConv μ g α - A) := by
      rw [← intervalIntegral.integral_add hgA hgx]
      congr 1; funext α; ring
    rw [hsplit]
    have : 0 ≤ ∫ α in (-π)..π, g α * A := by
      rw [intervalIntegral.integral_mul_const, hA, ← cosCoeff_zero g]
      have : 0 ≤ (2 * π)⁻¹ * (cosCoeff g 0 * cosCoeff g 0) := by
        have := mul_self_nonneg (cosCoeff g 0)
        positivity
      linarith [this]
    linarith
  · -- measurability
    intro n
    rw [uIoc_of_le (by linarith)]
    exact hgi.aestronglyMeasurable.mul (continuous_xiConvTerm μ g n).aestronglyMeasurable
  · -- bound
    intro n
    refine Filter.Eventually.of_forall fun α _ => ?_
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_xiConvTerm_le hg n α) (abs_nonneg _) |>.trans_eq (by ring)
  · refine Filter.Eventually.of_forall fun α _ => ?_
    exact (summable_xiConvTerm_bound hμ (2 * L)).mul_left _
  · have : (fun α : ℝ => ∑' n : ℕ, |g α| * (π⁻¹ * Real.exp (-μ) ^ (n + 1) * (2 * L))) =
        fun α => |g α| * ∑' n : ℕ, (π⁻¹ * Real.exp (-μ) ^ (n + 1) * (2 * L)) := by
      funext α; rw [tsum_mul_left]
    rw [this]
    exact hg.abs.mul_const _
  · refine Filter.Eventually.of_forall fun α _ => ?_
    have := (hasSum_xiConv hμ hg α).mul_left (g α)
    convert this using 1
    funext n
    rfl


/-- Uniqueness mechanism (almost-everywhere form): if `D` is integrable and
`D = -(Ξ_μ * D)` almost everywhere on `(-π, π]`, then `D = 0` almost everywhere on `(-π, π]`. -/
theorem eq_zero_of_ae_eq_neg_xiConv {μ : ℝ} (hμ : 0 < μ) {D : ℝ → ℝ}
    (hD : IntervalIntegrable D volume (-π) π)
    (h : ∀ᵐ α ∂(volume.restrict (Ioc (-π) π)), D α = -xiConv μ D α) :
    D =ᵐ[volume.restrict (Ioc (-π) π)] 0 := by
  have hpi := Real.pi_pos
  have hcont := continuous_xiConv hμ hD
  have hE : IntervalIntegrable (fun α => D α * xiConv μ D α) volume (-π) π :=
    hD.mul_continuousOn hcont.continuousOn
  have hEi : IntegrableOn (fun α => D α * xiConv μ D α) (Ioc (-π) π) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 hE
  have hsq : ∀ᵐ α ∂(volume.restrict (Ioc (-π) π)),
      D α ^ 2 = -(D α * xiConv μ D α) := by
    filter_upwards [h] with α hα
    calc D α ^ 2 = D α * D α := sq _
      _ = D α * (-xiConv μ D α) := by rw [← hα]
      _ = -(D α * xiConv μ D α) := by ring
  have hsqi : IntegrableOn (fun α => D α ^ 2) (Ioc (-π) π) volume :=
    Integrable.congr hEi.neg (by filter_upwards [hsq] with α hα; exact hα.symm)
  have hint : ∫ α in Ioc (-π) π, D α ^ 2 = -∫ α in Ioc (-π) π, D α * xiConv μ D α := by
    rw [← MeasureTheory.integral_neg]
    exact integral_congr_ae hsq
  have hnn := integral_mul_xiConv_nonneg hμ hD
  rw [intervalIntegral.integral_of_le (by linarith)] at hnn
  have h0 : ∫ α in Ioc (-π) π, D α ^ 2 = 0 := by
    have : 0 ≤ ∫ α in Ioc (-π) π, D α ^ 2 := setIntegral_nonneg measurableSet_Ioc (fun α _ => sq_nonneg _)
    linarith
  have := (integral_eq_zero_iff_of_nonneg (μ := volume.restrict (Ioc (-π) π))
    (fun α => sq_nonneg (D α)) hsqi).1 h0
  filter_upwards [this] with α hα
  simpa using hα

/-- Uniqueness mechanism: if `D` is integrable and `D = -(Ξ_μ * D)` on `(-π, π]`, then `D = 0`
almost everywhere on `(-π, π]`. -/
theorem eq_zero_of_eq_neg_xiConv {μ : ℝ} (hμ : 0 < μ) {D : ℝ → ℝ}
    (hD : IntervalIntegrable D volume (-π) π)
    (h : ∀ α ∈ Ioc (-π) π, D α = -xiConv μ D α) :
    D =ᵐ[volume.restrict (Ioc (-π) π)] 0 :=
  eq_zero_of_ae_eq_neg_xiConv hμ hD ((ae_restrict_iff' measurableSet_Ioc).2
    (Filter.Eventually.of_forall h))

end PottsDiscontinuity.Bethe
