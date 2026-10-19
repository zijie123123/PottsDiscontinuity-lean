module

public import Mathlib
public import PottsDiscontinuity.Bethe.FourierPoisson

/-!
# Absolutely convergent trigonometric series and the Poisson convolution

For absolutely summable coefficient sequences `a, b`, the series
`trigSeries a₀ a b α = a₀ + ∑_{n ≥ 0} (a n cos((n+1)α) + b n sin((n+1)α))` is continuous, has
Fourier coefficients `∫ g cos(m ·) = π a_{m-1}`, `∫ g sin(m ·) = π b_{m-1}`, `∫ g = 2π a₀`
(termwise integration over `[-π, π]`), and the Poisson convolution `xiConv μ` multiplies the
`m`-th coefficient by `e^{-μ m}` (`xiConv_trigSeries`).  This is the form in which the
Fourier-coefficient identities of §4 (`Ξ̂_μ(m) = e^{-μ|m|}`) are used.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- Termwise integration over `[-π, π]` of a series of continuous functions with a summable
uniform bound. -/
theorem hasSum_intervalIntegral_of_bound {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, Continuous (F n)) (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ n β, |F n β| ≤ b n) (hsum : ∀ β, HasSum (fun n => F n β) (f β)) :
    HasSum (fun n => ∫ β in (-π)..π, F n β) (∫ β in (-π)..π, f β) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -π) (b := π)
    (fun n _ => b n) (fun n => (hF n).aestronglyMeasurable) ?_ ?_ ?_ ?_
  · intro n
    exact Filter.Eventually.of_forall fun β _ => by rw [Real.norm_eq_abs]; exact hbound n β
  · exact Filter.Eventually.of_forall fun β _ => hb
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun β _ => hsum β

/-- The trigonometric series `a₀ + ∑_{n≥0} (a_n cos((n+1)α) + b_n sin((n+1)α))`. -/
noncomputable def trigSeries (a₀ : ℝ) (a b : ℕ → ℝ) (α : ℝ) : ℝ :=
  a₀ + ∑' n : ℕ, (a n * Real.cos (((n + 1 : ℕ) : ℝ) * α) + b n * Real.sin (((n + 1 : ℕ) : ℝ) * α))

/-- The general term of a trigonometric series. -/
noncomputable def trigTerm (a b : ℕ → ℝ) (n : ℕ) (α : ℝ) : ℝ :=
  a n * Real.cos (((n + 1 : ℕ) : ℝ) * α) + b n * Real.sin (((n + 1 : ℕ) : ℝ) * α)

theorem abs_trigTerm_le (a b : ℕ → ℝ) (n : ℕ) (α : ℝ) : |trigTerm a b n α| ≤ |a n| + |b n| := by
  unfold trigTerm
  calc |a n * Real.cos (((n + 1 : ℕ) : ℝ) * α) + b n * Real.sin (((n + 1 : ℕ) : ℝ) * α)|
      ≤ |a n * Real.cos (((n + 1 : ℕ) : ℝ) * α)| + |b n * Real.sin (((n + 1 : ℕ) : ℝ) * α)| :=
        abs_add_le _ _
    _ ≤ |a n| + |b n| := by
        rw [abs_mul, abs_mul]
        gcongr
        · calc |a n| * |Real.cos (((n + 1 : ℕ) : ℝ) * α)| ≤ |a n| * 1 := by
                gcongr; exact Real.abs_cos_le_one _
            _ = |a n| := mul_one _
        · calc |b n| * |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤ |b n| * 1 := by
                gcongr; exact Real.abs_sin_le_one _
            _ = |b n| := mul_one _

theorem continuous_trigTerm (a b : ℕ → ℝ) (n : ℕ) : Continuous (trigTerm a b n) := by
  unfold trigTerm; fun_prop

theorem hasSum_trigTerm {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (α : ℝ) :
    HasSum (fun n => trigTerm a b n α) (∑' n, trigTerm a b n α) := by
  refine Summable.hasSum ?_
  refine Summable.of_norm_bounded (g := fun n => |a n| + |b n|) (ha.abs.add hb.abs) ?_
  intro n
  rw [Real.norm_eq_abs]
  exact abs_trigTerm_le a b n α

theorem continuous_trigSeries {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ) :
    Continuous (trigSeries a₀ a b) := by
  unfold trigSeries
  refine continuous_const.add ?_
  exact continuous_tsum (continuous_trigTerm a b) (ha.abs.add hb.abs) (abs_trigTerm_le a b)


theorem integral_trigTerm (a b : ℕ → ℝ) (n : ℕ) :
    ∫ β in (-π)..π, trigTerm a b n β = 0 := by
  unfold trigTerm
  rw [intervalIntegral.integral_add ((intervalIntegrable_cos_mul _).const_mul _)
    ((intervalIntegrable_sin_mul _).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_nat_mul (by omega), integral_sin_nat_mul]
  simp

theorem integral_trigTerm_mul_cos (a b : ℕ → ℝ) (n m : ℕ) :
    ∫ β in (-π)..π, trigTerm a b n β * Real.cos (((m + 1 : ℕ) : ℝ) * β) =
      if n = m then π * a n else 0 := by
  have h1 : ∀ β : ℝ, trigTerm a b n β * Real.cos (((m + 1 : ℕ) : ℝ) * β) =
      a n * (Real.cos (((n + 1 : ℕ) : ℝ) * β) * Real.cos (((m + 1 : ℕ) : ℝ) * β)) +
        b n * (Real.sin (((n + 1 : ℕ) : ℝ) * β) * Real.cos (((m + 1 : ℕ) : ℝ) * β)) := by
    intro β; unfold trigTerm; ring
  simp_rw [h1]
  have hi1 : IntervalIntegrable (fun β : ℝ => Real.cos (((n + 1 : ℕ) : ℝ) * β) *
      Real.cos (((m + 1 : ℕ) : ℝ) * β)) volume (-π) π :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun β : ℝ => Real.sin (((n + 1 : ℕ) : ℝ) * β) *
      Real.cos (((m + 1 : ℕ) : ℝ) * β)) volume (-π) π :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos_mul_cos_pos (by omega) (by omega), integral_sin_mul_cos_nat]
  by_cases h : n = m
  · subst h; simp [mul_comm]
  · simp [h]

theorem integral_trigTerm_mul_sin (a b : ℕ → ℝ) (n m : ℕ) :
    ∫ β in (-π)..π, trigTerm a b n β * Real.sin (((m + 1 : ℕ) : ℝ) * β) =
      if n = m then π * b n else 0 := by
  have h1 : ∀ β : ℝ, trigTerm a b n β * Real.sin (((m + 1 : ℕ) : ℝ) * β) =
      a n * (Real.sin (((m + 1 : ℕ) : ℝ) * β) * Real.cos (((n + 1 : ℕ) : ℝ) * β)) +
        b n * (Real.sin (((n + 1 : ℕ) : ℝ) * β) * Real.sin (((m + 1 : ℕ) : ℝ) * β)) := by
    intro β; unfold trigTerm; ring
  simp_rw [h1]
  have hi1 : IntervalIntegrable (fun β : ℝ => Real.sin (((m + 1 : ℕ) : ℝ) * β) *
      Real.cos (((n + 1 : ℕ) : ℝ) * β)) volume (-π) π :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun β : ℝ => Real.sin (((n + 1 : ℕ) : ℝ) * β) *
      Real.sin (((m + 1 : ℕ) : ℝ) * β)) volume (-π) π :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sin_mul_sin_pos (by omega) (by omega), integral_sin_mul_cos_nat]
  by_cases h : n = m
  · subst h; simp [mul_comm]
  · simp [h]

/-- The constant coefficient of a trigonometric series. -/
theorem cosCoeff_trigSeries_zero {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ) :
    cosCoeff (trigSeries a₀ a b) 0 = 2 * π * a₀ := by
  have hpi := Real.pi_pos
  have hs := hasSum_intervalIntegral_of_bound (F := fun n β => trigTerm a b n β)
    (f := fun β => ∑' n, trigTerm a b n β) (continuous_trigTerm a b) _ (ha.abs.add hb.abs)
    (abs_trigTerm_le a b) (hasSum_trigTerm ha hb)
  simp_rw [integral_trigTerm] at hs
  have h0 : ∫ β in (-π)..π, ∑' n, trigTerm a b n β = 0 := hs.unique hasSum_zero
  have hcont : Continuous (fun β => ∑' n, trigTerm a b n β) :=
    continuous_tsum (continuous_trigTerm a b) (ha.abs.add hb.abs) (abs_trigTerm_le a b)
  change ∫ β in (-π)..π, (a₀ + ∑' n, trigTerm a b n β) * Real.cos (((0 : ℕ) : ℝ) * β) = _
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
  rw [intervalIntegral.integral_add intervalIntegrable_const (hcont.intervalIntegrable _ _), h0]
  simp only [add_zero, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem cosCoeff_trigSeries_succ {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ)
    (m : ℕ) : cosCoeff (trigSeries a₀ a b) (m + 1) = π * a m := by
  have hpi := Real.pi_pos
  have hcont : Continuous (fun β => ∑' n, trigTerm a b n β) :=
    continuous_tsum (continuous_trigTerm a b) (ha.abs.add hb.abs) (abs_trigTerm_le a b)
  have hs := hasSum_intervalIntegral_of_bound
    (F := fun n β => trigTerm a b n β * Real.cos (((m + 1 : ℕ) : ℝ) * β))
    (f := fun β => (∑' n, trigTerm a b n β) * Real.cos (((m + 1 : ℕ) : ℝ) * β))
    (fun n => (continuous_trigTerm a b n).mul (by fun_prop)) _ (ha.abs.add hb.abs)
    (fun n β => by
      rw [abs_mul]
      calc |trigTerm a b n β| * |Real.cos (((m + 1 : ℕ) : ℝ) * β)| ≤ |trigTerm a b n β| * 1 := by
            gcongr; exact Real.abs_cos_le_one _
        _ ≤ |a n| + |b n| := by rw [mul_one]; exact abs_trigTerm_le a b n β)
    (fun β => (hasSum_trigTerm ha hb β).mul_right _)
  simp_rw [integral_trigTerm_mul_cos] at hs
  have h2 : ∫ β in (-π)..π, (∑' n, trigTerm a b n β) * Real.cos (((m + 1 : ℕ) : ℝ) * β) = π * a m := by
    refine hs.unique ?_
    have := hasSum_single (f := fun n : ℕ => if n = m then π * a n else 0) m
      (fun n hn => by simp [hn])
    simpa using this
  have hI1 : IntervalIntegrable (fun β : ℝ => a₀ * Real.cos (((m + 1 : ℕ) : ℝ) * β)) volume (-π) π :=
    (intervalIntegrable_cos_mul _).const_mul _
  have hI2 : IntervalIntegrable
      (fun β : ℝ => (∑' n, trigTerm a b n β) * Real.cos (((m + 1 : ℕ) : ℝ) * β)) volume (-π) π :=
    (hcont.mul (by fun_prop)).intervalIntegrable _ _
  change ∫ β in (-π)..π, (a₀ + ∑' n, trigTerm a b n β) * Real.cos (((m + 1 : ℕ) : ℝ) * β) = _
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add hI1 hI2, h2, intervalIntegral.integral_const_mul,
    integral_cos_nat_mul (by omega)]
  simp

theorem sinCoeff_trigSeries_succ {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ)
    (m : ℕ) : sinCoeff (trigSeries a₀ a b) (m + 1) = π * b m := by
  have hpi := Real.pi_pos
  have hcont : Continuous (fun β => ∑' n, trigTerm a b n β) :=
    continuous_tsum (continuous_trigTerm a b) (ha.abs.add hb.abs) (abs_trigTerm_le a b)
  have hs := hasSum_intervalIntegral_of_bound
    (F := fun n β => trigTerm a b n β * Real.sin (((m + 1 : ℕ) : ℝ) * β))
    (f := fun β => (∑' n, trigTerm a b n β) * Real.sin (((m + 1 : ℕ) : ℝ) * β))
    (fun n => (continuous_trigTerm a b n).mul (by fun_prop)) _ (ha.abs.add hb.abs)
    (fun n β => by
      rw [abs_mul]
      calc |trigTerm a b n β| * |Real.sin (((m + 1 : ℕ) : ℝ) * β)| ≤ |trigTerm a b n β| * 1 := by
            gcongr; exact Real.abs_sin_le_one _
        _ ≤ |a n| + |b n| := by rw [mul_one]; exact abs_trigTerm_le a b n β)
    (fun β => (hasSum_trigTerm ha hb β).mul_right _)
  simp_rw [integral_trigTerm_mul_sin] at hs
  have h2 : ∫ β in (-π)..π, (∑' n, trigTerm a b n β) * Real.sin (((m + 1 : ℕ) : ℝ) * β) = π * b m := by
    refine hs.unique ?_
    have := hasSum_single (f := fun n : ℕ => if n = m then π * b n else 0) m
      (fun n hn => by simp [hn])
    simpa using this
  have hI1 : IntervalIntegrable (fun β : ℝ => a₀ * Real.sin (((m + 1 : ℕ) : ℝ) * β)) volume (-π) π :=
    (intervalIntegrable_sin_mul _).const_mul _
  have hI2 : IntervalIntegrable
      (fun β : ℝ => (∑' n, trigTerm a b n β) * Real.sin (((m + 1 : ℕ) : ℝ) * β)) volume (-π) π :=
    (hcont.mul (by fun_prop)).intervalIntegrable _ _
  change ∫ β in (-π)..π, (a₀ + ∑' n, trigTerm a b n β) * Real.sin (((m + 1 : ℕ) : ℝ) * β) = _
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add hI1 hI2, h2, intervalIntegral.integral_const_mul,
    integral_sin_nat_mul]
  simp


theorem summable_pow_succ_mul {a : ℕ → ℝ} (ha : Summable a) {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    Summable (fun n : ℕ => c ^ (n + 1) * a n) := by
  refine Summable.of_norm_bounded (g := fun n => |a n|) ha.abs ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ c ^ (n + 1))]
  calc c ^ (n + 1) * |a n| ≤ 1 * |a n| := by
        gcongr; exact pow_le_one₀ h0 h1
    _ = |a n| := one_mul _

/-- The Poisson convolution acts diagonally on trigonometric series:
`Ξ_μ * (a₀ + ∑ a_n cos((n+1)·) + b_n sin((n+1)·))/(2π) = a₀ + ∑ e^{-μ(n+1)} (a_n cos + b_n sin)`
(the coefficient statement `\widehat{Ξ_μ * g}(m) = e^{-μ|m|} ĝ(m)`). -/
theorem xiConv_trigSeries {μ : ℝ} (hμ : 0 < μ) {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (a₀ α : ℝ) :
    xiConv μ (trigSeries a₀ a b) α = trigSeries a₀ (fun n => Real.exp (-μ) ^ (n + 1) * a n)
      (fun n => Real.exp (-μ) ^ (n + 1) * b n) α := by
  have hpi := Real.pi_pos
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hr1 : Real.exp (-μ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hg : IntervalIntegrable (trigSeries a₀ a b) volume (-π) π :=
    (continuous_trigSeries ha hb a₀).intervalIntegrable _ _
  have h := hasSum_xiConv hμ hg α
  simp_rw [cosCoeff_trigSeries_succ ha hb, sinCoeff_trigSeries_succ ha hb,
    cosCoeff_trigSeries_zero ha hb] at h
  have h2 := h.tsum_eq
  have e1 : (2 * π)⁻¹ * (2 * π * a₀) = a₀ := by field_simp
  rw [e1] at h2
  have e2 : ∀ n : ℕ, π⁻¹ * Real.exp (-μ) ^ (n + 1) *
      (Real.cos (((n + 1 : ℕ) : ℝ) * α) * (π * a n) + Real.sin (((n + 1 : ℕ) : ℝ) * α) * (π * b n)) =
      Real.exp (-μ) ^ (n + 1) * a n * Real.cos (((n + 1 : ℕ) : ℝ) * α) +
        Real.exp (-μ) ^ (n + 1) * b n * Real.sin (((n + 1 : ℕ) : ℝ) * α) := by
    intro n; field_simp
  simp_rw [e2] at h2
  have e3 : trigSeries a₀ (fun n => Real.exp (-μ) ^ (n + 1) * a n)
      (fun n => Real.exp (-μ) ^ (n + 1) * b n) α =
      a₀ + ∑' n : ℕ, (Real.exp (-μ) ^ (n + 1) * a n * Real.cos (((n + 1 : ℕ) : ℝ) * α) +
        Real.exp (-μ) ^ (n + 1) * b n * Real.sin (((n + 1 : ℕ) : ℝ) * α)) := rfl
  rw [e3]
  linarith

end PottsDiscontinuity.Bethe
