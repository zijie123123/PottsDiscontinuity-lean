module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib

/-! # Tannery's theorem and the Wallis constant in the odd correction -/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

/-- The positive Wallis factors, indexed starting at zero. -/
noncomputable def ratioWallisFactor (k : ℕ) : ℝ :=
  1 - (1 / 2 : ℝ) ^ 2 / ((k : ℝ) + 1) ^ 2

theorem ratio_wallisFactor_pos (k : ℕ) : 0 < ratioWallisFactor k := by
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hden : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
  have hq : (1 / 2 : ℝ) ^ 2 / ((k : ℝ) + 1) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
    div_le_self (by positivity) hden
  unfold ratioWallisFactor
  nlinarith only [hq]

theorem ratio_wallis_product_tendsto :
    Tendsto (fun n => ∏ k ∈ range n, ratioWallisFactor k) atTop (𝓝 (2 / Real.pi)) := by
  have ht := (Real.tendsto_euler_sin_prod (1 / 2)).div_const (Real.pi * (1 / 2))
  have hvalue : Real.sin (Real.pi * (1 / 2)) / (Real.pi * (1 / 2)) = 2 / Real.pi := by
    rw [mul_one_div, Real.sin_pi_div_two]
    field_simp
  rw [hvalue] at ht
  apply ht.congr
  intro n
  unfold ratioWallisFactor
  field_simp [Real.pi_ne_zero]

theorem ratio_summable_rank_bound (C : ℝ) :
    Summable (fun k : ℕ => C / ((k : ℝ) + 1) ^ 2) := by
  have hs : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hs
  simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using hshift.mul_left C

/-- A growing finite log-product with pointwise Wallis limits and a common
reciprocal-square majorant converges to the Wallis constant. This is the
standard dominated-series step, independent of the root construction. -/
theorem ratio_wallis_limit_of_log_bounds (t : ℕ → ℕ) (v : ℕ → ℕ → ℝ) (C : ℝ)
    (hpoint : ∀ k, Tendsto (fun i => v i k) atTop (𝓝 (Real.log (ratioWallisFactor k))))
    (hzero : ∀ i k, t i ≤ k → v i k = 0)
    (hbound : ∀ᶠ i in atTop, ∀ k, ‖v i k‖ ≤ C / ((k : ℝ) + 1) ^ 2) :
    Tendsto (fun i => Real.exp (∑ k ∈ range (t i), v i k)) atTop (𝓝 (2 / Real.pi)) := by
  have hdom := ratio_summable_rank_bound C
  have hlogBound (k : ℕ) : ‖Real.log (ratioWallisFactor k)‖ ≤ C / ((k : ℝ) + 1) ^ 2 :=
    le_of_tendsto (hpoint k).norm (hbound.mono (fun i hi => hi k))
  have hlogSummable : Summable (fun k => Real.log (ratioWallisFactor k)) :=
    Summable.of_norm_bounded hdom hlogBound
  have hseries := tendsto_tsum_of_dominated_convergence hdom hpoint hbound
  have hlogs := (Real.continuous_exp.tendsto _).comp hlogSummable.hasSum.tendsto_sum_nat
  have hfinite (n : ℕ) : Real.exp (∑ k ∈ range n, Real.log (ratioWallisFactor k)) =
      ∏ k ∈ range n, ratioWallisFactor k := by
    rw [Real.exp_sum]
    apply prod_congr rfl
    intro k hk
    exact Real.exp_log (ratio_wallisFactor_pos k)
  have hlogValue : Real.exp (∑' k, Real.log (ratioWallisFactor k)) = 2 / Real.pi := by
    have ht : Tendsto (fun n => ∏ k ∈ range n, ratioWallisFactor k) atTop
        (𝓝 (Real.exp (∑' k, Real.log (ratioWallisFactor k)))) := by
      simpa only [Function.comp_def, hfinite] using hlogs
    exact tendsto_nhds_unique ht ratio_wallis_product_tendsto
  have ht := (Real.continuous_exp.tendsto _).comp hseries
  rw [hlogValue] at ht
  have hs (i : ℕ) : (∑' k, v i k) = ∑ k ∈ range (t i), v i k :=
    tsum_eq_sum (fun k hk => hzero i k (Nat.le_of_not_gt (fun h => hk (mem_range.mpr h))))
  simpa only [Function.comp_def, hs] using ht

end PottsDiscontinuity.Bethe
