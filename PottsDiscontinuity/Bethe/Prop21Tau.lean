module

public import Mathlib
public import PottsDiscontinuity.Bethe.FourierSawtooth
public import PottsDiscontinuity.Bethe.Prop21Rho

/-!
# Proposition 2.1 for `τ`: the explicit solution of (cOE_Δ) and its uniqueness

Source: arXiv:1611.09877v2, Proposition 2.1 and its proof (§2.1), with the Fourier computations of
§4 (`T̂(m) = ((-1)^m/(i m)) tanh(λ|m|)`, `Ψ̂(m) = ((-1)^m/(i m))(1 - Ξ̂_{2λ}(m))`).

**End-point convention.**  The series in (2.1),
`τ(x) = ∑_{m>0} (-1)^m/(π m) tanh(λ m) sin(m α)`, is not absolutely summable and is interpreted as
the limit of its partial sums (`tauPartial`, `tauSeries`, `tau`).  For `|α| < π` the limit exists and
equals `T(α)/(2π)`, where `T = -α + U_λ` (`tendsto_tauPartial`, `tau_eq_tauCont`).  At `α = ±π` all
terms vanish, so the *literal* series is `0` there (`tau_pi`, `tau_neg_pi`), while the continuous
solution has `τ_c(±π) = ∓1/2` (`tauCont_pi`, `tauCont_neg_pi`).  Consequently the literal `τ`
solves (cOE) on `(-π, π)` (`tau_cOE_on_Ioo`) but not at the end points (`tau_not_cOE_pi`); the
continuous representative `tauCont` solves (cOE) on all of `[-π, π]` (`tauCont_isCOESolution`),
and uniqueness holds in `L²` (`eq_tauCont_of_isCOESolution_of_integrableOn`), i.e. up to a null set.

* `TcontFn_add_xiConv`: `T + (1/2π) Ξ_{2λ} * T = Ψ`, i.e. (cOE'), for `T = -α + U_λ`;
* `tauU_add_xiConv`: `U + (1/2π) Ξ_{2λ} * U = -2 sawS(2λ)`, from the Poisson action on the sine
  series and `1 - tanh x = e^{-x}/cosh x`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- The partial sums `∑_{m=1}^{N} (-1)^m/(π m) tanh(λ m) sin(m α)` of the series for `τ` in (2.1)
(written with `m = n + 1`). -/
noncomputable def tauPartial (lam α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (-1) ^ (n + 1) / (π * ((n : ℝ) + 1)) * Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) *
    Real.sin (((n + 1 : ℕ) : ℝ) * α)

/-- The literal series `τ(x) = ∑_{m>0} (-1)^m/(π m) tanh(λ m) sin(m α)` of (2.1) at `α`,
as the limit of the partial sums (the series is not absolutely summable). -/
noncomputable def tauSeries (lam α : ℝ) : ℝ := limUnder atTop (tauPartial lam α)

/-- The literal `τ` of (2.1): `τ(x) = tauSeries λ (k^{-1}(x))`. -/
noncomputable def tau (Δ x : ℝ) : ℝ := tauSeries (lamOf Δ) (kInv (lamOf Δ) x)

/-- Coefficients of the smooth periodic part `U` of `T`: `u_n = 2(-1)^n (1 - tanh(λ(n+1)))/(n+1)`. -/
noncomputable def tauCoeff (lam : ℝ) (n : ℕ) : ℝ :=
  2 * (-1) ^ n * (1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ))) / ((n : ℝ) + 1)

/-- `U_λ(α) = ∑_{n≥0} u_n sin((n+1)α)`, absolutely convergent. -/
noncomputable def tauU (lam α : ℝ) : ℝ := trigSeries 0 (fun _ => 0) (tauCoeff lam) α

/-- `T(α) = 2π τ(k(α))` for the continuous representative: `T(α) = -α + U_λ(α)`. -/
noncomputable def TcontFn (lam α : ℝ) : ℝ := -α + tauU lam α

/-- The continuous representative of `τ`: `τ_c(x) = T(k^{-1}(x))/(2π)`; it equals the series
(2.1) for `|x| < π` and takes the values `∓1/2` at `x = ±π`. -/
noncomputable def tauCont (Δ x : ℝ) : ℝ :=
  TcontFn (lamOf Δ) (kInv (lamOf Δ) x) / (2 * π)

theorem one_sub_tanh_eq (x : ℝ) : 1 - Real.tanh x = Real.exp (-x) / Real.cosh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  field_simp
  rw [Real.cosh_sub_sinh]

theorem one_sub_tanh_eq_mul_secCoeff (lam : ℝ) (n : ℕ) :
    1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) = Real.exp (-lam) ^ (n + 1) * secCoeff lam n := by
  rw [one_sub_tanh_eq]
  unfold secCoeff
  have h2 : Real.exp (-lam) ^ (n + 1) = Real.exp (-(lam * ((n + 1 : ℕ) : ℝ))) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h2]; ring

theorem secCoeff_le_one (lam : ℝ) (n : ℕ) : secCoeff lam n ≤ 1 := by
  unfold secCoeff
  rw [div_le_one (Real.cosh_pos _)]
  exact Real.one_le_cosh _

theorem abs_tauCoeff_le (lam : ℝ) (n : ℕ) :
    |tauCoeff lam n| ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
  have hq : 0 < Real.exp (-lam) ^ (n + 1) := by positivity
  have h1 := one_sub_tanh_eq_mul_secCoeff lam n
  have h2 := secCoeff_pos lam n
  have h3 := secCoeff_le_one lam n
  have h4 : 0 ≤ 1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) := by
    rw [h1]; positivity
  have h5 : 1 - Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) ≤ Real.exp (-lam) ^ (n + 1) := by
    rw [h1]; nlinarith
  unfold tauCoeff
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [abs_div, abs_of_pos hn, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (two_pos : (0:ℝ) < 2), abs_of_nonneg h4]
  rw [div_le_iff₀ hn]
  have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  nlinarith

theorem summable_tauCoeff {lam : ℝ} (hlam : 0 < lam) : Summable (tauCoeff lam) := by
  have hr : 0 < Real.exp (-lam) := Real.exp_pos _
  have hr1 : Real.exp (-lam) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hs : Summable (fun n : ℕ => 2 * Real.exp (-lam) ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-lam))
    exact this.congr fun n => by ring
  exact Summable.of_norm_bounded hs (fun n => by rw [Real.norm_eq_abs]; exact abs_tauCoeff_le lam n)

theorem continuous_tauU {lam : ℝ} (hlam : 0 < lam) : Continuous (tauU lam) :=
  continuous_trigSeries summable_zero (summable_tauCoeff hlam) 0

theorem continuous_TcontFn {lam : ℝ} (hlam : 0 < lam) : Continuous (TcontFn lam) :=
  continuous_neg.add (continuous_tauU hlam)

/-- `(1 + e^{-2λ(n+1)}) u_n = -4 (-1)^{n+1} e^{-2λ(n+1)}/(n+1)`. -/
theorem one_add_mul_tauCoeff {lam : ℝ} (n : ℕ) :
    (1 + Real.exp (-(2 * lam)) ^ (n + 1)) * tauCoeff lam n =
      -(2 * (2 * (-1) ^ (n + 1) * Real.exp (-(2 * lam)) ^ (n + 1) / ((n : ℝ) + 1))) := by
  have h1 := one_sub_tanh_eq_mul_secCoeff lam n
  have h2 := one_add_exp_two_mul_div_cosh (lam := lam) n
  have h3 : Real.exp (-(2 * lam)) ^ (n + 1) = Real.exp (-lam) ^ (n + 1) * Real.exp (-lam) ^ (n + 1) := by
    have e : Real.exp (-(2 * lam)) = Real.exp (-lam) * Real.exp (-lam) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e, mul_pow]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  unfold tauCoeff
  rw [h1]
  have : (1 + Real.exp (-(2 * lam)) ^ (n + 1)) * (2 * (-1) ^ n *
      (Real.exp (-lam) ^ (n + 1) * secCoeff lam n) / ((n : ℝ) + 1)) =
      2 * (-1) ^ n * Real.exp (-lam) ^ (n + 1) * ((1 + Real.exp (-(2 * lam)) ^ (n + 1)) * secCoeff lam n) /
        ((n : ℝ) + 1) := by ring
  rw [this, h2, h3]
  rw [pow_succ (-1 : ℝ) n]
  field_simp

/-- `U + (1/2π) Ξ_{2λ} * U = -2 sawS(2λ)`. -/
theorem tauU_add_xiConv {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    tauU lam α + xiConv (2 * lam) (tauU lam) α = -2 * sawS (2 * lam) α := by
  have hlam2 : 0 < 2 * lam := by linarith
  have hr : 0 < Real.exp (-(2 * lam)) := Real.exp_pos _
  have hr1 : Real.exp (-(2 * lam)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hu := summable_tauCoeff hlam
  have hz : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  have hX : xiConv (2 * lam) (tauU lam) α =
      trigSeries 0 (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * tauCoeff lam n) α :=
    xiConv_trigSeries hlam2 hz hu 0 α
  have hu2 : Summable (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * tauCoeff lam n) :=
    summable_pow_succ_mul hu hr.le hr1.le
  have hz2 : Summable (fun n : ℕ => Real.exp (-(2 * lam)) ^ (n + 1) * 0) := by simp
  have h1 := hasSum_trigTerm hz hu α
  have h2 := hasSum_trigTerm hz2 hu2 α
  have h3 := h1.add h2
  have h4 := (hasSum_xiConv_neg_id hlam2 α).mul_left (-2)
  have e1 : tauU lam α = 0 + ∑' n, trigTerm (fun _ => 0) (tauCoeff lam) n α := rfl
  have e2 : xiConv (2 * lam) (tauU lam) α = 0 +
      ∑' n, trigTerm (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * tauCoeff lam n) n α := by
    rw [hX]; rfl
  have h5 : (fun n => trigTerm (fun _ => 0) (tauCoeff lam) n α +
      trigTerm (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * 0)
        (fun n => Real.exp (-(2 * lam)) ^ (n + 1) * tauCoeff lam n) n α) =
      fun n : ℕ => -2 * (2 * (-1) ^ (n + 1) * Real.exp (-(2 * lam)) ^ (n + 1) / ((n : ℝ) + 1) *
        Real.sin (((n + 1 : ℕ) : ℝ) * α)) := by
    funext n
    unfold trigTerm
    have := one_add_mul_tauCoeff (lam := lam) n
    have e : tauCoeff lam n + Real.exp (-(2 * lam)) ^ (n + 1) * tauCoeff lam n =
        (1 + Real.exp (-(2 * lam)) ^ (n + 1)) * tauCoeff lam n := by ring
    calc 0 * Real.cos (((n + 1 : ℕ) : ℝ) * α) + tauCoeff lam n * Real.sin (((n + 1 : ℕ) : ℝ) * α) +
        (Real.exp (-(2 * lam)) ^ (n + 1) * 0 * Real.cos (((n + 1 : ℕ) : ℝ) * α) +
          Real.exp (-(2 * lam)) ^ (n + 1) * tauCoeff lam n * Real.sin (((n + 1 : ℕ) : ℝ) * α))
        = (tauCoeff lam n + Real.exp (-(2 * lam)) ^ (n + 1) * tauCoeff lam n) *
            Real.sin (((n + 1 : ℕ) : ℝ) * α) := by ring
      _ = _ := by rw [e, this]; ring
  rw [h5] at h3
  have h6 := h3.unique h4
  rw [xiConv_neg_id hlam2] at h6
  rw [e1, e2]
  linarith

/-- The key identity of the existence half for `τ`: `T + (1/2π) Ξ_{2λ} * T = Ψ`
(equation (cOE') of the source) for `T = -α + U_λ`. -/
theorem TcontFn_add_xiConv {Δ : ℝ} (hΔ : Δ < -1) (α : ℝ) :
    TcontFn (lamOf Δ) α + xiConv (2 * lamOf Δ) (TcontFn (lamOf Δ)) α = PsiFn Δ α := by
  have hlam := lamOf_pos hΔ
  have hlam2 : 0 < 2 * lamOf Δ := by linarith
  have hneg : IntervalIntegrable (fun β : ℝ => -β) volume (-π) π :=
    continuous_neg.intervalIntegrable _ _
  have hU : IntervalIntegrable (tauU (lamOf Δ)) volume (-π) π :=
    (continuous_tauU hlam).intervalIntegrable _ _
  have hfun : TcontFn (lamOf Δ) = fun β => -β + tauU (lamOf Δ) β := rfl
  rw [hfun, xiConv_add hlam2 hneg hU, xiConv_neg_id hlam2, PsiFn_eq_neg_sub_sawS hΔ]
  have := tauU_add_xiConv hlam α
  simp only
  linarith

theorem Ttrans_tauCont {Δ : ℝ} (hΔ : Δ < -1) :
    Ttrans Δ (tauCont Δ) = TcontFn (lamOf Δ) := by
  have hlam := lamOf_pos hΔ
  have hpi := Real.pi_pos
  funext α
  unfold Ttrans tauCont
  rw [kInv_kMap hlam]
  field_simp

/-- **Proposition 2.1, existence for `τ`**: the continuous representative `τ_c` of `τ` solves
(cOE_Δ) at every `x ∈ [-π, π]`, including the end points (where `τ_c(±π) = ∓1/2`). -/
theorem tauCont_isCOESolution {Δ : ℝ} (hΔ : Δ < -1) : IsCOESolution Δ (tauCont Δ) := by
  rw [isCOESolution_iff hΔ, Ttrans_tauCont hΔ]
  intro α _
  exact TcontFn_add_xiConv hΔ α

theorem continuous_tauCont {Δ : ℝ} (hΔ : Δ < -1) : Continuous (tauCont Δ) := by
  have hlam := lamOf_pos hΔ
  exact ((continuous_TcontFn hlam).comp (continuous_kInv hlam)).div_const _

/-- **Proposition 2.1, uniqueness for `τ`** (integrable version): every integrable solution of
(cOE_Δ) on `[-π, π]` coincides with `τ_c` at every point of `[-π, π]`. -/
theorem eq_tauCont_of_isCOESolution_of_integrableOn {Δ : ℝ} (hΔ : Δ < -1) {τ' : ℝ → ℝ}
    (hτ' : IntegrableOn τ' (Icc (-π) π) volume) (h : IsCOESolution Δ τ') :
    ∀ x ∈ Icc (-π) π, τ' x = tauCont Δ x := by
  have hlam := lamOf_pos hΔ
  have hlam2 : 0 < 2 * lamOf Δ := by linarith
  have hpi := Real.pi_pos
  have hT'eq := (isCOESolution_iff hΔ τ').1 h
  have hTeq := (isCOESolution_iff hΔ (tauCont Δ)).1 (tauCont_isCOESolution hΔ)
  have hTrho : Ttrans Δ (tauCont Δ) = TcontFn (lamOf Δ) := Ttrans_tauCont hΔ
  rw [hTrho] at hTeq
  have hT'int : IntegrableOn (Ttrans Δ τ') (Icc (-π) π) volume := by
    have : IntegrableOn (fun β => 2 * π * τ' (kMap (lamOf Δ) β)) (Icc (-π) π) volume :=
      (integrableOn_comp_kMap_of_Xi hlam hτ').const_mul (2 * π)
    exact this
  have hT'ii := intervalIntegrable_of_integrableOn_Icc hT'int
  have hTii : IntervalIntegrable (TcontFn (lamOf Δ)) volume (-π) π :=
    ((continuous_TcontFn hlam).intervalIntegrable _ _)
  have hD : ∀ α ∈ Ioc (-π) π,
      (fun β => Ttrans Δ τ' β - TcontFn (lamOf Δ) β) α =
        -xiConv (2 * lamOf Δ) (fun β => Ttrans Δ τ' β - TcontFn (lamOf Δ) β) α := by
    intro α hα
    have hα' : α ∈ Icc (-π) π := Ioc_subset_Icc_self hα
    rw [xiConv_sub hlam2 hT'ii hTii]
    have h1 := hT'eq α hα'
    have h2 := hTeq α hα'
    simp only
    linarith
  have hD0 := eq_zero_of_eq_neg_xiConv hlam2 (hT'ii.sub hTii) hD
  have hae : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)),
      τ' (kMap (lamOf Δ) β) = tauCont Δ (kMap (lamOf Δ) β) := by
    have h1 : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)),
        Ttrans Δ τ' β - TcontFn (lamOf Δ) β = 0 := by
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
      exact hD0
    filter_upwards [h1] with β hβ
    have : Ttrans Δ τ' β = Ttrans Δ (tauCont Δ) β := by
      rw [hTrho]; linarith
    unfold Ttrans at this
    have h2 : 2 * π ≠ 0 := by positivity
    exact mul_left_cancel₀ h2 this
  have hτc : IntegrableOn (tauCont Δ) (Icc (-π) π) volume :=
    integrableOn_Icc_of_continuous (continuous_tauCont hΔ)
  have hae2 := ae_eq_of_comp_kMap hlam hτ' hτc hae
  intro x hx
  have h3 := h x hx
  have h4 := tauCont_isCOESolution hΔ x hx
  have h5 : cOEop Δ τ' x = cOEop Δ (tauCont Δ) x := by
    unfold cOEop
    congr 1
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    refine integral_congr_ae ?_
    have : ∀ᵐ y ∂(volume.restrict (Ioc (-π) π)), τ' y = tauCont Δ y := by
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
      exact hae2
    filter_upwards [this] with y hy
    rw [hy]
  have h6 : 2 * π * τ' x = 2 * π * tauCont Δ x := by rw [h3, h4, h5]
  have h7 : 2 * π ≠ 0 := by positivity
  exact mul_left_cancel₀ h7 h6

/-! ### The literal series (2.1) for `τ` -/

/-- For `|α| < π` the partial sums of the series (2.1) for `τ` converge to `T(α)/(2π)`
with `T = -α + U_λ`, i.e. to the continuous representative. -/
theorem tendsto_tauPartial {lam : ℝ} (hlam : 0 < lam) {α : ℝ} (hα : |α| < π) :
    Tendsto (tauPartial lam α) atTop (𝓝 (TcontFn lam α / (2 * π))) := by
  have hpi := Real.pi_pos
  have h1 := tendsto_sawtooth hα
  have hU := (hasSum_trigTerm (a := fun _ => (0 : ℝ)) (b := tauCoeff lam) summable_zero
    (summable_tauCoeff hlam) α).tendsto_sum_nat
  have h2 := (h1.add (hU.const_mul (1 / 2))).const_mul (1 / π)
  have hval : 1 / π * (-α / 2 + 1 / 2 * ∑' n, trigTerm (fun _ => (0 : ℝ)) (tauCoeff lam) n α) =
      TcontFn lam α / (2 * π) := by
    unfold TcontFn tauU trigSeries
    simp only [zero_add]
    unfold trigTerm
    field_simp
  rw [hval] at h2
  refine h2.congr (fun N => ?_)
  unfold tauPartial
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold tauCoeff trigTerm
  have hn : ((i : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  rw [pow_succ (-1 : ℝ) i]
  ring

theorem tauSeries_eq {lam : ℝ} (hlam : 0 < lam) {α : ℝ} (hα : |α| < π) :
    tauSeries lam α = TcontFn lam α / (2 * π) :=
  (tendsto_tauPartial hlam hα).limUnder_eq

theorem tauPartial_pi (lam : ℝ) (N : ℕ) : tauPartial lam π N = 0 := by
  unfold tauPartial
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Real.sin_nat_mul_pi]; simp [mul_comm]

theorem tauPartial_neg_pi (lam : ℝ) (N : ℕ) : tauPartial lam (-π) N = 0 := by
  unfold tauPartial
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_neg, Real.sin_neg, Real.sin_nat_mul_pi]; simp

/-- At the end points the *literal* series of (2.1) vanishes (every `sin(mπ) = 0`). -/
theorem tauSeries_pi (lam : ℝ) : tauSeries lam π = 0 := by
  have : tauPartial lam π = fun _ => 0 := funext (tauPartial_pi lam)
  unfold tauSeries
  rw [this]
  exact (tendsto_const_nhds (x := (0:ℝ))).limUnder_eq

theorem tauSeries_neg_pi (lam : ℝ) : tauSeries lam (-π) = 0 := by
  have : tauPartial lam (-π) = fun _ => 0 := funext (tauPartial_neg_pi lam)
  unfold tauSeries
  rw [this]
  exact (tendsto_const_nhds (x := (0:ℝ))).limUnder_eq

theorem tauU_pi (lam : ℝ) : tauU lam π = 0 := by
  have : ∀ n : ℕ, Real.sin (((n + 1 : ℕ) : ℝ) * π) = 0 := fun n => Real.sin_nat_mul_pi (n + 1)
  unfold tauU trigSeries
  simp only [this, mul_zero, zero_mul, add_zero, tsum_zero]

theorem tauU_neg_pi (lam : ℝ) : tauU lam (-π) = 0 := by
  unfold tauU trigSeries
  have : ∀ n : ℕ, Real.sin (((n + 1 : ℕ) : ℝ) * -π) = 0 := fun n => by
    rw [mul_neg, Real.sin_neg, Real.sin_nat_mul_pi, neg_zero]
  simp only [this, mul_zero, zero_mul, add_zero, tsum_zero]

/-- The continuous representative has the end-point values `τ(π) = -1/2`. -/
theorem tauCont_pi {Δ : ℝ} (hΔ : Δ < -1) : tauCont Δ π = -1 / 2 := by
  have hlam := lamOf_pos hΔ
  have hpi := Real.pi_pos
  unfold tauCont
  rw [kInv_eq_of_kMap_eq hlam (kMap_pi _)]
  unfold TcontFn
  rw [tauU_pi]
  field_simp
  ring

/-- ... and `τ(-π) = 1/2`. -/
theorem tauCont_neg_pi {Δ : ℝ} (hΔ : Δ < -1) : tauCont Δ (-π) = 1 / 2 := by
  have hlam := lamOf_pos hΔ
  have hpi := Real.pi_pos
  unfold tauCont
  rw [kInv_eq_of_kMap_eq hlam (kMap_neg_pi _)]
  unfold TcontFn
  rw [tauU_neg_pi]
  field_simp
  ring

theorem tau_pi {Δ : ℝ} (hΔ : Δ < -1) : tau Δ π = 0 := by
  unfold tau
  rw [kInv_eq_of_kMap_eq (lamOf_pos hΔ) (kMap_pi _), tauSeries_pi]

theorem tau_neg_pi {Δ : ℝ} (hΔ : Δ < -1) : tau Δ (-π) = 0 := by
  unfold tau
  rw [kInv_eq_of_kMap_eq (lamOf_pos hΔ) (kMap_neg_pi _), tauSeries_neg_pi]

theorem abs_kInv_lt {Δ : ℝ} (hΔ : Δ < -1) {x : ℝ} (hx : x ∈ Ioo (-π) π) :
    |kInv (lamOf Δ) x| < π := by
  have hlam := lamOf_pos hΔ
  have hx' : x ∈ Icc (-π) π := Ioo_subset_Icc_self hx
  have hm := kInv_mem_Icc hlam hx'
  rw [abs_lt]
  have hk := kMap_kInv hlam x
  refine ⟨lt_of_le_of_ne hm.1 ?_, lt_of_le_of_ne hm.2 ?_⟩
  · intro h
    have : x = -π := by rw [← hk, ← h, kMap_neg_pi]
    exact hx.1.ne this.symm
  · intro h
    have : x = π := by rw [← hk, h, kMap_pi]
    exact hx.2.ne this

/-- In the open interval the literal series (2.1) is the continuous representative. -/
theorem tau_eq_tauCont {Δ : ℝ} (hΔ : Δ < -1) {x : ℝ} (hx : x ∈ Ioo (-π) π) :
    tau Δ x = tauCont Δ x := by
  unfold tau tauCont
  exact tauSeries_eq (lamOf_pos hΔ) (abs_kInv_lt hΔ hx)

theorem tau_ae_eq_tauCont {Δ : ℝ} (hΔ : Δ < -1) :
    tau Δ =ᵐ[volume.restrict (Icc (-π) π)] tauCont Δ := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  exact Filter.Eventually.of_forall fun x hx => tau_eq_tauCont hΔ hx

/-- The literal `τ` satisfies (cOE) at every interior point. -/
theorem tau_cOE_on_Ioo {Δ : ℝ} (hΔ : Δ < -1) {x : ℝ} (hx : x ∈ Ioo (-π) π) :
    2 * π * tau Δ x = cOEop Δ (tau Δ) x := by
  have hpi := Real.pi_pos
  have h1 := tauCont_isCOESolution hΔ x (Ioo_subset_Icc_self hx)
  have h2 : cOEop Δ (tau Δ) x = cOEop Δ (tauCont Δ) x := by
    unfold cOEop
    congr 1
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    refine integral_congr_ae ?_
    have : ∀ᵐ y ∂(volume.restrict (Ioc (-π) π)), tau Δ y = tauCont Δ y := by
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
      exact tau_ae_eq_tauCont hΔ
    filter_upwards [this] with y hy
    rw [hy]
  rw [h2, tau_eq_tauCont hΔ hx, h1]

/-- **Uniqueness for `τ`, almost-everywhere form**: an integrable function satisfying (cOE_Δ)
for almost every `x ∈ [-π, π]` coincides with `τ_c` (equivalently with the literal series `τ`)
almost everywhere on `[-π, π]`. -/
theorem ae_eq_tauCont_of_ae_cOE {Δ : ℝ} (hΔ : Δ < -1) {τ' : ℝ → ℝ}
    (hτ' : IntegrableOn τ' (Icc (-π) π) volume)
    (h : ∀ᵐ x ∂(volume.restrict (Icc (-π) π)), 2 * π * τ' x = cOEop Δ τ' x) :
    τ' =ᵐ[volume.restrict (Icc (-π) π)] tauCont Δ := by
  have hlam := lamOf_pos hΔ
  have hlam2 : 0 < 2 * lamOf Δ := by linarith
  have hpi := Real.pi_pos
  have hTeq := (isCOESolution_iff hΔ (tauCont Δ)).1 (tauCont_isCOESolution hΔ)
  have hTrho : Ttrans Δ (tauCont Δ) = TcontFn (lamOf Δ) := Ttrans_tauCont hΔ
  rw [hTrho] at hTeq
  have hT'int : IntegrableOn (Ttrans Δ τ') (Icc (-π) π) volume :=
    (integrableOn_comp_kMap_of_Xi hlam hτ').const_mul (2 * π)
  have hT'ii := intervalIntegrable_of_integrableOn_Icc hT'int
  have hTii : IntervalIntegrable (TcontFn (lamOf Δ)) volume (-π) π :=
    ((continuous_TcontFn hlam).intervalIntegrable _ _)
  have h1 := ae_comp_kMap hlam h
  have h2 : ∀ᵐ α ∂(volume.restrict (Ioc (-π) π)),
      (fun β => Ttrans Δ τ' β - TcontFn (lamOf Δ) β) α =
        -xiConv (2 * lamOf Δ) (fun β => Ttrans Δ τ' β - TcontFn (lamOf Δ) β) α := by
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    rw [ae_restrict_iff' measurableSet_Icc] at h1 ⊢
    filter_upwards [h1] with α hα hαI
    rw [xiConv_sub hlam2 hT'ii hTii]
    have e1 := (cOE_at_iff hΔ τ' α).1 (hα hαI)
    have e2 := hTeq α hαI
    linarith
  have hD0 := eq_zero_of_ae_eq_neg_xiConv hlam2 (hT'ii.sub hTii) h2
  have hae : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)),
      τ' (kMap (lamOf Δ) β) = tauCont Δ (kMap (lamOf Δ) β) := by
    have h3 : ∀ᵐ β ∂(volume.restrict (Icc (-π) π)), Ttrans Δ τ' β - TcontFn (lamOf Δ) β = 0 := by
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
      exact hD0
    filter_upwards [h3] with β hβ
    have : Ttrans Δ τ' β = Ttrans Δ (tauCont Δ) β := by
      rw [hTrho]; linarith
    unfold Ttrans at this
    have h4 : 2 * π ≠ 0 := by positivity
    exact mul_left_cancel₀ h4 this
  exact ae_eq_of_comp_kMap hlam hτ' (integrableOn_Icc_of_continuous (continuous_tauCont hΔ)) hae

end PottsDiscontinuity.Bethe
