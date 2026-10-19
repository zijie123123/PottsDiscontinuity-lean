module

public import Mathlib
public import PottsDiscontinuity.Bethe.Prop21Tau

/-!
# Complex Fourier coefficients of §4 for Proposition 2.1

`hatCoef f m = (1/2π) ∫_{-π}^{π} e^{-imα} f(α) dα` is the Fourier coefficient of the source.  This
file records the coefficient computations of §4 (done here without residues, see below):

* `hatCoef_Xi`: `Ξ̂_μ(m) = e^{-μ|m|}` (the Fourier coefficients of `Ξ_μ`, Section 4);
* `hatCoef_Rsech`: `R̂(m) = 1/(2 cosh(λ m))` (eq. (4.1), `eq:Rhat`);
* `hatCoef_PsiFn_zero`, `hatCoef_PsiFn`: `Ψ̂(0) = 0` and `Ψ̂(m) = ((-1)^m/(i m)) (1 - Ξ̂_{2λ}(m))`;
* `hatCoef_TcontFn_zero`, `hatCoef_TcontFn`: `T̂(0) = 0` and `T̂(m) = ((-1)^m/(i m)) tanh(λ|m|)`;
* `rfourier_R`, `rfourier_T`: the Fourier equations (2.2) for the explicit `R` and `T`.

*Route.*  `Ξ̂_μ(m) = e^{-μ|m|}` follows from the geometric (Poisson-kernel) series of `Ξ_μ`
instead of the contour integral of §4; `R̂` from the Poisson summation formula for the hyperbolic
secant (Fourier transform of `sech` via the Beta function) instead of the residue evaluation;
`Ψ̂` from the closed series of `Ψ` obtained by differentiating (footnote 5) instead of integration
by parts; `T̂` from the splitting `T = -α + U_λ` with `U_λ` an absolutely convergent sine series.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- The Fourier coefficient `f̂(m) = (1/2π) ∫_{-π}^{π} e^{-imα} f(α) dα` of the source (§2.1). -/
noncomputable def hatCoef (f : ℝ → ℝ) (m : ℤ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ α in (-π)..π, Complex.exp (-(I * (m : ℂ) * (α : ℂ))) * (f α : ℂ)

theorem intervalIntegrable_ofReal_pi {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-π) π) :
    IntervalIntegrable (fun x => (f x : ℂ)) volume (-π) π := by
  have hpi := Real.pi_pos
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at hf ⊢
  exact hf.ofReal

theorem hatCoef_eq {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-π) π) (m : ℤ) :
    hatCoef f m = ((2 * π : ℝ) : ℂ)⁻¹ *
      (((∫ α in (-π)..π, f α * Real.cos (m * α) : ℝ) : ℂ) -
        I * ((∫ α in (-π)..π, f α * Real.sin (m * α) : ℝ) : ℂ)) := by
  unfold hatCoef
  congr 1
  have h1 : ∀ α : ℝ, Complex.exp (-(I * (m : ℂ) * (α : ℂ))) * (f α : ℂ) =
      ((f α * Real.cos (m * α) : ℝ) : ℂ) - I * ((f α * Real.sin (m * α) : ℝ) : ℂ) := by
    intro α
    have : -(I * (m : ℂ) * (α : ℂ)) = ((-((m : ℝ) * α) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast; ring
  simp_rw [h1]
  have hc : IntervalIntegrable (fun α => f α * Real.cos (m * α)) volume (-π) π :=
    hf.mul_continuousOn (by fun_prop)
  have hs : IntervalIntegrable (fun α => f α * Real.sin (m * α)) volume (-π) π :=
    hf.mul_continuousOn (by fun_prop)
  rw [intervalIntegral.integral_sub (intervalIntegrable_ofReal_pi hc) ((intervalIntegrable_ofReal_pi hs).const_mul I),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]

theorem hatCoef_natCast {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-π) π) (n : ℕ) :
    hatCoef f (n : ℤ) = ((2 * π : ℝ) : ℂ)⁻¹ * ((cosCoeff f n : ℂ) - I * (sinCoeff f n : ℂ)) := by
  rw [hatCoef_eq hf]
  unfold cosCoeff sinCoeff
  simp only [Int.cast_natCast]

theorem hatCoef_neg_natCast {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-π) π) (n : ℕ) :
    hatCoef f (-(n : ℤ)) = ((2 * π : ℝ) : ℂ)⁻¹ * ((cosCoeff f n : ℂ) + I * (sinCoeff f n : ℂ)) := by
  rw [hatCoef_eq hf]
  unfold cosCoeff sinCoeff
  have h1 : ∀ α : ℝ, f α * Real.cos (((-(n : ℤ) : ℤ) : ℝ) * α) = f α * Real.cos (n * α) := by
    intro α; push_cast; rw [neg_mul, Real.cos_neg]
  have h2 : ∀ α : ℝ, f α * Real.sin (((-(n : ℤ) : ℤ) : ℝ) * α) = -(f α * Real.sin (n * α)) := by
    intro α; push_cast; rw [neg_mul, Real.sin_neg]; ring
  simp_rw [h1, h2]
  rw [intervalIntegral.integral_neg]
  push_cast
  ring

theorem hatCoef_trigSeries {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ) :
    hatCoef (trigSeries a₀ a b) 0 = (a₀ : ℂ) ∧
    (∀ n : ℕ, hatCoef (trigSeries a₀ a b) (((n + 1 : ℕ) : ℤ)) = ((a n : ℂ) - I * (b n : ℂ)) / 2) ∧
    (∀ n : ℕ, hatCoef (trigSeries a₀ a b) (-((n + 1 : ℕ) : ℤ)) = ((a n : ℂ) + I * (b n : ℂ)) / 2) := by
  have hpi := Real.pi_pos
  have hg : IntervalIntegrable (trigSeries a₀ a b) volume (-π) π :=
    (continuous_trigSeries ha hb a₀).intervalIntegrable _ _
  have hpi' : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  refine ⟨?_, fun n => ?_, fun n => ?_⟩
  · have := hatCoef_natCast hg 0
    simp only [Nat.cast_zero] at this
    rw [this, cosCoeff_trigSeries_zero ha hb]
    have : sinCoeff (trigSeries a₀ a b) 0 = 0 := by simp [sinCoeff]
    rw [this]
    push_cast
    field_simp
    ring
  · rw [hatCoef_natCast hg, cosCoeff_trigSeries_succ ha hb, sinCoeff_trigSeries_succ ha hb]
    push_cast
    field_simp
  · rw [hatCoef_neg_natCast hg, cosCoeff_trigSeries_succ ha hb, sinCoeff_trigSeries_succ ha hb]
    push_cast
    field_simp

theorem hatCoef_sub {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume (-π) π)
    (hg : IntervalIntegrable g volume (-π) π) (m : ℤ) :
    hatCoef (fun α => f α - g α) m = hatCoef f m - hatCoef g m := by
  rw [hatCoef_eq (hf.sub hg), hatCoef_eq hf, hatCoef_eq hg]
  have h1 : ∀ α : ℝ, (f α - g α) * Real.cos (m * α) = f α * Real.cos (m * α) - g α * Real.cos (m * α) :=
    fun α => by ring
  have h2 : ∀ α : ℝ, (f α - g α) * Real.sin (m * α) = f α * Real.sin (m * α) - g α * Real.sin (m * α) :=
    fun α => by ring
  simp_rw [h1, h2]
  rw [intervalIntegral.integral_sub (hf.mul_continuousOn (by fun_prop)) (hg.mul_continuousOn (by fun_prop)),
    intervalIntegral.integral_sub (hf.mul_continuousOn (by fun_prop)) (hg.mul_continuousOn (by fun_prop))]
  push_cast
  ring

theorem hatCoef_add {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume (-π) π)
    (hg : IntervalIntegrable g volume (-π) π) (m : ℤ) :
    hatCoef (fun α => f α + g α) m = hatCoef f m + hatCoef g m := by
  rw [hatCoef_eq (hf.add hg), hatCoef_eq hf, hatCoef_eq hg]
  have h1 : ∀ α : ℝ, (f α + g α) * Real.cos (m * α) = f α * Real.cos (m * α) + g α * Real.cos (m * α) :=
    fun α => by ring
  have h2 : ∀ α : ℝ, (f α + g α) * Real.sin (m * α) = f α * Real.sin (m * α) + g α * Real.sin (m * α) :=
    fun α => by ring
  simp_rw [h1, h2]
  rw [intervalIntegral.integral_add (hf.mul_continuousOn (by fun_prop)) (hg.mul_continuousOn (by fun_prop)),
    intervalIntegral.integral_add (hf.mul_continuousOn (by fun_prop)) (hg.mul_continuousOn (by fun_prop))]
  push_cast
  ring

/-- Case distinction on `m ∈ ℤ`: `0`, `n + 1`, `-(n + 1)`. -/
theorem int_cases_aux {P : ℤ → Prop} (h0 : P 0) (hp : ∀ n : ℕ, P ((n + 1 : ℕ) : ℤ))
    (hn : ∀ n : ℕ, P (-((n + 1 : ℕ) : ℤ))) : ∀ m : ℤ, P m := by
  intro m
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · cases k with
    | zero => simpa using h0
    | succ n => exact hp n
  · cases k with
    | zero => simpa using h0
    | succ n => exact hn n

/-- `Ξ_μ(α) = 1 + ∑ 2 e^{-μ(n+1)} cos((n+1)α)` as a trigonometric series. -/
theorem Xi_eq_trigSeries {μ : ℝ} (hμ : 0 < μ) :
    Xi μ = trigSeries 1 (fun n => 2 * Real.exp (-μ) ^ (n + 1)) (fun _ => 0) := by
  funext α
  have h := (hasSum_Xi_cos hμ α).tsum_eq
  unfold trigSeries
  simp only [zero_mul, add_zero]
  linarith

theorem summable_two_mul_exp_pow {μ : ℝ} (hμ : 0 < μ) :
    Summable (fun n : ℕ => 2 * Real.exp (-μ) ^ (n + 1)) := by
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hr1 : Real.exp (-μ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have := (summable_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-μ))
  exact this.congr fun n => by ring

/-- **Fourier coefficients of `Ξ_μ`** (§4): `Ξ̂_μ(m) = e^{-μ|m|}` for `μ > 0` and all `m ∈ ℤ`. -/
theorem hatCoef_Xi {μ : ℝ} (hμ : 0 < μ) (m : ℤ) :
    hatCoef (Xi μ) m = ((Real.exp (-(μ * |(m : ℝ)|)) : ℝ) : ℂ) := by
  have hs := summable_two_mul_exp_pow hμ
  obtain ⟨h0, hp, hn⟩ := hatCoef_trigSeries hs (summable_zero (β := ℕ)) 1
  rw [Xi_eq_trigSeries hμ]
  revert m
  refine int_cases_aux ?_ (fun n => ?_) (fun n => ?_)
  · rw [h0]; simp
  · rw [hp n]
    have : (-(μ * |(((n + 1 : ℕ) : ℤ) : ℝ)|)) = ((n + 1 : ℕ) : ℝ) * (-μ) := by
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]; ring
    rw [this, Real.exp_nat_mul]
    push_cast
    ring
  · rw [hn n]
    have : (-(μ * |((-((n + 1 : ℕ) : ℤ) : ℤ) : ℝ)|)) = ((n + 1 : ℕ) : ℝ) * (-μ) := by
      rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]; ring
    rw [this, Real.exp_nat_mul]
    push_cast
    ring

/-- **Fourier coefficients of `R`** (eq. (4.1), `eq:Rhat`): `R̂(m) = 1/(2 cosh(λ m))`. -/
theorem hatCoef_Rsech {lam : ℝ} (hlam : 0 < lam) (m : ℤ) :
    hatCoef (Rsech lam) m = ((1 / (2 * Real.cosh (lam * |(m : ℝ)|)) : ℝ) : ℂ) := by
  have hs := summable_secCoeff hlam
  obtain ⟨h0, hp, hn⟩ := hatCoef_trigSeries hs (summable_zero (β := ℕ)) (1 / 2)
  have e : Rsech lam = trigSeries (1 / 2) (secCoeff lam) (fun _ => 0) :=
    funext (Rsech_eq_trigSeries hlam)
  rw [e]
  revert m
  refine int_cases_aux ?_ (fun n => ?_) (fun n => ?_)
  · rw [h0]; simp
  · rw [hp n]
    unfold secCoeff
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    push_cast
    field_simp
    simp only [mul_zero, sub_zero]
  · rw [hn n]
    unfold secCoeff
    rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    push_cast
    field_simp
    simp only [mul_zero, add_zero]

theorem hatCoef_neg_id {m : ℤ} (hm : m ≠ 0) :
    hatCoef (fun α => -α) m = (-1 : ℂ) ^ m.natAbs / (I * (m : ℂ)) := by
  have hpi := Real.pi_pos
  have hpi' : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  have hg : IntervalIntegrable (fun β : ℝ => -β) volume (-π) π :=
    (continuous_neg).intervalIntegrable _ _
  revert m
  have key : ∀ m : ℤ, m ≠ 0 → hatCoef (fun α => -α) m = (-1 : ℂ) ^ m.natAbs / (I * (m : ℂ)) := by
    refine int_cases_aux (fun h => absurd rfl h) (fun n _ => ?_) (fun n _ => ?_)
    · rw [hatCoef_natCast hg, cosCoeff_neg_id, sinCoeff_neg_id]
      have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      simp only [Int.natAbs_natCast]
      push_cast
      field_simp
      linear_combination (-(2 * (π : ℂ) * (-1) ^ (n + 1))) * Complex.I_sq
    · rw [hatCoef_neg_natCast hg, cosCoeff_neg_id, sinCoeff_neg_id]
      have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
      push_cast
      field_simp
      linear_combination (2 * (π : ℂ) * (-1) ^ (n + 1)) * Complex.I_sq
  exact key

/-- `sawS μ` as a (sine) trigonometric series. -/
theorem sawS_eq_trigSeries (μ : ℝ) :
    sawS μ = trigSeries 0 (fun _ => 0)
      (fun n : ℕ => 2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) / ((n : ℝ) + 1)) := by
  funext α
  unfold sawS trigSeries
  simp

theorem summable_sawS_coeff {μ : ℝ} (hμ : 0 < μ) :
    Summable (fun n : ℕ => 2 * (-1 : ℝ) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) / ((n : ℝ) + 1)) := by
  refine Summable.of_norm_bounded (summable_two_mul_exp_pow hμ) (fun n => ?_)
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (two_pos : (0:ℝ) < 2), abs_of_pos (pow_pos hr _), abs_of_pos (by linarith : (0:ℝ) < (n : ℝ) + 1)]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_pos hr (n + 1)]

theorem hatCoef_sawS {μ : ℝ} (hμ : 0 < μ) {m : ℤ} (hm : m ≠ 0) :
    hatCoef (sawS μ) m = (-1 : ℂ) ^ m.natAbs / (I * (m : ℂ)) *
      ((Real.exp (-(μ * |(m : ℝ)|)) : ℝ) : ℂ) := by
  obtain ⟨_, hp, hn⟩ := hatCoef_trigSeries (summable_zero (β := ℕ)) (summable_sawS_coeff hμ) 0
  rw [sawS_eq_trigSeries]
  have key : ∀ m : ℤ, m ≠ 0 → hatCoef (trigSeries 0 (fun _ => 0)
      (fun n : ℕ => 2 * (-1) ^ (n + 1) * Real.exp (-μ) ^ (n + 1) / ((n : ℝ) + 1))) m =
      (-1 : ℂ) ^ m.natAbs / (I * (m : ℂ)) * ((Real.exp (-(μ * |(m : ℝ)|)) : ℝ) : ℂ) := by
    refine int_cases_aux (fun h => absurd rfl h) (fun n _ => ?_) (fun n _ => ?_)
    · rw [hp n]
      have e : (-(μ * |(((n + 1 : ℕ) : ℤ) : ℝ)|)) = ((n + 1 : ℕ) : ℝ) * (-μ) := by
        rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]; ring
      rw [e, Real.exp_nat_mul]
      have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      simp only [Int.natAbs_natCast]
      push_cast
      field_simp
      linear_combination (-(2 * (-1 : ℂ) ^ (n + 1) * (Complex.exp (-(μ : ℂ))) ^ (n + 1))) * Complex.I_sq
    · rw [hn n]
      have e : (-(μ * |((-((n + 1 : ℕ) : ℤ) : ℤ) : ℝ)|)) = ((n + 1 : ℕ) : ℝ) * (-μ) := by
        rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]; ring
      rw [e, Real.exp_nat_mul]
      have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
      push_cast
      field_simp
      linear_combination ((2 * (-1 : ℂ) ^ (n + 1) * (Complex.exp (-(μ : ℂ))) ^ (n + 1))) * Complex.I_sq
  exact key m hm

theorem intervalIntegrable_sawS {μ : ℝ} (hμ : 0 < μ) : IntervalIntegrable (sawS μ) volume (-π) π := by
  rw [sawS_eq_trigSeries]
  exact (continuous_trigSeries (summable_zero (β := ℕ)) (summable_sawS_coeff hμ) 0).intervalIntegrable _ _

/-- **`Ψ̂(m) = ((-1)^m/(i m)) (1 - Ξ̂_{2λ}(m))`** for `m ≠ 0` (§4). -/
theorem hatCoef_PsiFn {Δ : ℝ} (hΔ : Δ < -1) {m : ℤ} (hm : m ≠ 0) :
    hatCoef (PsiFn Δ) m =
      (-1 : ℂ) ^ m.natAbs / (I * (m : ℂ)) * (1 - hatCoef (Xi (2 * lamOf Δ)) m) := by
  have hlam2 : 0 < 2 * lamOf Δ := by linarith [lamOf_pos hΔ]
  have hg : IntervalIntegrable (fun β : ℝ => -β) volume (-π) π :=
    (continuous_neg).intervalIntegrable _ _
  have e : PsiFn Δ = fun α => -α - sawS (2 * lamOf Δ) α := funext (PsiFn_eq_neg_sub_sawS hΔ)
  rw [e, hatCoef_sub hg (intervalIntegrable_sawS hlam2), hatCoef_neg_id hm,
    hatCoef_sawS hlam2 hm, hatCoef_Xi hlam2 m]
  ring

theorem tauU_eq_trigSeries (lam : ℝ) : tauU lam = trigSeries 0 (fun _ => 0) (tauCoeff lam) := rfl

theorem hatCoef_tauU {lam : ℝ} (hlam : 0 < lam) {m : ℤ} (hm : m ≠ 0) :
    hatCoef (tauU lam) m = (-1 : ℂ) ^ m.natAbs / (I * (m : ℂ)) *
      (((Real.tanh (lam * |(m : ℝ)|) : ℝ) : ℂ) - 1) := by
  obtain ⟨_, hp, hn⟩ := hatCoef_trigSeries (summable_zero (β := ℕ)) (summable_tauCoeff hlam) 0
  rw [tauU_eq_trigSeries]
  have key : ∀ m : ℤ, m ≠ 0 → hatCoef (trigSeries 0 (fun _ => 0) (tauCoeff lam)) m =
      (-1 : ℂ) ^ m.natAbs / (I * (m : ℂ)) * (((Real.tanh (lam * |(m : ℝ)|) : ℝ) : ℂ) - 1) := by
    refine int_cases_aux (fun h => absurd rfl h) (fun n _ => ?_) (fun n _ => ?_)
    · rw [hp n]
      have e : |(((n + 1 : ℕ) : ℤ) : ℝ)| = ((n + 1 : ℕ) : ℝ) := by
        rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      rw [e]
      have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      simp only [Int.natAbs_natCast, tauCoeff]
      push_cast
      field_simp
      linear_combination (-2 * (-1 : ℂ) ^ n * (1 - Complex.tanh (↑lam * (↑n + 1)))) * Complex.I_sq
    · rw [hn n]
      have e : |((-((n + 1 : ℕ) : ℤ) : ℤ) : ℝ)| = ((n + 1 : ℕ) : ℝ) := by
        rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
      rw [e]
      have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      simp only [Int.natAbs_neg, Int.natAbs_natCast, tauCoeff]
      push_cast
      field_simp
      linear_combination (2 * (-1 : ℂ) ^ n * (1 - Complex.tanh (↑lam * (↑n + 1)))) * Complex.I_sq
  exact key m hm

/-- **`T̂(m) = ((-1)^m/(i m)) tanh(λ|m|)`** for `m ≠ 0` (§4). -/
theorem hatCoef_TcontFn {lam : ℝ} (hlam : 0 < lam) {m : ℤ} (hm : m ≠ 0) :
    hatCoef (TcontFn lam) m = (-1 : ℂ) ^ m.natAbs / (I * (m : ℂ)) *
      ((Real.tanh (lam * |(m : ℝ)|) : ℝ) : ℂ) := by
  have hg : IntervalIntegrable (fun β : ℝ => -β) volume (-π) π :=
    (continuous_neg).intervalIntegrable _ _
  have e : TcontFn lam = fun α => -α + tauU lam α := rfl
  rw [e, hatCoef_add hg ((continuous_tauU hlam).intervalIntegrable _ _), hatCoef_neg_id hm,
    hatCoef_tauU hlam hm]
  ring

/-! ### The Fourier form (2.2) of (cBE') and (cOE') -/

end PottsDiscontinuity.Bethe
