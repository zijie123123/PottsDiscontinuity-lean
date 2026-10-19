module

public import Mathlib
public import PottsDiscontinuity.Bethe.Prop21Rho

/-!
# Proposition 2.1: positivity of `ρ` and the uniform lower bound `m_ρ`

* `rho_pos`: `ρ_Δ(x) > 0` for every `Δ < -1` and every `x` (all terms of the sum in (2.1) are
  positive and `k' = Ξ_λ > 0`);
* `rho_uniform_lower_bound` (the constant `m_ρ > 0` used in Section 2.2, the infimum of `ρ`
  over `x ∈ [-π, π]` and `Δ ≤ Δ₀`): for `Δ₀ < -1` there is `m_ρ > 0`
  with `ρ_Δ(x) ≥ m_ρ` for all `Δ ≤ Δ₀` and `x ∈ [-π, π]`.  The proof splits at `λ = 3`: for
  `λ ≥ 3` the cosine series `R = 1/2 + ∑ cos(mα)/cosh(λ m)` gives `R ≥ 1/4`; for `λ₀ ≤ λ ≤ 3`
  only the term `j = 0` of the periodised sech is kept; and `k' = Ξ_λ ≤ (e^λ+1)/(e^λ-1) ≤
  (e^{λ₀}+1)/(e^{λ₀}-1)`;
* `rho_uniform_upper_bound`: for `Δ₀ < -1`, `ρ_Δ(x) ≤ M_ρ` for all `Δ ≤ Δ₀` (from `R ≤ 1/2 + 2/(e^λ-1)`
  and `k' = Ξ_λ ≥ (e^λ-1)/(e^λ+1)`).
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-! ### Positivity of `ρ` -/

theorem Rsech_pos {lam : ℝ} (hlam : 0 < lam) (α : ℝ) : 0 < Rsech lam α := by
  unfold Rsech
  have hs := summable_sech_periodic hlam α
  have : 0 < ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam)) :=
    hs.tsum_pos (fun j => by positivity) 0 (by positivity)
  positivity

/-- **Strict positivity of `ρ`** (Proposition 2.1): `ρ_Δ(x) > 0`. -/
theorem rho_pos {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) : 0 < rho Δ x := by
  have hlam := lamOf_pos hΔ
  rw [rho_eq hΔ]
  have := Xi_pos hlam (kInv (lamOf Δ) x)
  have := Rsech_pos hlam (kInv (lamOf Δ) x)
  positivity

/-! ### The uniform lower bound for `Δ ≤ Δ₀ < -1` -/

/-- The cosine-series form of `R` gives `R ≥ 1/2 - 2/(e^λ - 1)`. -/
theorem Rsech_ge_half_sub {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    1 / 2 - 2 * Real.exp (-lam) / (1 - Real.exp (-lam)) ≤ Rsech lam α := by
  have hr : 0 < Real.exp (-lam) := Real.exp_pos _
  have hr1 : Real.exp (-lam) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  rw [Rsech_eq_trigSeries hlam]
  unfold trigSeries
  have hb : ∀ n : ℕ, |trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α| ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
    intro n
    have := abs_trigTerm_le (secCoeff lam) (fun _ => (0 : ℝ)) n α
    have h2 := secCoeff_le hlam n
    have h3 := secCoeff_pos lam n
    simp only [abs_zero, add_zero] at this
    rw [abs_of_pos h3] at this
    linarith
  have hgeo : HasSum (fun n : ℕ => 2 * Real.exp (-lam) ^ (n + 1))
      (2 * Real.exp (-lam) / (1 - Real.exp (-lam))) := by
    have := (hasSum_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-lam))
    convert this using 1
    · funext n; ring
    · field_simp
  have hsum : Summable (fun n => trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α) :=
    (hasSum_trigTerm (summable_secCoeff hlam) summable_zero α).summable
  have h1 : |∑' n, trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α| ≤
      2 * Real.exp (-lam) / (1 - Real.exp (-lam)) := by
    calc |∑' n, trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α|
        ≤ ∑' n, |trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α| := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum.norm
      _ ≤ ∑' n : ℕ, 2 * Real.exp (-lam) ^ (n + 1) :=
          hsum.abs.tsum_le_tsum hb hgeo.summable
      _ = 2 * Real.exp (-lam) / (1 - Real.exp (-lam)) := hgeo.tsum_eq
  have h2 := neg_abs_le (∑' n, trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α)
  show 1 / 2 - 2 * Real.exp (-lam) / (1 - Real.exp (-lam)) ≤
    1 / 2 + ∑' n, trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α
  linarith


theorem exp_neg_three_le : Real.exp (-3) ≤ 1 / 9 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp (-3) = (Real.exp 1)⁻¹ ^ 3 := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h2]
  have h3 : 0 < Real.exp 1 := Real.exp_pos 1
  have h4 : (Real.exp 1)⁻¹ ≤ 10 / 27 := by
    rw [inv_eq_one_div]
    have : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith
    calc 1 / Real.exp 1 ≤ 1 / (27 / 10) := one_div_le_one_div_of_le (by norm_num) this
      _ = 10 / 27 := by norm_num
  have h5 : 0 ≤ (Real.exp 1)⁻¹ := by positivity
  calc (Real.exp 1)⁻¹ ^ 3 ≤ (10 / 27) ^ 3 := by gcongr
    _ ≤ 1 / 9 := by norm_num

/-- For `λ ≥ 3`, `R ≥ 1/4` (the cosine series has `∑ 1/cosh(λ m) ≤ 1/4`). -/
theorem Rsech_ge_quarter {lam : ℝ} (hlam : 3 ≤ lam) (α : ℝ) : 1 / 4 ≤ Rsech lam α := by
  have hl : 0 < lam := by linarith
  have h := Rsech_ge_half_sub hl α
  have hq : Real.exp (-lam) ≤ 1 / 9 := by
    refine le_trans (Real.exp_le_exp.2 (by linarith)) exp_neg_three_le
  have hq0 : 0 < Real.exp (-lam) := Real.exp_pos _
  have h1 : 2 * Real.exp (-lam) / (1 - Real.exp (-lam)) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

/-- For `λ₀ ≤ λ ≤ 3`, `|α| ≤ π`: `R(α) ≥ (π/6) / cosh(π²/(2λ₀))` (keep only the term `j = 0`). -/
theorem Rsech_ge_of_le_three {lam lam0 : ℝ} (h0 : 0 < lam0) (h1 : lam0 ≤ lam) (h2 : lam ≤ 3)
    {α : ℝ} (hα : |α| ≤ π) :
    (π / 6) * (1 / Real.cosh (π ^ 2 / (2 * lam0))) ≤ Rsech lam α := by
  have hpi := Real.pi_pos
  have hl : 0 < lam := by linarith
  unfold Rsech
  have hs := summable_sech_periodic hl α
  have hterm : 1 / Real.cosh (π * (2 * π * ((0 : ℤ) : ℝ) + α) / (2 * lam)) ≤
      ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam)) :=
    hs.le_tsum 0 (fun j _ => by positivity)
  have hc : Real.cosh (π * (2 * π * ((0 : ℤ) : ℝ) + α) / (2 * lam)) ≤ Real.cosh (π ^ 2 / (2 * lam0)) := by
    rw [Real.cosh_le_cosh]
    simp only [Int.cast_zero, mul_zero, zero_add]
    have e : |π * α / (2 * lam)| = π * |α| / (2 * lam) := by
      rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos (by positivity : (0:ℝ) < 2 * lam)]
    have e1 : π * |α| / (2 * lam) ≤ π * π / (2 * lam) := by gcongr
    have e2 : π * π / (2 * lam) ≤ π ^ 2 / (2 * lam0) := by
      rw [sq]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    rw [e, abs_of_pos (by positivity : (0:ℝ) < π ^ 2 / (2 * lam0))]
    exact e1.trans e2
  have hcpos : 0 < Real.cosh (π * (2 * π * ((0 : ℤ) : ℝ) + α) / (2 * lam)) := Real.cosh_pos _
  have h3 : 1 / Real.cosh (π ^ 2 / (2 * lam0)) ≤
      1 / Real.cosh (π * (2 * π * ((0 : ℤ) : ℝ) + α) / (2 * lam)) :=
    one_div_le_one_div_of_le hcpos hc
  have h4 : π / 6 ≤ π / (2 * lam) := by
    apply div_le_div_of_nonneg_left hpi.le (by positivity); linarith
  calc π / 6 * (1 / Real.cosh (π ^ 2 / (2 * lam0)))
      ≤ π / (2 * lam) * (1 / Real.cosh (π ^ 2 / (2 * lam0))) := by gcongr
    _ ≤ π / (2 * lam) * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam)) := by
        gcongr; exact h3.trans hterm

/-- The uniform lower bound for `R`: for `λ ≥ λ₀ > 0` and `|α| ≤ π`. -/
theorem Rsech_lower_bound {lam0 : ℝ} (h0 : 0 < lam0) {lam : ℝ} (h1 : lam0 ≤ lam) {α : ℝ}
    (hα : |α| ≤ π) :
    min (1 / 4) ((π / 6) * (1 / Real.cosh (π ^ 2 / (2 * lam0)))) ≤ Rsech lam α := by
  rcases le_total 3 lam with h | h
  · exact (min_le_left _ _).trans (Rsech_ge_quarter h α)
  · exact (min_le_right _ _).trans (Rsech_ge_of_le_three h0 h1 h hα)

theorem Xi_le_exp_ratio {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Xi lam α ≤ (Real.exp lam + 1) / (Real.exp lam - 1) := by
  have h := (Xi_bounds hlam α).2
  refine h.trans (le_of_eq ?_)
  have hE : 1 < Real.exp lam := by simpa using hlam
  have hE0 : Real.exp lam ≠ 0 := (Real.exp_pos lam).ne'
  have hE1 : Real.exp lam - 1 ≠ 0 := by linarith
  rw [Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  have hd : (Real.exp lam + (Real.exp lam)⁻¹) / 2 - 1 ≠ 0 := by
    have : (Real.exp lam + (Real.exp lam)⁻¹) / 2 - 1 = (Real.exp lam - 1) ^ 2 / (2 * Real.exp lam) := by
      field_simp; ring
    rw [this]; positivity
  rw [div_eq_div_iff hd hE1]
  field_simp
  ring

theorem exp_ratio_mono {lam0 lam : ℝ} (h0 : 0 < lam0) (h : lam0 ≤ lam) :
    (Real.exp lam + 1) / (Real.exp lam - 1) ≤ (Real.exp lam0 + 1) / (Real.exp lam0 - 1) := by
  have hE0 : 1 < Real.exp lam0 := by simpa using h0
  have hE : Real.exp lam0 ≤ Real.exp lam := Real.exp_le_exp.2 h
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem lamOf_mono {Δ Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) (h : Δ ≤ Δ₀) : lamOf Δ₀ ≤ lamOf Δ := by
  have hΔ : Δ < -1 := lt_of_le_of_lt h hΔ₀
  have h1 := lamOf_pos hΔ
  have h2 := lamOf_pos hΔ₀
  have h3 := cosh_lamOf hΔ
  have h4 := cosh_lamOf hΔ₀
  have : Real.cosh (lamOf Δ₀) ≤ Real.cosh (lamOf Δ) := by rw [h3, h4]; linarith
  rw [Real.cosh_le_cosh, abs_of_pos h1, abs_of_pos h2] at this
  exact this

/-- **Uniform lower bound** (the constant `m_ρ` of Section 2.2): for every `Δ₀ < -1` there is
`m_ρ > 0` with `ρ_Δ(x) ≥ m_ρ` for all `Δ ≤ Δ₀` and all `x ∈ [-π, π]`; an explicit constant is
given. -/
theorem rho_uniform_lower_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ m : ℝ, 0 < m ∧ ∀ Δ : ℝ, Δ ≤ Δ₀ → ∀ x ∈ Icc (-π) π, m ≤ rho Δ x := by
  have hpi := Real.pi_pos
  set lam0 := lamOf Δ₀ with hlam0
  have h0 : 0 < lam0 := lamOf_pos hΔ₀
  have hE0 : 1 < Real.exp lam0 := by simpa using h0
  set X0 := (Real.exp lam0 + 1) / (Real.exp lam0 - 1) with hX0
  have hX0pos : 0 < X0 := by rw [hX0]; apply div_pos <;> linarith
  set mR := min (1 / 4) ((π / 6) * (1 / Real.cosh (π ^ 2 / (2 * lam0)))) with hmR
  have hmR : 0 < mR := by
    rw [hmR]; apply lt_min (by norm_num); positivity
  refine ⟨mR / (2 * π * X0), by positivity, fun Δ hΔ x hx => ?_⟩
  have hΔ1 : Δ < -1 := lt_of_le_of_lt hΔ hΔ₀
  have hlam := lamOf_pos hΔ1
  have hle := lamOf_mono hΔ₀ hΔ
  have hα := kInv_mem_Icc hlam hx
  have habs : |kInv (lamOf Δ) x| ≤ π := abs_le.2 ⟨hα.1, hα.2⟩
  rw [rho_eq hΔ1]
  have hR := Rsech_lower_bound h0 hle habs
  have hX := Xi_pos hlam (kInv (lamOf Δ) x)
  have hXle : Xi (lamOf Δ) (kInv (lamOf Δ) x) ≤ X0 :=
    (Xi_le_exp_ratio hlam _).trans (exp_ratio_mono h0 hle)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc mR * (2 * π * Xi (lamOf Δ) (kInv (lamOf Δ) x)) ≤ Rsech (lamOf Δ) (kInv (lamOf Δ) x) * (2 * π * X0) := by
        have := Rsech_pos hlam (kInv (lamOf Δ) x)
        nlinarith [mul_le_mul hR (mul_le_mul_of_nonneg_left hXle (by positivity : (0:ℝ) ≤ 2 * π))
          (by positivity) this.le]
    _ = _ := by ring


/-! ### A uniform upper bound -/

/-- The cosine-series form of `R` gives `R ≤ 1/2 + 2/(e^λ - 1)`. -/
theorem Rsech_le_half_add {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Rsech lam α ≤ 1 / 2 + 2 * Real.exp (-lam) / (1 - Real.exp (-lam)) := by
  have hr : 0 < Real.exp (-lam) := Real.exp_pos _
  have hr1 : Real.exp (-lam) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  rw [Rsech_eq_trigSeries hlam]
  unfold trigSeries
  have hb : ∀ n : ℕ, |trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α| ≤ 2 * Real.exp (-lam) ^ (n + 1) := by
    intro n
    have := abs_trigTerm_le (secCoeff lam) (fun _ => (0 : ℝ)) n α
    have h2 := secCoeff_le hlam n
    have h3 := secCoeff_pos lam n
    simp only [abs_zero, add_zero] at this
    rw [abs_of_pos h3] at this
    linarith
  have hgeo : HasSum (fun n : ℕ => 2 * Real.exp (-lam) ^ (n + 1))
      (2 * Real.exp (-lam) / (1 - Real.exp (-lam))) := by
    have := (hasSum_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-lam))
    convert this using 1
    · funext n; ring
    · field_simp
  have hsum : Summable (fun n => trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α) :=
    (hasSum_trigTerm (summable_secCoeff hlam) summable_zero α).summable
  have h1 : |∑' n, trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α| ≤
      2 * Real.exp (-lam) / (1 - Real.exp (-lam)) := by
    calc |∑' n, trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α|
        ≤ ∑' n, |trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α| := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum.norm
      _ ≤ ∑' n : ℕ, 2 * Real.exp (-lam) ^ (n + 1) :=
          hsum.abs.tsum_le_tsum hb hgeo.summable
      _ = 2 * Real.exp (-lam) / (1 - Real.exp (-lam)) := hgeo.tsum_eq
  have h2 := le_abs_self (∑' n, trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α)
  show 1 / 2 + ∑' n, trigTerm (secCoeff lam) (fun _ => (0 : ℝ)) n α ≤
    1 / 2 + 2 * Real.exp (-lam) / (1 - Real.exp (-lam))
  linarith

theorem Xi_ge_exp_ratio {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    (Real.exp lam - 1) / (Real.exp lam + 1) ≤ Xi lam α := by
  have h := (Xi_bounds hlam α).1
  refine le_trans (le_of_eq ?_) h
  have hE : 1 < Real.exp lam := by simpa using hlam
  have hE0 : Real.exp lam ≠ 0 := (Real.exp_pos lam).ne'
  have hE1 : Real.exp lam + 1 ≠ 0 := by linarith
  rw [Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  have hd : (Real.exp lam + (Real.exp lam)⁻¹) / 2 + 1 ≠ 0 := by
    have : (Real.exp lam + (Real.exp lam)⁻¹) / 2 + 1 = (Real.exp lam + 1) ^ 2 / (2 * Real.exp lam) := by
      field_simp; ring
    rw [this]; positivity
  rw [div_eq_div_iff hE1 hd]
  field_simp
  ring

theorem exp_ratio_mono' {lam0 lam : ℝ} (h0 : 0 < lam0) (h : lam0 ≤ lam) :
    (Real.exp lam0 - 1) / (Real.exp lam0 + 1) ≤ (Real.exp lam - 1) / (Real.exp lam + 1) := by
  have hE0 : 1 < Real.exp lam0 := by simpa using h0
  have hE : Real.exp lam0 ≤ Real.exp lam := Real.exp_le_exp.2 h
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Uniform upper bound**: for every `Δ₀ < -1` there is `M_ρ` with `ρ_Δ(x) ≤ M_ρ` for all
`Δ ≤ Δ₀` and all `x ∈ [-π, π]` (used for `ρ` bounded above uniformly in `Δ ≤ Δ₀`). -/
theorem rho_uniform_upper_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ M : ℝ, ∀ Δ : ℝ, Δ ≤ Δ₀ → ∀ x : ℝ, rho Δ x ≤ M := by
  have hpi := Real.pi_pos
  set lam0 := lamOf Δ₀ with hlam0
  have h0 : 0 < lam0 := lamOf_pos hΔ₀
  have hE0 : 1 < Real.exp lam0 := by simpa using h0
  have hq0 : 0 < Real.exp (-lam0) := Real.exp_pos _
  have hq1 : Real.exp (-lam0) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  set Y0 := (Real.exp lam0 - 1) / (Real.exp lam0 + 1) with hY0
  have hY0pos : 0 < Y0 := by rw [hY0]; apply div_pos <;> linarith
  set B := 1 / 2 + 2 * Real.exp (-lam0) / (1 - Real.exp (-lam0)) with hB
  have hBpos : 0 < B := by
    rw [hB]; have : 0 < 1 - Real.exp (-lam0) := by linarith
    positivity
  refine ⟨B / (2 * π * Y0), fun Δ hΔ x => ?_⟩
  have hΔ1 : Δ < -1 := lt_of_le_of_lt hΔ hΔ₀
  have hlam := lamOf_pos hΔ1
  have hle := lamOf_mono hΔ₀ hΔ
  rw [rho_eq hΔ1]
  have hX := Xi_pos hlam (kInv (lamOf Δ) x)
  have hR := Rsech_le_half_add hlam (kInv (lamOf Δ) x)
  have hRq : 1 / 2 + 2 * Real.exp (-(lamOf Δ)) / (1 - Real.exp (-(lamOf Δ))) ≤ B := by
    rw [hB]
    have hq : Real.exp (-(lamOf Δ)) ≤ Real.exp (-lam0) := Real.exp_le_exp.2 (by linarith)
    have hqpos : 0 < Real.exp (-(lamOf Δ)) := Real.exp_pos _
    have hqlt : Real.exp (-(lamOf Δ)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    have : 2 * Real.exp (-(lamOf Δ)) / (1 - Real.exp (-(lamOf Δ))) ≤
        2 * Real.exp (-lam0) / (1 - Real.exp (-lam0)) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith
  have hY : Y0 ≤ Xi (lamOf Δ) (kInv (lamOf Δ) x) :=
    (exp_ratio_mono' h0 hle).trans (Xi_ge_exp_ratio hlam _)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hRpos := Rsech_pos hlam (kInv (lamOf Δ) x)
  nlinarith [mul_le_mul (hR.trans hRq) (mul_le_mul_of_nonneg_left hY (by positivity : (0:ℝ) ≤ 2 * π))
    (by positivity) hBpos.le]

end PottsDiscontinuity.Bethe
