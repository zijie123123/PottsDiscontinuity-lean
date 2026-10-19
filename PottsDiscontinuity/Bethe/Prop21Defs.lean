module

public import Mathlib
public import PottsDiscontinuity.Bethe.ThetaK
public import PottsDiscontinuity.Bethe.FourierPoisson

/-!
# Proposition 2.1: the equations (cBE_Δ), (cOE_Δ) and the change of variables `x = k(α)`

Source: arXiv:1611.09877v2, §2.1 (equations (cBE_Δ), (cOE_Δ) and the proof of Proposition 2.1).

* `d1Theta`, `d2Theta`: the partial derivatives `∂₁Θ`, `∂₂Θ` of `theta`;
* `cBEop`, `IsCBESolution`: the equation (cBE_Δ); `cOEop`, `IsCOESolution`: the equation (cOE_Δ);
* `kInv`: explicit inverse of `kMap` (`kMap_kInv`, `kInv_kMap`);
* `Rtrans`, `Ttrans`, `PsiFn`: `R = 2π ρ(k) k'`, `T = 2π τ(k)`, `Ψ = (Θ(k·,-π) + Θ(k·,π))/2`;
* `isCBESolution_iff`, `isCOESolution_iff`: the change of variables turns (cBE), (cOE) into
  (cBE'): `R + (1/2π) Ξ_{2λ} * R = Ξ_λ` and (cOE'): `T + (1/2π) Ξ_{2λ} * T = Ψ` on `[-π, π]`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- The inverse `x ↦ α` of `kMap lam` (explicit closed form):
`k_λ^{-1}(x) = x - 2 arctan (sin x / (e^λ + cos x))`. -/
noncomputable def kInv (lam x : ℝ) : ℝ :=
  x - 2 * Real.arctan (Real.sin x / (Real.exp lam + Real.cos x))

theorem exp_add_cos_pos {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : 0 < Real.exp lam + Real.cos x := by
  have := Real.add_one_lt_exp hlam.ne'
  have := Real.neg_one_le_cos x
  linarith

theorem continuous_kInv {lam : ℝ} (hlam : 0 < lam) : Continuous (kInv lam) := by
  unfold kInv
  refine continuous_id.sub (continuous_const.mul (Real.continuous_arctan.comp ?_))
  exact Real.continuous_sin.div (continuous_const.add Real.continuous_cos)
    (fun x => (exp_add_cos_pos hlam x).ne')

theorem analyticAt_kInv {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : AnalyticAt ℝ (kInv lam) x := by
  have hq : AnalyticAt ℝ (fun y => Real.sin y / (Real.exp lam + Real.cos y)) x :=
    Real.analyticAt_sin.div (analyticAt_const.add Real.analyticAt_cos) (exp_add_cos_pos hlam x).ne'
  exact analyticAt_id.sub (analyticAt_const.mul ((analyticAt_real_arctan _).comp hq))

theorem exp_I_mul_kInv {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    Complex.exp (I * (kInv lam x : ℂ)) =
      (Complex.exp (I * x) * (Real.exp lam : ℂ) + 1) / ((Real.exp lam : ℂ) + Complex.exp (I * x)) := by
  have ha : 0 < Real.exp lam + Real.cos x := exp_add_cos_pos hlam x
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sin x / (Real.exp lam + Real.cos x) := ⟨_, rfl⟩
  have hk : kInv lam x = x - 2 * Real.arctan t := by rw [ht]; rfl
  have ha' : ((Real.exp lam : ℂ) + (Real.cos x : ℂ)) ≠ 0 := by exact_mod_cast ha.ne'
  have hts' : t * (Real.exp lam + Real.cos x) = Real.sin x := by
    rw [ht]; field_simp
  have hts : (t : ℂ) * ((Real.exp lam : ℂ) + (Real.cos x : ℂ)) = (Real.sin x : ℂ) := by
    exact_mod_cast hts'
  have hu : Complex.exp (I * x) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * I := exp_I_mul_ofReal x
  have hub : Complex.exp (-(I * x)) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * I :=
    exp_neg_I_mul_ofReal x
  have h1 : Complex.exp (I * (kInv lam x : ℂ)) = Complex.exp (I * x) *
      (Complex.exp (((2 * Real.arctan t : ℝ) : ℂ) * I))⁻¹ := by
    rw [← Complex.exp_neg, ← Complex.exp_add, hk]
    congr 1
    push_cast
    ring
  rw [h1, exp_two_arctan_mul_I, inv_div]
  have hE1 : (Real.exp lam : ℂ) + Complex.exp (I * x) =
      ((Real.exp lam : ℂ) + (Real.cos x : ℂ)) * (1 + (t : ℂ) * I) := by
    rw [hu]; linear_combination (-I) * hts
  have hE2 : (Real.exp lam : ℂ) + Complex.exp (-(I * x)) =
      ((Real.exp lam : ℂ) + (Real.cos x : ℂ)) * (1 - (t : ℂ) * I) := by
    rw [hub]; linear_combination (I) * hts
  have huu : Complex.exp (I * x) * Complex.exp (-(I * x)) = 1 := by
    rw [← Complex.exp_add]; simp
  have hne1 : (1 - (t : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hne2 : (1 + (t : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hne3 : (Real.exp lam : ℂ) + Complex.exp (I * x) ≠ 0 := by
    rw [hE1]; exact mul_ne_zero ha' hne2
  have h3 : (1 - (t : ℂ) * I) / (1 + (t : ℂ) * I) =
      ((Real.exp lam : ℂ) + Complex.exp (-(I * x))) / ((Real.exp lam : ℂ) + Complex.exp (I * x)) := by
    rw [hE1, hE2]
    field_simp
  rw [h3, mul_div_assoc', div_left_inj' hne3]
  linear_combination huu

theorem kMap_kInv {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : kMap lam (kInv lam x) = x := by
  have key : (fun x => kMap lam (kInv lam x)) = fun x => x := by
    refine eq_of_exp_eq (X := ℝ) ?_ continuous_id ?_ 0 ?_
    · exact (continuous_kMap hlam).comp (continuous_kInv hlam)
    · intro x
      have hE : (1 : ℝ) < Real.exp lam := by simpa using hlam
      have hw : ‖Complex.exp (I * (x : ℂ))‖ = 1 := norm_exp_I_mul' x
      have hw0 : Complex.exp (I * (x : ℂ)) ≠ 0 := Complex.exp_ne_zero _
      have hE2 : (Real.exp lam : ℂ) ^ 2 - 1 ≠ 0 := by
        have : (Real.exp lam : ℂ) ^ 2 - 1 = (((Real.exp lam ^ 2 - 1 : ℝ)) : ℂ) := by push_cast; ring
        rw [this]
        exact Complex.ofReal_ne_zero.mpr (by nlinarith)
      have hne3 : (Real.exp lam : ℂ) + Complex.exp (I * x) ≠ 0 := by
        intro h
        have : (Real.exp lam : ℂ) = -Complex.exp (I * x) := by linear_combination h
        have h2 : ‖(Real.exp lam : ℂ)‖ = ‖Complex.exp (I * (x : ℂ))‖ := by
          rw [this, norm_neg]
        rw [hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h2
        linarith
      show Complex.exp ((kMap lam (kInv lam x) : ℂ) * I) = Complex.exp ((x : ℂ) * I)
      rw [mul_comm, exp_I_mul_kMap_unit hlam, exp_I_mul_kInv hlam x, mul_comm _ I]
      set u := Complex.exp (I * x)
      set E : ℂ := (Real.exp lam : ℂ)
      have hne3' : E + u ≠ 0 := hne3
      have : E - (u * E + 1) / (E + u) = (E ^ 2 - 1) / (E + u) := by
        field_simp; ring
      have h2 : E * ((u * E + 1) / (E + u)) - 1 = u * (E ^ 2 - 1) / (E + u) := by
        field_simp; ring
      rw [h2, this]
      field_simp
    · simp [kInv, kMap]
  exact congrFun key x


theorem kInv_kMap {lam : ℝ} (hlam : 0 < lam) (α : ℝ) : kInv lam (kMap lam α) = α :=
  (strictMono_kMap hlam).injective (kMap_kInv hlam (kMap lam α))

theorem kInv_eq_of_kMap_eq {lam : ℝ} (hlam : 0 < lam) {α x : ℝ} (h : kMap lam α = x) :
    kInv lam x = α := by
  rw [← h]; exact kInv_kMap hlam α

theorem kInv_mem_Icc {lam : ℝ} (hlam : 0 < lam) {x : ℝ} (hx : x ∈ Icc (-π) π) :
    kInv lam x ∈ Icc (-π) π := by
  have hm := strictMono_kMap hlam
  have h := kMap_kInv hlam x
  constructor
  · by_contra hlt
    have := hm (not_le.mp hlt)
    rw [h, kMap_neg_pi] at this
    linarith [hx.1]
  · by_contra hlt
    have := hm (not_le.mp hlt)
    rw [h, kMap_pi] at this
    linarith [hx.2]

theorem kMap_mem_Icc {lam : ℝ} (hlam : 0 < lam) {α : ℝ} (hα : α ∈ Icc (-π) π) :
    kMap lam α ∈ Icc (-π) π := mapsTo_kMap hlam hα

/-! ### The operators of (cBE) and (cOE) -/

/-- `∂₁Θ_Δ(x, y)`, the partial derivative of the Bethe phase in its first variable. -/
noncomputable def d1Theta (Δ x y : ℝ) : ℝ := deriv (fun s => theta Δ s y) x

/-- `∂₂Θ_Δ(x, y)`, the partial derivative of the Bethe phase in its second variable. -/
noncomputable def d2Theta (Δ x y : ℝ) : ℝ := deriv (fun t => theta Δ x t) y

/-- The right-hand side of (cBE_Δ): `1 + ∫_{-π}^{π} ∂₁Θ(x,y) ρ(y) dy`. -/
noncomputable def cBEop (Δ : ℝ) (ρ : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + ∫ y in (-π)..π, d1Theta Δ x y * ρ y

/-- `ρ` solves (cBE_Δ): `2π ρ(x) = 1 + ∫_{-π}^{π} ∂₁Θ(x,y) ρ(y) dy` for all `x ∈ [-π, π]`. -/
def IsCBESolution (Δ : ℝ) (ρ : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc (-π) π, 2 * π * ρ x = cBEop Δ ρ x

/-- The right-hand side of (cOE_Δ):
`(Θ(x,-π) + Θ(x,π))/2 - ∫_{-π}^{π} ∂₂Θ(x,y) τ(y) dy`. -/
noncomputable def cOEop (Δ : ℝ) (τ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (theta Δ x (-π) + theta Δ x π) / 2 - ∫ y in (-π)..π, d2Theta Δ x y * τ y

/-- `τ` solves (cOE_Δ): `2π τ(x) = (Θ(x,-π)+Θ(x,π))/2 - ∫_{-π}^{π} ∂₂Θ(x,y) τ(y) dy` for all
`x ∈ [-π, π]`. -/
def IsCOESolution (Δ : ℝ) (τ : ℝ → ℝ) : Prop :=
  ∀ x ∈ Icc (-π) π, 2 * π * τ x = cOEop Δ τ x

/-! ### The change of variables `x = k(α)` -/

/-- `R(α) = 2π ρ(k(α)) k'(α)`. -/
noncomputable def Rtrans (Δ : ℝ) (ρ : ℝ → ℝ) (α : ℝ) : ℝ :=
  2 * π * ρ (kMap (lamOf Δ) α) * deriv (kMap (lamOf Δ)) α

/-- `T(α) = 2π τ(k(α))`. -/
noncomputable def Ttrans (Δ : ℝ) (τ : ℝ → ℝ) (α : ℝ) : ℝ :=
  2 * π * τ (kMap (lamOf Δ) α)

/-- `Ψ(α) = (Θ(k(α),-π) + Θ(k(α),π))/2`. -/
noncomputable def PsiFn (Δ : ℝ) (α : ℝ) : ℝ :=
  (theta Δ (kMap (lamOf Δ) α) (-π) + theta Δ (kMap (lamOf Δ) α) π) / 2

theorem Rtrans_eq {Δ : ℝ} (hΔ : Δ < -1) (ρ : ℝ → ℝ) (α : ℝ) :
    Rtrans Δ ρ α = 2 * π * ρ (kMap (lamOf Δ) α) * Xi (lamOf Δ) α := by
  rw [Rtrans, deriv_kMap (lamOf_pos hΔ)]

theorem integral_Icc_comp_kMap {lam : ℝ} (hlam : 0 < lam) (g : ℝ → ℝ) :
    ∫ y in (-π)..π, g y = ∫ β in (-π)..π, Xi lam β * g (kMap lam β) := by
  have hpi := Real.pi_pos
  have himg : kMap lam '' Icc (-π) π = Icc (-π) π := (bijOn_kMap hlam).image_eq
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Icc (-π) π) (f := kMap lam)
    (f' := Xi lam) measurableSet_Icc (fun x _ => (hasDerivAt_kMap hlam x).hasDerivWithinAt)
    (strictMono_kMap hlam).injective.injOn g
  rw [himg] at hcov
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc, hcov]
  refine setIntegral_congr_fun measurableSet_Icc fun β _ => ?_
  simp only [smul_eq_mul]
  rw [abs_of_pos (Xi_pos hlam β)]


/-- Change of variables `x = k(α)` in (cBE): for every function `ρ` and every `α`,
`cBEop ρ (k α) = 1 - (1/(2π Ξ_λ(α))) ∫_{-π}^{π} Ξ_{2λ}(α-β) (2π ρ(k β) Ξ_λ(β)) dβ`. -/
theorem cBEop_kMap {Δ : ℝ} (hΔ : Δ < -1) (ρ : ℝ → ℝ) (α : ℝ) :
    cBEop Δ ρ (kMap (lamOf Δ) α) =
      1 - (2 * π * Xi (lamOf Δ) α)⁻¹ *
        ∫ β in (-π)..π, Xi (2 * lamOf Δ) (α - β) * (2 * π * ρ (kMap (lamOf Δ) β) * Xi (lamOf Δ) β) := by
  have hlam := lamOf_pos hΔ
  have hcosh := cosh_lamOf hΔ
  have hpi := Real.pi_pos
  have hXa := Xi_pos hlam α
  unfold cBEop
  rw [integral_Icc_comp_kMap hlam]
  have h1 : ∀ β : ℝ, Xi (lamOf Δ) β * (d1Theta Δ (kMap (lamOf Δ) α) (kMap (lamOf Δ) β) * ρ (kMap (lamOf Δ) β)) =
      -((2 * π * Xi (lamOf Δ) α)⁻¹ *
        (Xi (2 * lamOf Δ) (α - β) * (2 * π * ρ (kMap (lamOf Δ) β) * Xi (lamOf Δ) β))) := by
    intro β
    rw [d1Theta, deriv_theta_left_kMap hlam hcosh α β]
    field_simp
  simp_rw [h1]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  ring

/-- Change of variables `x = k(α)` in (cOE): for every function `τ` and every `α`,
`cOEop τ (k α) = Ψ(α) - ∫_{-π}^{π} Ξ_{2λ}(α-β) τ(k β) dβ`. -/
theorem cOEop_kMap {Δ : ℝ} (hΔ : Δ < -1) (τ : ℝ → ℝ) (α : ℝ) :
    cOEop Δ τ (kMap (lamOf Δ) α) =
      PsiFn Δ α - ∫ β in (-π)..π, Xi (2 * lamOf Δ) (α - β) * τ (kMap (lamOf Δ) β) := by
  have hlam := lamOf_pos hΔ
  have hcosh := cosh_lamOf hΔ
  have hpi := Real.pi_pos
  unfold cOEop PsiFn
  rw [integral_Icc_comp_kMap hlam]
  have h1 : ∀ β : ℝ, Xi (lamOf Δ) β * (d2Theta Δ (kMap (lamOf Δ) α) (kMap (lamOf Δ) β) * τ (kMap (lamOf Δ) β)) =
      Xi (2 * lamOf Δ) (α - β) * τ (kMap (lamOf Δ) β) := by
    intro β
    have hXb := Xi_pos hlam β
    rw [d2Theta, deriv_theta_right_kMap hlam hcosh α β]
    field_simp
  simp_rw [h1]


theorem xiConv_Rtrans {Δ : ℝ} (hΔ : Δ < -1) (ρ : ℝ → ℝ) (α : ℝ) :
    xiConv (2 * lamOf Δ) (Rtrans Δ ρ) α =
      (2 * π)⁻¹ * ∫ β in (-π)..π,
        Xi (2 * lamOf Δ) (α - β) * (2 * π * ρ (kMap (lamOf Δ) β) * Xi (lamOf Δ) β) := by
  have : Rtrans Δ ρ = fun β => 2 * π * ρ (kMap (lamOf Δ) β) * Xi (lamOf Δ) β :=
    funext (Rtrans_eq hΔ ρ)
  rw [xiConv, this]

theorem xiConv_Ttrans {Δ : ℝ} (τ : ℝ → ℝ) (α : ℝ) :
    xiConv (2 * lamOf Δ) (Ttrans Δ τ) α =
      ∫ β in (-π)..π, Xi (2 * lamOf Δ) (α - β) * τ (kMap (lamOf Δ) β) := by
  have hpi := Real.pi_pos
  unfold xiConv Ttrans
  have : ∀ β : ℝ, Xi (2 * lamOf Δ) (α - β) * (2 * π * τ (kMap (lamOf Δ) β)) =
      (2 * π) * (Xi (2 * lamOf Δ) (α - β) * τ (kMap (lamOf Δ) β)) := fun β => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- Pointwise form of the change of variables for (cBE): the equation at `x = k(α)` is
equivalent to (cBE') at `α`. -/
theorem cBE_at_iff {Δ : ℝ} (hΔ : Δ < -1) (ρ : ℝ → ℝ) (α : ℝ) :
    (2 * π * ρ (kMap (lamOf Δ) α) = cBEop Δ ρ (kMap (lamOf Δ) α)) ↔
      Rtrans Δ ρ α + xiConv (2 * lamOf Δ) (Rtrans Δ ρ) α = Xi (lamOf Δ) α := by
  have hlam := lamOf_pos hΔ
  have hpi := Real.pi_pos
  have hXa := Xi_pos hlam α
  rw [cBEop_kMap hΔ, Rtrans_eq hΔ, xiConv_Rtrans hΔ]
  set J := ∫ β in (-π)..π,
      Xi (2 * lamOf Δ) (α - β) * (2 * π * ρ (kMap (lamOf Δ) β) * Xi (lamOf Δ) β)
  set P := ρ (kMap (lamOf Δ) α)
  constructor
  · intro h
    have : 2 * π * P * Xi (lamOf Δ) α = (1 - (2 * π * Xi (lamOf Δ) α)⁻¹ * J) * Xi (lamOf Δ) α := by
      rw [h]
    field_simp at this ⊢
    linarith
  · intro h
    field_simp at h ⊢
    nlinarith [h]

/-- Pointwise form of the change of variables for (cOE). -/
theorem cOE_at_iff {Δ : ℝ} (hΔ : Δ < -1) (τ : ℝ → ℝ) (α : ℝ) :
    (2 * π * τ (kMap (lamOf Δ) α) = cOEop Δ τ (kMap (lamOf Δ) α)) ↔
      Ttrans Δ τ α + xiConv (2 * lamOf Δ) (Ttrans Δ τ) α = PsiFn Δ α := by
  rw [cOEop_kMap hΔ, xiConv_Ttrans, Ttrans]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- (cBE) is equivalent to (cBE') for `R = 2π ρ(k·) k'`: for `x = k(α)`,
`R + (1/2π) Ξ_{2λ} * R = Ξ_λ`. -/
theorem isCBESolution_iff {Δ : ℝ} (hΔ : Δ < -1) (ρ : ℝ → ℝ) :
    IsCBESolution Δ ρ ↔ ∀ α ∈ Icc (-π) π,
      Rtrans Δ ρ α + xiConv (2 * lamOf Δ) (Rtrans Δ ρ) α = Xi (lamOf Δ) α := by
  have hlam := lamOf_pos hΔ
  constructor
  · intro h α hα
    exact (cBE_at_iff hΔ ρ α).1 (h _ (kMap_mem_Icc hlam hα))
  · intro h x hx
    have hα := kInv_mem_Icc hlam hx
    have := (cBE_at_iff hΔ ρ (kInv (lamOf Δ) x)).2 (h _ hα)
    rwa [kMap_kInv hlam] at this

/-- (cOE) is equivalent to (cOE') for `T = 2π τ(k·)`: `T + (1/2π) Ξ_{2λ} * T = Ψ`. -/
theorem isCOESolution_iff {Δ : ℝ} (hΔ : Δ < -1) (τ : ℝ → ℝ) :
    IsCOESolution Δ τ ↔ ∀ α ∈ Icc (-π) π,
      Ttrans Δ τ α + xiConv (2 * lamOf Δ) (Ttrans Δ τ) α = PsiFn Δ α := by
  have hlam := lamOf_pos hΔ
  constructor
  · intro h α hα
    exact (cOE_at_iff hΔ τ α).1 (h _ (kMap_mem_Icc hlam hα))
  · intro h x hx
    have hα := kInv_mem_Icc hlam hx
    have := (cOE_at_iff hΔ τ (kInv (lamOf Δ) x)).2 (h _ hα)
    rwa [kMap_kInv hlam] at this

/-- Transport of an almost-everywhere statement through the change of variables `x = k(α)`. -/
theorem ae_comp_kMap {lam : ℝ} (hlam : 0 < lam) {P : ℝ → Prop}
    (h : ∀ᵐ x ∂(volume.restrict (Icc (-π) π)), P x) :
    ∀ᵐ α ∂(volume.restrict (Icc (-π) π)), P (kMap lam α) := by
  rw [ae_restrict_iff' measurableSet_Icc] at h ⊢
  have hnull : volume {x : ℝ | ¬ (x ∈ Icc (-π) π → P x)} = 0 := by
    simpa [ae_iff] using h
  have hdiff : DifferentiableOn ℝ (kInv lam) {x : ℝ | ¬ (x ∈ Icc (-π) π → P x)} := by
    intro x _
    exact (analyticAt_kInv hlam x).differentiableAt.differentiableWithinAt
  have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hnull
  rw [ae_iff]
  refine measure_mono_null (fun α hα => ?_) himg
  simp only [not_imp] at hα
  refine ⟨kMap lam α, ?_, kInv_kMap hlam α⟩
  simp only [not_imp]
  exact ⟨kMap_mem_Icc hlam hα.1, hα.2⟩

end PottsDiscontinuity.Bethe
