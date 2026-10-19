module

public import Mathlib
public import PottsDiscontinuity.Bethe.Theta

/-!
# The map `k` of arXiv:1611.09877v2, §2.1 (change of variable `x = k(α)`)

For `Δ < -1` let `λ > 0` with `cosh λ = -Δ`.  The paper defines `k` as "the unique continuous
function from `[-π, π]` to itself satisfying
`e^{ik(α)} = (e^λ - e^{-iα}) / (e^{λ-iα} - 1)`" (footnote 3: take the complex logarithm and fix
`k(±π) = ±π`).

Here `k = kMap λ` is given an explicit closed form.  Writing `w = e^{iα}` and `E = e^λ`, the
right-hand side equals `w (E - w̄)/(E - w)`, and `E - w = (E - cos α) - i sin α` has positive real
part, so

  `kMap λ α = α + 2 arctan (sin α / (e^λ - cos α))`.

This is defined for all real `α` (it is the continuous lift with `kMap λ 0 = 0` of the Möbius
map of the circle, extended `2π`-quasi-periodically, `kMap λ (α + 2π) = kMap λ α + 2π`).

Proved separately: the exponential identity, the uniqueness among continuous maps
`[-π, π] → [-π, π]`, `k(±π) = ±π`, oddness, strict monotonicity, bijectivity of
`[-π, π] → [-π, π]`, and `k' = Ξ_λ` with `Ξ_μ(α) = sinh μ / (cosh μ - cos α)`.
-/

@[expose] public section

open Complex Filter Topology Set

namespace PottsDiscontinuity.Bethe

/-- `Ξ_μ(α) = sinh μ / (cosh μ - cos α)` (source: `prop:rhoProp`, definition of `Ξ_μ`). -/
noncomputable def Xi (μ α : ℝ) : ℝ := Real.sinh μ / (Real.cosh μ - Real.cos α)

/-- The map `k = k_λ` of the source: `k_λ(α) = α + 2 arctan (sin α / (e^λ - cos α))`. -/
noncomputable def kMap (lam α : ℝ) : ℝ :=
  α + 2 * Real.arctan (Real.sin α / (Real.exp lam - Real.cos α))

theorem exp_sub_cos_pos {lam : ℝ} (hlam : 0 < lam) (α : ℝ) : 0 < Real.exp lam - Real.cos α := by
  have := Real.add_one_lt_exp hlam.ne'
  have := Real.cos_le_one α
  linarith

theorem Xi_pos {μ : ℝ} (hμ : 0 < μ) (α : ℝ) : 0 < Xi μ α := by
  unfold Xi
  have h1 := Real.sinh_pos_iff.mpr hμ
  have h2 : 1 < Real.cosh μ := by
    have := Real.one_lt_cosh.mpr hμ.ne'
    exact this
  have := Real.cos_le_one α
  exact div_pos h1 (by linarith)

/-! ### Basic symmetries -/

theorem kMap_zero (lam : ℝ) : kMap lam 0 = 0 := by simp [kMap]

/-- `k` is odd. -/
theorem kMap_neg (lam α : ℝ) : kMap lam (-α) = -kMap lam α := by
  simp only [kMap, Real.sin_neg, Real.cos_neg, neg_div, Real.arctan_neg]
  ring

theorem kMap_add_two_pi (lam α : ℝ) : kMap lam (α + 2 * Real.pi) = kMap lam α + 2 * Real.pi := by
  simp only [kMap, Real.sin_add_two_pi, Real.cos_add_two_pi]
  ring

/-- `k(π) = π`. -/
theorem kMap_pi (lam : ℝ) : kMap lam Real.pi = Real.pi := by simp [kMap]

/-- `k(-π) = -π`. -/
theorem kMap_neg_pi (lam : ℝ) : kMap lam (-Real.pi) = -Real.pi := by
  rw [kMap_neg, kMap_pi]

/-! ### The parameter `λ` and analyticity -/

/-- `λ(Δ) = arcosh(-Δ)`: for `Δ < -1` the unique `λ > 0` with `cosh λ = -Δ`. -/
noncomputable def lamOf (Δ : ℝ) : ℝ := Real.arcosh (-Δ)

theorem lamOf_pos {Δ : ℝ} (hΔ : Δ < -1) : 0 < lamOf Δ :=
  Real.arcosh_pos (by linarith)

theorem cosh_lamOf {Δ : ℝ} (hΔ : Δ < -1) : Real.cosh (lamOf Δ) = -Δ :=
  Real.cosh_arcosh (by linarith)

theorem eq_lamOf {Δ lam : ℝ} (hlam : 0 < lam) (hcosh : Real.cosh lam = -Δ) : lam = lamOf Δ := by
  rw [lamOf, ← hcosh, Real.arcosh_cosh hlam.le]

/-! ### The exponential identity -/

theorem norm_exp_I_mul' (α : ℝ) : ‖Complex.exp (I * (α : ℂ))‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal α

theorem ofReal_sub_ne_zero {E : ℝ} (hE : 1 < E) {w : ℂ} (hw : ‖w‖ = 1) : (E : ℂ) - w ≠ 0 := by
  intro h
  have : (E : ℂ) = w := sub_eq_zero.mp h
  have h2 : ‖(E : ℂ)‖ = ‖w‖ := by rw [this]
  rw [hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h2
  linarith

theorem ofReal_mul_sub_one_ne_zero {E : ℝ} (hE : 1 < E) {w : ℂ} (hw : ‖w‖ = 1) :
    (E : ℂ) * w - 1 ≠ 0 := by
  intro h
  have : (E : ℂ) * w = 1 := sub_eq_zero.mp h
  have h2 : ‖(E : ℂ) * w‖ = ‖(1 : ℂ)‖ := by rw [this]
  rw [norm_mul, hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h2
  simp at h2
  linarith

/-- The exponential identity of `k` in unit-circle form with `w = e^{iα}` and `E = e^λ`:
`e^{ik(α)} = w (E - w⁻¹) / (E - w)`. -/
theorem exp_I_mul_kMap_aux {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Complex.exp (I * (kMap lam α : ℂ)) =
      Complex.exp (I * α) * ((Real.exp lam : ℂ) - Complex.exp (-(I * α))) /
        ((Real.exp lam : ℂ) - Complex.exp (I * α)) := by
  set a : ℝ := Real.exp lam - Real.cos α with ha
  set b : ℝ := Real.sin α with hb
  have ha0 : 0 < a := exp_sub_cos_pos hlam α
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hD1 : (Real.exp lam : ℂ) - Complex.exp (I * α) = (a : ℂ) - (b : ℂ) * I := by
    rw [exp_I_mul_ofReal, ha, hb]; push_cast; ring
  have hD2 : (Real.exp lam : ℂ) - Complex.exp (-(I * α)) = (a : ℂ) + (b : ℂ) * I := by
    rw [exp_neg_I_mul_ofReal, ha, hb]; push_cast; ring
  have hne : (a : ℂ) - (b : ℂ) * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; exact ha0.ne' this
  have hth : kMap lam α = α + 2 * Real.arctan (b / a) := rfl
  have h1 : I * (kMap lam α : ℂ) = I * α + (((2 * Real.arctan (b / a) : ℝ) : ℂ)) * I := by
    rw [hth]; push_cast; ring
  rw [h1, Complex.exp_add, exp_two_arctan_mul_I, hD1, hD2]
  push_cast
  field_simp

/-- The exponential identity defining `k` (source form):
`e^{ik(α)} = (e^λ - e^{-iα}) / (e^{λ-iα} - 1)` for every real `α` (`λ > 0`). -/
theorem exp_I_mul_kMap {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Complex.exp (I * (kMap lam α : ℂ)) =
      (Complex.exp (lam : ℂ) - Complex.exp (-(I * α))) /
        (Complex.exp ((lam : ℂ) - I * α) - 1) := by
  rw [exp_I_mul_kMap_aux hlam α]
  have hE : (1 : ℝ) < Real.exp lam := by simpa using hlam
  have hw : ‖Complex.exp (I * (α : ℂ))‖ = 1 := norm_exp_I_mul' α
  have hw0 : Complex.exp (I * (α : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hne := ofReal_sub_ne_zero hE hw
  have h2 : Complex.exp ((lam : ℂ) - I * α) = (Real.exp lam : ℂ) * (Complex.exp (I * α))⁻¹ := by
    rw [Complex.exp_sub, div_eq_mul_inv, Complex.ofReal_exp]
  rw [h2, Complex.exp_neg, Complex.ofReal_exp] at *
  field_simp

/-- The same identity with the exponent written as `k(α) * I`. -/
theorem exp_kMap_mul_I {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Complex.exp ((kMap lam α : ℂ) * I) =
      (Complex.exp (lam : ℂ) - Complex.exp (-(I * α))) /
        (Complex.exp ((lam : ℂ) - I * α) - 1) := by
  rw [mul_comm]; exact exp_I_mul_kMap hlam α

/-! ### Derivative `k' = Ξ_λ`, monotonicity -/

/-- Footnote 5: `k'(α) = Ξ_λ(α) = sinh λ / (cosh λ - cos α)`. -/
theorem hasDerivAt_kMap {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    HasDerivAt (kMap lam) (Xi lam α) α := by
  have ha := (exp_sub_cos_pos hlam α).ne'
  have h1 : HasDerivAt (fun x => Real.sin x / (Real.exp lam - Real.cos x))
      ((Real.cos α * (Real.exp lam - Real.cos α) - Real.sin α * (0 - -Real.sin α)) /
        (Real.exp lam - Real.cos α) ^ 2) α :=
    (Real.hasDerivAt_sin α).div ((hasDerivAt_const α (Real.exp lam)).sub (Real.hasDerivAt_cos α)) ha
  have h2 := (h1.arctan.const_mul 2)
  have h3 := (hasDerivAt_id' α).add h2
  refine h3.congr_deriv ?_
  have hE : Real.exp lam ≠ 0 := (Real.exp_pos lam).ne'
  have hs : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  simp only [Xi, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  have hpos : 0 < (Real.exp lam - Real.cos α)^2 + Real.sin α ^2 := by
    have := exp_sub_cos_pos hlam α
    positivity
  have hden : (Real.exp lam + (Real.exp lam)⁻¹) / 2 - Real.cos α ≠ 0 := by
    have : (Real.exp lam + (Real.exp lam)⁻¹) / 2 - Real.cos α =
        ((Real.exp lam - Real.cos α)^2 + Real.sin α ^2) / (2 * Real.exp lam) := by
      field_simp
      linear_combination (-1) * hs
    rw [this]
    positivity
  have h1' : (Real.exp lam - Real.cos α)^2 + Real.sin α ^2 ≠ 0 := hpos.ne'
  have h2' : Real.exp lam ^ 2 + 1 - 2 * Real.exp lam * Real.cos α =
      (Real.exp lam - Real.cos α)^2 + Real.sin α ^2 := by linear_combination (-1) * hs
  field_simp
  rw [h2']
  field_simp
  linear_combination (-1) * hs

theorem deriv_kMap {lam : ℝ} (hlam : 0 < lam) (α : ℝ) : deriv (kMap lam) α = Xi lam α :=
  (hasDerivAt_kMap hlam α).deriv

theorem continuous_kMap {lam : ℝ} (hlam : 0 < lam) : Continuous (kMap lam) :=
  continuous_iff_continuousAt.mpr fun α => (hasDerivAt_kMap hlam α).continuousAt

/-- `k` is strictly increasing on all of `ℝ`. -/
theorem strictMono_kMap {lam : ℝ} (hlam : 0 < lam) : StrictMono (kMap lam) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_kMap hlam) (fun α => Xi_pos hlam α)

/-- `k` maps `[-π, π]` into itself. -/
theorem mapsTo_kMap {lam : ℝ} (hlam : 0 < lam) :
    MapsTo (kMap lam) (Icc (-Real.pi) Real.pi) (Icc (-Real.pi) Real.pi) := by
  intro α hα
  have hm := (strictMono_kMap hlam).monotone
  constructor
  · calc -Real.pi = kMap lam (-Real.pi) := (kMap_neg_pi lam).symm
      _ ≤ kMap lam α := hm hα.1
  · calc kMap lam α ≤ kMap lam Real.pi := hm hα.2
      _ = Real.pi := kMap_pi lam

/-- `k : [-π, π] → [-π, π]` is a bijection (footnote 3: "`k` is invertible"). -/
theorem bijOn_kMap {lam : ℝ} (hlam : 0 < lam) :
    BijOn (kMap lam) (Icc (-Real.pi) Real.pi) (Icc (-Real.pi) Real.pi) := by
  refine ⟨mapsTo_kMap hlam, (strictMono_kMap hlam).injective.injOn, ?_⟩
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have := intermediate_value_Icc hpi (continuous_kMap hlam).continuousOn
  rw [kMap_neg_pi, kMap_pi] at this
  exact this

/-- The derivative of `k` is bounded away from `0` and `∞`: it lies between the explicit positive
constants `sinh λ / (cosh λ + 1)` and `sinh λ / (cosh λ - 1)`. -/
theorem Xi_bounds {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    Real.sinh μ / (Real.cosh μ + 1) ≤ Xi μ α ∧ Xi μ α ≤ Real.sinh μ / (Real.cosh μ - 1) := by
  have h1 := Real.sinh_pos_iff.mpr hμ
  have h2 : 1 < Real.cosh μ := Real.one_lt_cosh.mpr hμ.ne'
  have hc1 := Real.cos_le_one α
  have hc2 := Real.neg_one_le_cos α
  unfold Xi
  constructor
  · exact div_le_div_of_nonneg_left h1.le (by linarith) (by linarith)
  · exact div_le_div_of_nonneg_left h1.le (by linarith) (by linarith)

/-! ### Uniqueness (footnote 3) -/

/-- Uniqueness in the class stated in the source: any continuous `f : [-π, π] → [-π, π]` with
`e^{i f(α)} = (e^λ - e^{-iα}) / (e^{λ-iα} - 1)` on `[-π, π]` coincides with `kMap λ` there. -/
theorem eqOn_kMap_of_exp {lam : ℝ} (hlam : 0 < lam) {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc (-Real.pi) Real.pi))
    (hmaps : MapsTo f (Icc (-Real.pi) Real.pi) (Icc (-Real.pi) Real.pi))
    (hexp : ∀ α ∈ Icc (-Real.pi) Real.pi, Complex.exp (I * (f α : ℂ)) =
      (Complex.exp (lam : ℂ) - Complex.exp (-(I * α))) /
        (Complex.exp ((lam : ℂ) - I * α) - 1)) :
    EqOn f (kMap lam) (Icc (-Real.pi) Real.pi) := by
  have : PreconnectedSpace (Icc (-Real.pi) Real.pi) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hF : Continuous (fun p : Icc (-Real.pi) Real.pi => f p) := hc.domRestrict
  have hG : Continuous (fun p : Icc (-Real.pi) Real.pi => kMap lam p) :=
    (continuous_kMap hlam).comp continuous_subtype_val
  have hFG : ∀ p : Icc (-Real.pi) Real.pi,
      Complex.exp ((f p : ℂ) * I) = Complex.exp ((kMap lam p : ℂ) * I) := by
    intro p
    have h1 := hexp p p.2
    have h2 := exp_kMap_mul_I hlam p
    rw [mul_comm (f p : ℂ) I, h1, h2]
  have h0mem : (0 : ℝ) ∈ Icc (-Real.pi) Real.pi := ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
  have h0 : f 0 = kMap lam 0 := by
    have hE := hFG ⟨0, h0mem⟩
    simp only [kMap_zero] at hE
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero] at hE
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hE
    have h1 : (f 0 : ℂ) = (n : ℂ) * (2 * Real.pi) := by
      have h2 : (f 0 : ℂ) * I = (n : ℂ) * (2 * Real.pi) * I := by
        linear_combination hn
      exact mul_right_cancel₀ Complex.I_ne_zero h2
    have h3 : f 0 = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast h1
    have hb := hmaps h0mem
    have hpi := Real.pi_pos
    have h4 : (n : ℝ) < 1 := by nlinarith [hb.2]
    have h5 : (-1 : ℝ) < n := by nlinarith [hb.1]
    have h6 : n = 0 := by
      have a1 : n < 1 := by exact_mod_cast h4
      have a2 : -1 < n := by exact_mod_cast h5
      omega
    rw [h3, h6]; simp [kMap_zero]
  have := eq_of_exp_eq hF hG hFG ⟨0, h0mem⟩ h0
  intro α hα
  exact congrFun this ⟨α, hα⟩

/-- Existence and uniqueness: `kMap λ` is the unique continuous map `[-π, π] → [-π, π]` satisfying
the exponential identity. -/
theorem existsUnique_kMap {lam : ℝ} (hlam : 0 < lam) :
    ∃ k : Icc (-Real.pi) Real.pi → Icc (-Real.pi) Real.pi, Continuous k ∧
      (∀ α, Complex.exp (I * ((k α : ℝ) : ℂ)) =
        (Complex.exp (lam : ℂ) - Complex.exp (-(I * (α : ℝ)))) /
          (Complex.exp ((lam : ℂ) - I * (α : ℝ)) - 1)) ∧
      ∀ k' : Icc (-Real.pi) Real.pi → Icc (-Real.pi) Real.pi, Continuous k' →
        (∀ α, Complex.exp (I * ((k' α : ℝ) : ℂ)) =
          (Complex.exp (lam : ℂ) - Complex.exp (-(I * (α : ℝ)))) /
            (Complex.exp ((lam : ℂ) - I * (α : ℝ)) - 1)) → k' = k := by
  refine ⟨fun α => ⟨kMap lam α, mapsTo_kMap hlam α.2⟩, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk ((continuous_kMap hlam).comp continuous_subtype_val) _
  · intro α
    exact exp_I_mul_kMap hlam α
  · intro k' hk' hexp
    funext α
    apply Subtype.ext
    let f : ℝ → ℝ := fun t => if ht : t ∈ Icc (-Real.pi) Real.pi then (k' ⟨t, ht⟩ : ℝ) else 0
    have hcf : ContinuousOn f (Icc (-Real.pi) Real.pi) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (Icc (-Real.pi) Real.pi).domRestrict f = fun p => (k' p : ℝ) := by
        funext p
        show f p = _
        have hp := p.2
        simp only [f, hp, dite_true]
      rw [this]
      exact continuous_subtype_val.comp hk'
    have hmaps : MapsTo f (Icc (-Real.pi) Real.pi) (Icc (-Real.pi) Real.pi) := by
      intro t ht
      simp only [f, ht, dite_true]
      exact (k' ⟨t, ht⟩).2
    have hα := α.2
    have := eqOn_kMap_of_exp hlam hcf hmaps (by
      intro t ht
      simp only [f, ht, dite_true]
      exact hexp ⟨t, ht⟩) hα
    simp only [f, hα, dite_true] at this
    exact this

end PottsDiscontinuity.Bethe
