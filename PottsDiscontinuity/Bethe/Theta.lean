module

public import Mathlib

/-!
# The Bethe phase `Θ` for `Δ < -1`

Source: arXiv:1611.09877v2, equation (1.8) and footnote 2.  For `Δ < -1` the paper defines `Θ`
as "the unique continuous function `ℝ² → ℝ` with `Θ(0,0) = 0` and
`exp(-iΘ(x,y)) = e^{i(x-y)} (e^{-ix} + e^{iy} - 2Δ) / (e^{ix} + e^{-iy} - 2Δ)`".

Here `Θ` is given an explicit closed form.  Since `e^{ix} + e^{-iy} - 2Δ = a + ib` with
`a = cos x + cos y - 2Δ > 0` and `b = sin x - sin y`, and `e^{-ix} + e^{iy} - 2Δ` is its complex
conjugate, the phase `-arg` of the right-hand side of (1.8) is `y - x + 2 arg (a + ib)` with
`arg (a + ib) = arctan (b / a)` because `a > 0`:

  `Θ(Δ, x, y) = y - x + 2 arctan ((sin x - sin y) / (cos x + cos y - 2Δ))`.

The characterization in the source (continuity, `Θ(0,0) = 0`, the exponential identity (1.8),
uniqueness) is then proved as separate theorems:

* `theta_isBethePhase`, `eq_theta_of_isBethePhase`, `existsUnique_isBethePhase`;
* `analyticAt_theta` (joint real analyticity in `(Δ, x, y)` for `Δ < -1`) and consequences;
* the listed properties: antisymmetries, `Θ(x,x) = 0`, the `2π` period shifts in both variables,
  `Θ(π,y) - Θ(-π,y) = -2π`, and the limit `Δ → -∞` (`Θ(x,y) → y - x`).
-/

@[expose] public section

open Complex Filter Topology

namespace PottsDiscontinuity.Bethe

/-! ### Generic helper lemmas -/

/-- `exp (2 i arctan t) = (1 + i t) / (1 - i t)`. -/
theorem exp_two_arctan_mul_I (t : ℝ) :
    Complex.exp (((2 * Real.arctan t : ℝ) : ℂ) * I) = (1 + (t : ℂ) * I) / (1 - (t : ℂ) * I) := by
  have hs : (0:ℝ) < 1 + t ^ 2 := by positivity
  have hc : Real.cos (Real.arctan t) ^ 2 = 1 / (1 + t ^ 2) := by
    rw [Real.cos_arctan, div_pow, Real.sq_sqrt hs.le]; simp
  have h2 : Real.cos (Real.arctan t) * Real.sin (Real.arctan t) = t / (1 + t ^ 2) := by
    rw [Real.cos_arctan, Real.sin_arctan]
    have : (0:ℝ) < √(1 + t^2) := Real.sqrt_pos.mpr hs
    field_simp
    rw [Real.sq_sqrt hs.le]
  have hcos : Real.cos (2 * Real.arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [Real.cos_two_mul, hc]; field_simp; ring
  have hsin : Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
    rw [Real.sin_two_mul]; linear_combination 2 * h2
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin]
  have h1 : (1 - (t : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h3 : (1 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h4 : (1 + (t:ℂ)^2) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- `exp (i x) = cos x + i sin x` for real `x`, with the factor `I` on the left. -/
theorem exp_I_mul_ofReal (x : ℝ) :
    Complex.exp (I * (x : ℂ)) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * I := by
  rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- `exp (-(i x)) = cos x - i sin x` for real `x`. -/
theorem exp_neg_I_mul_ofReal (x : ℝ) :
    Complex.exp (-(I * (x : ℂ))) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * I := by
  have := exp_I_mul_ofReal (-x)
  rw [show I * ((-x : ℝ) : ℂ) = -(I * (x:ℂ)) by push_cast; ring] at this
  rw [this]; simp [Real.cos_neg, Real.sin_neg]; ring

/-- Uniqueness of continuous lifts: two continuous real functions on a preconnected space with
the same `x ↦ exp (i x)` which agree at one point are equal. -/
theorem eq_of_exp_eq {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ p, Complex.exp ((f p : ℂ) * I) = Complex.exp ((g p : ℂ) * I)) (p₀ : X)
    (h0 : f p₀ = g p₀) : f = g := by
  have key : ∀ p, ((f p - g p) / (2 * Real.pi)) ∈ Set.range ((↑) : ℤ → ℝ) := by
    intro p
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (h p)
    refine ⟨n, ?_⟩
    have h1 : ((f p : ℂ) - g p) = (n : ℂ) * (2 * Real.pi) := by
      have h2 : ((f p : ℂ) - g p) * I = (n : ℂ) * (2 * Real.pi) * I := by
        linear_combination hn
      exact mul_right_cancel₀ Complex.I_ne_zero h2
    have h3 : f p - g p = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast h1
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp
    linarith
  have hd : IsDiscrete (Set.range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isEmbedding.isInducing.isDiscrete_range
  have hc : Continuous (fun p => (f p - g p) / (2 * Real.pi)) :=
    (hf.sub hg).div_const _
  funext p
  have := (isPreconnected_univ (α := X)).constant_of_mapsTo hd hc.continuousOn
    (fun p _ => key p) (Set.mem_univ p) (Set.mem_univ p₀)
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h4 : (f p - g p) / (2 * Real.pi) = 0 := by rw [this, h0]; simp
  rw [div_eq_zero_iff] at h4
  rcases h4 with h4 | h4
  · linarith
  · exact absurd h4 hpi

/-- `Real.arctan` is real analytic everywhere. -/
theorem analyticAt_real_arctan (t : ℝ) : AnalyticAt ℝ Real.arctan t := by
  have h1 : AnalyticAt ℂ Complex.arctan (t : ℂ) := by
    unfold Complex.arctan
    have hden : (1 - (t:ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hslit : ((1 + (t:ℂ) * I) / (1 - (t:ℂ) * I)) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      have h2 : (1 + (t:ℂ)^2) ≠ 0 := by
        have : (0:ℝ) < 1 + t^2 := by positivity
        exact_mod_cast this.ne'
      have : ((1 + (t:ℂ) * I) / (1 - (t:ℂ) * I)) =
          (((1 - t^2) / (1 + t^2) : ℝ) : ℂ) + (((2 * t) / (1 + t^2) : ℝ) : ℂ) * I := by
        push_cast
        field_simp
        ring_nf
        simp [Complex.I_sq]
        ring
      by_cases ht : t = 0
      · left; subst ht; simp
      · right
        have hv : ((2 * t) / (1 + t^2) : ℝ) ≠ 0 := by positivity
        rw [this]
        generalize ((2 * t) / (1 + t^2) : ℝ) = v at *
        generalize ((1 - t^2) / (1 + t^2) : ℝ) = u at *
        simpa using hv
    have : AnalyticAt ℂ (fun z : ℂ => (1 + z * I) / (1 - z * I)) (t:ℂ) := by
      fun_prop (disch := assumption)
    exact analyticAt_const.mul (this.clog hslit)
  have h2 : Real.arctan = fun x : ℝ => (Complex.arctan (x:ℂ)).re := by
    funext x; rw [← Complex.ofReal_arctan, Complex.ofReal_re]
  rw [h2]
  exact h1.re_ofReal

/-! ### Definition of `Θ` -/

/-- The Bethe phase `Θ_Δ(x, y)` of arXiv:1611.09877v2, (1.8), for `Δ < -1` (the formula is
total in `Δ`, but it is the Bethe phase only for `Δ < -1`; see `theta_isBethePhase`):
`Θ(Δ, x, y) = y - x + 2 arctan ((sin x - sin y) / (cos x + cos y - 2Δ))`. -/
noncomputable def theta (Δ x y : ℝ) : ℝ :=
  y - x + 2 * Real.arctan ((Real.sin x - Real.sin y) / (Real.cos x + Real.cos y - 2 * Δ))

/-- The right-hand side of (1.8):
`e^{i(x-y)} (e^{-ix} + e^{iy} - 2Δ) / (e^{ix} + e^{-iy} - 2Δ)`. -/
noncomputable def thetaRhs (Δ x y : ℝ) : ℂ :=
  Complex.exp (I * ((x : ℂ) - y)) *
    ((Complex.exp (-(I * x)) + Complex.exp (I * y) - 2 * (Δ : ℂ)) /
      (Complex.exp (I * x) + Complex.exp (-(I * y)) - 2 * (Δ : ℂ)))

/-- The defining property of the Bethe phase in the source, for a given `Δ`: `f` is continuous on
`ℝ²`, `f 0 0 = 0`, and `exp (-i f(x,y))` is the right-hand side of (1.8) for all `x y`. -/
def IsBethePhase (Δ : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  Continuous (fun p : ℝ × ℝ => f p.1 p.2) ∧ f 0 0 = 0 ∧
    ∀ x y : ℝ, Complex.exp (-(I * (f x y : ℂ))) = thetaRhs Δ x y

/-- The denominator `cos x + cos y - 2Δ = Re (e^{ix} + e^{-iy} - 2Δ)` is positive for `Δ < -1`. -/
theorem cos_add_cos_sub_pos {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    0 < Real.cos x + Real.cos y - 2 * Δ := by
  have := Real.neg_one_le_cos x
  have := Real.neg_one_le_cos y
  linarith

theorem theta_zero_zero (Δ : ℝ) : theta Δ 0 0 = 0 := by
  simp [theta]

/-- Continuity of `Θ_Δ` on `ℝ²` for fixed `Δ < -1`. -/
theorem continuous_theta {Δ : ℝ} (hΔ : Δ < -1) :
    Continuous (fun p : ℝ × ℝ => theta Δ p.1 p.2) := by
  unfold theta
  refine (continuous_snd.sub continuous_fst).add (continuous_const.mul
    (Real.continuous_arctan.comp ?_))
  refine ((Real.continuous_sin.comp continuous_fst).sub (Real.continuous_sin.comp
    continuous_snd)).div (((Real.continuous_cos.comp continuous_fst).add
    (Real.continuous_cos.comp continuous_snd)).sub continuous_const) ?_
  intro p
  exact (cos_add_cos_sub_pos hΔ p.1 p.2).ne'

/-- The exponential identity (1.8): `exp (-i Θ(x,y)) = e^{i(x-y)} (e^{-ix} + e^{iy} - 2Δ) /
(e^{ix} + e^{-iy} - 2Δ)` for `Δ < -1`. -/
theorem exp_neg_I_theta {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    Complex.exp (-(I * (theta Δ x y : ℂ))) = thetaRhs Δ x y := by
  set a : ℝ := Real.cos x + Real.cos y - 2 * Δ with ha
  set b : ℝ := Real.sin x - Real.sin y with hb
  have ha0 : 0 < a := cos_add_cos_sub_pos hΔ x y
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hD1 : Complex.exp (I * x) + Complex.exp (-(I * y)) - 2 * (Δ : ℂ) =
      (a : ℂ) + (b : ℂ) * I := by
    rw [exp_I_mul_ofReal, exp_neg_I_mul_ofReal, ha, hb]; push_cast; ring
  have hD2 : Complex.exp (-(I * x)) + Complex.exp (I * y) - 2 * (Δ : ℂ) =
      (a : ℂ) - (b : ℂ) * I := by
    rw [exp_neg_I_mul_ofReal, exp_I_mul_ofReal, ha, hb]; push_cast; ring
  have hne : (a : ℂ) + (b : ℂ) * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; exact ha0.ne' this
  have hne' : (a : ℂ) - (b : ℂ) * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; exact ha0.ne' this
  have hth : theta Δ x y = y - x + 2 * Real.arctan (b / a) := rfl
  have hinv : Complex.exp (-(I * (theta Δ x y : ℂ))) =
      Complex.exp (I * ((x : ℂ) - y)) *
        (Complex.exp (-(((2 * Real.arctan (b / a) : ℝ) : ℂ) * I))) := by
    rw [← Complex.exp_add, hth]
    congr 1
    push_cast
    ring
  rw [hinv, thetaRhs, hD1, hD2, Complex.exp_neg, exp_two_arctan_mul_I]
  congr 1
  push_cast
  field_simp

/-- Existence part of the source characterization: `Θ_Δ` is continuous, vanishes at `(0,0)`,
and satisfies (1.8). -/
theorem theta_isBethePhase {Δ : ℝ} (hΔ : Δ < -1) : IsBethePhase Δ (theta Δ) :=
  ⟨continuous_theta hΔ, theta_zero_zero Δ, exp_neg_I_theta hΔ⟩

/-- Uniqueness part of the source characterization: any continuous `f : ℝ → ℝ → ℝ` with
`f 0 0 = 0` and satisfying (1.8) equals `Θ_Δ`. -/
theorem eq_theta_of_isBethePhase {Δ : ℝ} (hΔ : Δ < -1) {f : ℝ → ℝ → ℝ}
    (hf : IsBethePhase Δ f) : f = theta Δ := by
  obtain ⟨hc, h0, hexp⟩ := hf
  have hexp' : ∀ p : ℝ × ℝ, Complex.exp ((f p.1 p.2 : ℂ) * I) =
      Complex.exp ((theta Δ p.1 p.2 : ℂ) * I) := by
    intro p
    have h1 := hexp p.1 p.2
    have h2 := exp_neg_I_theta hΔ p.1 p.2
    rw [← h2, Complex.exp_neg, Complex.exp_neg] at h1
    have h3 := inv_injective h1
    rw [mul_comm] at h3
    rw [mul_comm (theta Δ p.1 p.2 : ℂ)]
    exact h3
  have := eq_of_exp_eq hc (continuous_theta hΔ) hexp' (0, 0) (by simp [h0, theta_zero_zero])
  funext x y
  exact congrFun this (x, y)

/-- Footnote 2 / (1.8): for `Δ < -1` there is exactly one continuous `Θ : ℝ → ℝ → ℝ` with
`Θ 0 0 = 0` satisfying (1.8), and it is `theta Δ`. -/
theorem existsUnique_isBethePhase {Δ : ℝ} (hΔ : Δ < -1) :
    ∃! f : ℝ → ℝ → ℝ, IsBethePhase Δ f :=
  ⟨theta Δ, theta_isBethePhase hΔ, fun _ hf => eq_theta_of_isBethePhase hΔ hf⟩

/-! ### Analyticity -/

/-- Joint real analyticity of `(Δ, x, y) ↦ Θ_Δ(x, y)` at every point with `Δ < -1`. -/
theorem analyticAt_theta {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => theta p.1 p.2.1 p.2.2) (Δ, x, y) := by
  have hD : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.1) (Δ, x, y) := analyticAt_fst
  have hX : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) (Δ, x, y) :=
    analyticAt_fst.comp analyticAt_snd
  have hY : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) (Δ, x, y) :=
    analyticAt_snd.comp analyticAt_snd
  have hsx : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => Real.sin p.2.1) (Δ, x, y) :=
    Real.analyticAt_sin.comp hX
  have hsy : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => Real.sin p.2.2) (Δ, x, y) :=
    Real.analyticAt_sin.comp hY
  have hcx : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => Real.cos p.2.1) (Δ, x, y) :=
    Real.analyticAt_cos.comp hX
  have hcy : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => Real.cos p.2.2) (Δ, x, y) :=
    Real.analyticAt_cos.comp hY
  have hden : AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => Real.cos p.2.1 + Real.cos p.2.2 - 2 * p.1) (Δ, x, y) :=
    (hcx.add hcy).sub (analyticAt_const.mul hD)
  have hq : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      (Real.sin p.2.1 - Real.sin p.2.2) / (Real.cos p.2.1 + Real.cos p.2.2 - 2 * p.1))
      (Δ, x, y) :=
    (hsx.sub hsy).div hden (cos_add_cos_sub_pos hΔ x y).ne'
  have hat := (analyticAt_real_arctan _).comp hq
  exact (hY.sub hX).add (analyticAt_const.mul hat)

/-- For fixed `Δ < -1`, `(x, y) ↦ Θ_Δ(x, y)` is real analytic. -/
theorem analyticAt_theta_xy {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => theta Δ p.1 p.2) (x, y) := by
  have h1 : AnalyticAt ℝ (fun p : ℝ × ℝ => ((Δ, p.1, p.2) : ℝ × ℝ × ℝ)) (x, y) :=
    (analyticAt_const (v := Δ)).prod (analyticAt_fst.prod analyticAt_snd)
  exact AnalyticAt.comp (g := fun p : ℝ × ℝ × ℝ => theta p.1 p.2.1 p.2.2)
    (f := fun p : ℝ × ℝ => ((Δ, p.1, p.2) : ℝ × ℝ × ℝ)) (analyticAt_theta hΔ x y) h1

/-- `Θ_Δ(·, y)` is analytic in the first variable (needed for the partial derivative `∂₁Θ`). -/
theorem analyticAt_theta_left {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => theta Δ s y) x := by
  have h1 : AnalyticAt ℝ (fun s : ℝ => ((s, y) : ℝ × ℝ)) x :=
    analyticAt_id.prod analyticAt_const
  exact AnalyticAt.comp (g := fun p : ℝ × ℝ => theta Δ p.1 p.2)
    (f := fun s : ℝ => ((s, y) : ℝ × ℝ)) (analyticAt_theta_xy hΔ x y) h1

/-- `Θ_Δ(x, ·)` is analytic in the second variable (needed for the partial derivative `∂₂Θ`). -/
theorem analyticAt_theta_right {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    AnalyticAt ℝ (fun t : ℝ => theta Δ x t) y := by
  have h1 : AnalyticAt ℝ (fun t : ℝ => ((x, t) : ℝ × ℝ)) y :=
    analyticAt_const.prod analyticAt_id
  exact AnalyticAt.comp (g := fun p : ℝ × ℝ => theta Δ p.1 p.2)
    (f := fun t : ℝ => ((x, t) : ℝ × ℝ)) (analyticAt_theta_xy hΔ x y) h1

/-! ### Symmetries and period shifts -/

/-- Antisymmetry under point reflection: `Θ(-x,-y) = -Θ(x,y)`. -/
theorem theta_neg_neg (Δ x y : ℝ) : theta Δ (-x) (-y) = -theta Δ x y := by
  simp only [theta, Real.sin_neg, Real.cos_neg]
  have : (-Real.sin x - -Real.sin y) = -(Real.sin x - Real.sin y) := by ring
  rw [this, neg_div, Real.arctan_neg]
  ring

/-- Antisymmetry under swapping the variables: `Θ(y,x) = -Θ(x,y)`. -/
theorem theta_swap (Δ x y : ℝ) : theta Δ y x = -theta Δ x y := by
  simp only [theta]
  have h1 : Real.sin y - Real.sin x = -(Real.sin x - Real.sin y) := by ring
  have h2 : Real.cos y + Real.cos x - 2 * Δ = Real.cos x + Real.cos y - 2 * Δ := by ring
  rw [h1, h2, neg_div, Real.arctan_neg]
  ring

/-- The equivalent form `Θ(x,-y) = -Θ(-x,y)` of the antisymmetry. -/
theorem theta_neg_right (Δ x y : ℝ) : theta Δ x (-y) = -theta Δ (-x) y := by
  have := theta_neg_neg Δ (-x) y
  rwa [neg_neg] at this

/-- `Θ` vanishes on the diagonal: `Θ(x,x) = 0`. -/
theorem theta_self (Δ x : ℝ) : theta Δ x x = 0 := by
  simp [theta]

/-- `Θ(x + 2π, y) - Θ(x, y) = -2π`. -/
theorem theta_add_two_pi_left (Δ x y : ℝ) :
    theta Δ (x + 2 * Real.pi) y = theta Δ x y - 2 * Real.pi := by
  simp only [theta, Real.sin_add_two_pi, Real.cos_add_two_pi]
  ring

/-! ### Derivative consequences -/

/-- `∂₂Θ(x,-y) = ∂₂Θ(-x,y)`, a consequence of `Θ(x,-y) = -Θ(-x,y)`. -/
theorem deriv_theta_right_neg (Δ x y : ℝ) :
    deriv (fun t => theta Δ x t) (-y) = deriv (fun t => theta Δ (-x) t) y := by
  have h : (fun t => theta Δ x (-t)) = fun t => -theta Δ (-x) t :=
    funext fun t => theta_neg_right Δ x t
  have h1 : deriv (fun t => theta Δ x (-t)) y = -deriv (fun t => theta Δ x t) (-y) :=
    deriv_comp_neg (fun t => theta Δ x t) y
  rw [h, deriv.fun_neg] at h1
  linarith

/-- On the diagonal `(∂₁Θ + ∂₂Θ)(x,x) = 0`. -/
theorem deriv_theta_diag {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) :
    deriv (fun s => theta Δ s x) x + deriv (fun t => theta Δ x t) x = 0 := by
  have h1 : HasDerivAt (fun s => theta Δ s x) (deriv (fun s => theta Δ s x) x) x :=
    (analyticAt_theta_left hΔ x x).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun t => theta Δ x t) (deriv (fun t => theta Δ x t) x) x :=
    (analyticAt_theta_right hΔ x x).differentiableAt.hasDerivAt
  have hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => theta Δ p.1 p.2) (x, x) :=
    (analyticAt_theta_xy hΔ x x).differentiableAt
  have h3 : HasDerivAt (fun s : ℝ => ((s, s) : ℝ × ℝ)) ((1, 1) : ℝ × ℝ) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_id x)
  have h4 := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, s) : ℝ × ℝ)) x hF.hasFDerivAt h3
  have h5 : (fun s : ℝ => theta Δ s s) = fun _ => 0 := funext fun s => theta_self Δ s
  have h6 : HasDerivAt (fun s : ℝ => theta Δ s s) 0 x := by
    rw [h5]; exact hasDerivAt_const x 0
  have h7 := h4.unique h6
  have hF1 : HasFDerivAt (fun p : ℝ × ℝ => theta Δ p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => theta Δ p.1 p.2) (x, x)) (x, x) := hF.hasFDerivAt
  have h8 : deriv (fun s => theta Δ s x) x =
      fderiv ℝ (fun p : ℝ × ℝ => theta Δ p.1 p.2) (x, x) (1, 0) := by
    have hh : HasDerivAt (fun s : ℝ => ((s, x) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x x)
    exact (HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, x) : ℝ × ℝ)) x hF1 hh).deriv
  have h9 : deriv (fun t => theta Δ x t) x =
      fderiv ℝ (fun p : ℝ × ℝ => theta Δ p.1 p.2) (x, x) (0, 1) := by
    have hh : HasDerivAt (fun t : ℝ => ((x, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) x :=
      (hasDerivAt_const x x).prodMk (hasDerivAt_id x)
    exact (HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => ((x, t) : ℝ × ℝ)) x hF1 hh).deriv
  rw [h8, h9, ← map_add]
  have : ((1, 0) : ℝ × ℝ) + (0, 1) = (1, 1) := by simp
  rw [this]
  exact h7

/-! ### The limit `Δ → -∞` -/

/-- As `Δ → -∞`, `Θ_Δ(x, y) → y - x` (footnote 8 / the convention `Θ_{-∞}(x,y) = y - x`). -/
theorem tendsto_theta_atBot (x y : ℝ) :
    Tendsto (fun Δ : ℝ => theta Δ x y) atBot (𝓝 (y - x)) := by
  have h1 : Tendsto (fun Δ : ℝ => Real.cos x + Real.cos y - 2 * Δ) atBot atTop := by
    have : Tendsto (fun Δ : ℝ => -2 * Δ) atBot atTop :=
      tendsto_id.const_mul_atBot_of_neg (by norm_num)
    have h := tendsto_atTop_add_const_left atBot (Real.cos x + Real.cos y) this
    refine h.congr fun Δ => ?_
    ring
  have h2 : Tendsto (fun Δ : ℝ =>
      (Real.sin x - Real.sin y) / (Real.cos x + Real.cos y - 2 * Δ)) atBot (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1
  have h3 := (Real.continuous_arctan.tendsto 0).comp h2
  rw [Real.arctan_zero] at h3
  have h4 := (tendsto_const_nhds (x := y - x)).add (h3.const_mul 2)
  simpa [theta] using h4

/-! ### Analyticity in `1/Δ` at `Δ = -∞` -/

/-- `Θ` as a function of `ε = 1/Δ`:
`Θ^{inv}(ε, x, y) = y - x + 2 arctan (ε (sin x - sin y) / (ε (cos x + cos y) - 2))`.
For `Δ < -1` one has `Θ_Δ = Θ^{inv}(1/Δ, ·, ·)` (`theta_eq_thetaInv`), and `ε = 0`
corresponds to `Δ = -∞`, where `Θ_{-∞}(x,y) = y - x` (`thetaInv_zero`). -/
noncomputable def thetaInv (ε x y : ℝ) : ℝ :=
  y - x + 2 * Real.arctan
    (ε * (Real.sin x - Real.sin y) / (ε * (Real.cos x + Real.cos y) - 2))

theorem thetaInv_zero (x y : ℝ) : thetaInv 0 x y = y - x := by
  simp [thetaInv]

theorem theta_eq_thetaInv {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    theta Δ x y = thetaInv (1 / Δ) x y := by
  have hΔ0 : Δ ≠ 0 := by intro h; rw [h] at hΔ; norm_num at hΔ
  have hd : Real.cos x + Real.cos y - 2 * Δ ≠ 0 := (cos_add_cos_sub_pos hΔ x y).ne'
  simp only [theta, thetaInv]
  congr 3
  have h2 : 1 / Δ * (Real.cos x + Real.cos y) - 2 ≠ 0 := by
    intro h
    apply hd
    field_simp at h
    linarith
  field_simp

/-- `(ε, x, y) ↦ Θ^{inv}(ε, x, y)` is real analytic for `|ε| < 1`; in particular at `ε = 0`
(`Δ = -∞`), which is the sense of footnote 8 of the source. -/
theorem analyticAt_thetaInv {ε : ℝ} (hε : |ε| < 1) (x y : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => thetaInv p.1 p.2.1 p.2.2) (ε, x, y) := by
  have hE : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.1) (ε, x, y) := analyticAt_fst
  have hX : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) (ε, x, y) :=
    analyticAt_fst.comp analyticAt_snd
  have hY : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) (ε, x, y) :=
    analyticAt_snd.comp analyticAt_snd
  have hsx : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => Real.sin p.2.1) (ε, x, y) :=
    Real.analyticAt_sin.comp hX
  have hsy : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => Real.sin p.2.2) (ε, x, y) :=
    Real.analyticAt_sin.comp hY
  have hcx : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => Real.cos p.2.1) (ε, x, y) :=
    Real.analyticAt_cos.comp hX
  have hcy : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => Real.cos p.2.2) (ε, x, y) :=
    Real.analyticAt_cos.comp hY
  have hden : AnalyticAt ℝ
      (fun p : ℝ × ℝ × ℝ => p.1 * (Real.cos p.2.1 + Real.cos p.2.2) - 2) (ε, x, y) :=
    (hE.mul (hcx.add hcy)).sub analyticAt_const
  have hden0 : ε * (Real.cos x + Real.cos y) - 2 ≠ 0 := by
    have hc : |Real.cos x + Real.cos y| ≤ 2 := by
      have h1 := Real.abs_cos_le_one x
      have h2 := Real.abs_cos_le_one y
      calc |Real.cos x + Real.cos y| ≤ |Real.cos x| + |Real.cos y| := abs_add_le _ _
        _ ≤ 2 := by linarith
    have h3 : |ε * (Real.cos x + Real.cos y)| < 2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg ε, abs_nonneg (Real.cos x + Real.cos y)]
    intro h
    have : ε * (Real.cos x + Real.cos y) = 2 := by linarith
    rw [this] at h3
    norm_num at h3
  have hq : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      p.1 * (Real.sin p.2.1 - Real.sin p.2.2) /
        (p.1 * (Real.cos p.2.1 + Real.cos p.2.2) - 2)) (ε, x, y) :=
    (hE.mul (hsx.sub hsy)).div hden hden0
  have hat := (analyticAt_real_arctan _).comp hq
  exact (hY.sub hX).add (analyticAt_const.mul hat)

end PottsDiscontinuity.Bethe
