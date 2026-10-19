module

public import Mathlib
public import PottsDiscontinuity.Bethe.Prop21Rho

/-!
# Proposition 2.1: regularity of `ρ`

* `continuous_rho` (in `Prop21Rho`): `x ↦ ρ_Δ(x)` is continuous;
* `analyticAt_rho`: for fixed `Δ < -1`, `x ↦ ρ_Δ(x)` is real analytic.  The cosine series
  `R(α) = 1/2 + ∑ cos(mα)/cosh(λ m)` extends to a holomorphic function on the strip
  `|Im z| < λ/2` (`differentiableOn_RsechC`, Weierstrass M-test), and `k^{-1}`, `Ξ_λ` are explicit
  analytic functions;
* `continuousOn_rho_joint`: `(Δ, x) ↦ ρ_Δ(x)` is jointly continuous on `{Δ < -1} × ℝ`.

*Joint real-analyticity in `(Δ, x)` is not proved here*: it needs holomorphy of a series of
functions of two complex variables (Osgood's lemma), which is not available in Mathlib.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

theorem norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos]
  have h1 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp
  calc ‖(Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) / 2‖
      ≤ (‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖) / 2 := by
        rw [norm_div]; simp only [Complex.norm_ofNat]
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ Real.exp |z.im| := by
        rw [h1, h2]
        have a1 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
        have a2 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
        linarith


/-- The holomorphic extension of the cosine series of `R` to a horizontal strip. -/
noncomputable def RsechC (lam : ℝ) (z : ℂ) : ℂ :=
  1 / 2 + ∑' n : ℕ, (secCoeff lam n : ℂ) * Complex.cos (((n + 1 : ℕ) : ℂ) * z)

theorem differentiableOn_RsechC {lam : ℝ} (hlam : 0 < lam) :
    DifferentiableOn ℂ (RsechC lam) {z : ℂ | |z.im| < lam / 2} := by
  have hr : 0 < Real.exp (-(lam / 2)) := Real.exp_pos _
  have hr1 : Real.exp (-(lam / 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hu : Summable (fun n : ℕ => 2 * Real.exp (-(lam / 2)) ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-(lam / 2)))
    exact this.congr fun n => by ring
  have hopen : IsOpen {z : ℂ | |z.im| < lam / 2} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have h := Complex.differentiableOn_tsum_of_summable_norm (U := {z : ℂ | |z.im| < lam / 2})
    (F := fun (n : ℕ) (z : ℂ) => (secCoeff lam n : ℂ) * Complex.cos (((n + 1 : ℕ) : ℂ) * z)) hu
    (fun n => (by fun_prop : Differentiable ℂ (fun z : ℂ =>
      (secCoeff lam n : ℂ) * Complex.cos (((n + 1 : ℕ) : ℂ) * z))).differentiableOn)
    hopen
    (fun n z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (secCoeff_pos lam n)]
      have h1 := norm_cos_le_exp_abs_im (((n + 1 : ℕ) : ℂ) * z)
      have h2 : |(((n + 1 : ℕ) : ℂ) * z).im| ≤ ((n + 1 : ℕ) : ℝ) * (lam / 2) := by
        have : (((n + 1 : ℕ) : ℂ) * z).im = ((n + 1 : ℕ) : ℝ) * z.im := by
          rw [Complex.mul_im]; simp
        rw [this, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (le_of_lt hz) (Nat.cast_nonneg _)
      have h3 : Real.exp |(((n + 1 : ℕ) : ℂ) * z).im| ≤ Real.exp (lam / 2) ^ (n + 1) := by
        calc Real.exp |(((n + 1 : ℕ) : ℂ) * z).im| ≤ Real.exp (((n + 1 : ℕ) : ℝ) * (lam / 2)) :=
              Real.exp_le_exp.2 h2
          _ = Real.exp (lam / 2) ^ (n + 1) := by rw [← Real.exp_nat_mul]
      have h4 := secCoeff_le hlam n
      have h5 : 2 * Real.exp (-(lam / 2)) ^ (n + 1) =
          2 * Real.exp (-lam) ^ (n + 1) * Real.exp (lam / 2) ^ (n + 1) := by
        rw [mul_assoc, ← mul_pow, ← Real.exp_add]; congr 2; ring_nf
      rw [h5]
      calc secCoeff lam n * ‖Complex.cos (((n + 1 : ℕ) : ℂ) * z)‖
          ≤ (2 * Real.exp (-lam) ^ (n + 1)) * Real.exp (lam / 2) ^ (n + 1) := by
            apply mul_le_mul h4 (h1.trans h3) (norm_nonneg _) (by positivity))
  unfold RsechC
  exact (differentiableOn_const _).add h


theorem RsechC_ofReal {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    RsechC lam (α : ℂ) = ((Rsech lam α : ℝ) : ℂ) := by
  have h := Rsech_eq_trigSeries hlam α
  unfold trigSeries at h
  have e : ∀ n : ℕ, secCoeff lam n * Real.cos (((n + 1 : ℕ) : ℝ) * α) +
      (fun _ : ℕ => (0 : ℝ)) n * Real.sin (((n + 1 : ℕ) : ℝ) * α) =
      secCoeff lam n * Real.cos (((n + 1 : ℕ) : ℝ) * α) := fun n => by simp
  simp_rw [e] at h
  rw [h]
  unfold RsechC
  push_cast
  rfl

/-- `α ↦ R_λ(α)` is real analytic. -/
theorem analyticAt_Rsech {lam : ℝ} (hlam : 0 < lam) (α : ℝ) : AnalyticAt ℝ (Rsech lam) α := by
  have hU : {z : ℂ | |z.im| < lam / 2} ∈ 𝓝 (α : ℂ) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    · simp; positivity
  have h1 : AnalyticAt ℂ (RsechC lam) (α : ℂ) := (differentiableOn_RsechC hlam).analyticAt hU
  have h2 := h1.re_ofReal
  have e : (fun x : ℝ => (RsechC lam (x : ℂ)).re) = Rsech lam := by
    funext x; rw [RsechC_ofReal hlam, Complex.ofReal_re]
  rwa [e] at h2

theorem analyticAt_Xi {lam : ℝ} (hlam : 0 < lam) (α : ℝ) : AnalyticAt ℝ (Xi lam) α := by
  unfold Xi
  have h2 : 1 < Real.cosh lam := Real.one_lt_cosh.mpr hlam.ne'
  have := Real.cos_le_one α
  exact analyticAt_const.div (analyticAt_const.sub Real.analyticAt_cos) (by linarith)

/-- **Analyticity of `ρ_Δ` in `x`** (fixed `Δ < -1`). -/
theorem analyticAt_rho {Δ : ℝ} (hΔ : Δ < -1) (x : ℝ) : AnalyticAt ℝ (rho Δ) x := by
  have hlam := lamOf_pos hΔ
  have hk := analyticAt_kInv hlam x
  have hR : AnalyticAt ℝ (fun y => Rsech (lamOf Δ) (kInv (lamOf Δ) y)) x :=
    (analyticAt_Rsech hlam (kInv (lamOf Δ) x)).comp hk
  have hX : AnalyticAt ℝ (fun y => Xi (lamOf Δ) (kInv (lamOf Δ) y)) x :=
    (analyticAt_Xi hlam (kInv (lamOf Δ) x)).comp hk
  have : rho Δ = fun y => Rsech (lamOf Δ) (kInv (lamOf Δ) y) /
      (2 * π * Xi (lamOf Δ) (kInv (lamOf Δ) y)) := funext (rho_eq hΔ)
  rw [this]
  refine hR.div (analyticAt_const.mul hX) ?_
  have := Xi_pos hlam (kInv (lamOf Δ) x)
  positivity


/-! ### Joint continuity in `(Δ, x)` -/

theorem continuousOn_kInv_joint :
    ContinuousOn (fun p : ℝ × ℝ => kInv p.1 p.2) {p : ℝ × ℝ | 0 < p.1} := by
  unfold kInv
  refine continuousOn_snd.sub (continuousOn_const.mul (Real.continuous_arctan.comp_continuousOn ?_))
  refine (Real.continuous_sin.comp_continuousOn continuousOn_snd).div
    ((Real.continuous_exp.comp_continuousOn continuousOn_fst).add
      (Real.continuous_cos.comp_continuousOn continuousOn_snd)) ?_
  intro p hp
  exact (exp_add_cos_pos hp p.2).ne'

theorem continuousOn_Xi_joint :
    ContinuousOn (fun p : ℝ × ℝ => Xi p.1 p.2) {p : ℝ × ℝ | 0 < p.1} := by
  unfold Xi
  refine (Real.continuous_sinh.comp_continuousOn continuousOn_fst).div
    ((Real.continuous_cosh.comp_continuousOn continuousOn_fst).sub
      (Real.continuous_cos.comp_continuousOn continuousOn_snd)) ?_
  intro p hp
  have h2 : 1 < Real.cosh p.1 := Real.one_lt_cosh.mpr (ne_of_gt hp)
  have := Real.cos_le_one p.2
  linarith

theorem Rsech_eq_tsum_cos {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Rsech lam α = 1 / 2 + ∑' n : ℕ, secCoeff lam n * Real.cos (((n + 1 : ℕ) : ℝ) * α) := by
  have h := Rsech_eq_trigSeries hlam α
  unfold trigSeries at h
  have e : ∀ n : ℕ, secCoeff lam n * Real.cos (((n + 1 : ℕ) : ℝ) * α) +
      (fun _ : ℕ => (0 : ℝ)) n * Real.sin (((n + 1 : ℕ) : ℝ) * α) =
      secCoeff lam n * Real.cos (((n + 1 : ℕ) : ℝ) * α) := fun n => by simp
  simp_rw [e] at h
  exact h

theorem continuousOn_Rsech_joint :
    ContinuousOn (fun p : ℝ × ℝ => Rsech p.1 p.2) {p : ℝ × ℝ | 0 < p.1} := by
  intro p₀ hp₀
  have hp₀' : 0 < p₀.1 := hp₀
  set L : ℝ := p₀.1 / 2 with hL
  have hL0 : 0 < L := by positivity
  have hr : 0 < Real.exp (-L) := Real.exp_pos _
  have hr1 : Real.exp (-L) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hu : Summable (fun n : ℕ => 2 * Real.exp (-L) ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one hr.le hr1).mul_left (2 * Real.exp (-L))
    exact this.congr fun n => by ring
  have hS : ContinuousOn (fun p : ℝ × ℝ => 1 / 2 + ∑' n : ℕ,
      secCoeff p.1 n * Real.cos (((n + 1 : ℕ) : ℝ) * p.2)) {p : ℝ × ℝ | L ≤ p.1} := by
    refine continuousOn_const.add (continuousOn_tsum (fun n => ?_) hu (fun n p hp => ?_))
    · unfold secCoeff
      refine ContinuousOn.mul ?_ (Real.continuous_cos.comp_continuousOn
        (continuousOn_const.mul continuousOn_snd))
      refine continuousOn_const.div (Real.continuous_cosh.comp_continuousOn
        (continuousOn_fst.mul continuousOn_const)) (fun p _ => (Real.cosh_pos _).ne')
    · have hp' : (0 : ℝ) < p.1 := lt_of_lt_of_le hL0 hp
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (secCoeff_pos p.1 n)]
      have h1 := secCoeff_le hp' n
      have h2 : Real.exp (-p.1) ^ (n + 1) ≤ Real.exp (-L) ^ (n + 1) := by
        gcongr
        exact hp
      calc secCoeff p.1 n * |Real.cos (((n + 1 : ℕ) : ℝ) * p.2)|
          ≤ secCoeff p.1 n * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (secCoeff_pos p.1 n).le
        _ ≤ 2 * Real.exp (-L) ^ (n + 1) := by rw [mul_one]; linarith
  have hnhds : {p : ℝ × ℝ | L ≤ p.1} ∈ 𝓝 p₀ := by
    have : {p : ℝ × ℝ | L < p.1} ∈ 𝓝 p₀ :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds (by simp [hL]; linarith)
    exact Filter.mem_of_superset this (fun p (hp : L < p.1) => hp.le)
  have hca : ContinuousAt (fun p : ℝ × ℝ => 1 / 2 + ∑' n : ℕ,
      secCoeff p.1 n * Real.cos (((n + 1 : ℕ) : ℝ) * p.2)) p₀ := hS.continuousAt hnhds
  have heq : (fun p : ℝ × ℝ => Rsech p.1 p.2) =ᶠ[𝓝 p₀] (fun p : ℝ × ℝ => 1 / 2 + ∑' n : ℕ,
      secCoeff p.1 n * Real.cos (((n + 1 : ℕ) : ℝ) * p.2)) := by
    have : {p : ℝ × ℝ | 0 < p.1} ∈ 𝓝 p₀ := (isOpen_lt continuous_const continuous_fst).mem_nhds hp₀
    filter_upwards [this] with p hp
    exact Rsech_eq_tsum_cos hp p.2
  exact (hca.congr heq.symm).continuousWithinAt

theorem continuousOn_lamOf : ContinuousOn lamOf {Δ : ℝ | Δ < -1} := by
  intro Δ hΔ
  have h : AnalyticAt ℝ Real.arcosh (-Δ) := Real.analyticAt_arcosh (by simp at hΔ ⊢; linarith)
  have h2 : ContinuousAt (fun Δ : ℝ => Real.arcosh (-Δ)) Δ :=
    h.continuousAt.comp (continuous_neg.continuousAt)
  exact h2.continuousWithinAt

/-- **Joint continuity** of `(Δ, x) ↦ ρ_Δ(x)` on `{Δ < -1} × ℝ`. -/
theorem continuousOn_rho_joint :
    ContinuousOn (fun p : ℝ × ℝ => rho p.1 p.2) {p : ℝ × ℝ | p.1 < -1} := by
  have hlam : ContinuousOn (fun p : ℝ × ℝ => lamOf p.1) {p : ℝ × ℝ | p.1 < -1} :=
    continuousOn_lamOf.comp continuousOn_fst (fun p hp => hp)
  have hpos : Set.MapsTo (fun p : ℝ × ℝ => (lamOf p.1, p.2)) {p : ℝ × ℝ | p.1 < -1}
      {p : ℝ × ℝ | 0 < p.1} := fun p hp => lamOf_pos hp
  have hpair : ContinuousOn (fun p : ℝ × ℝ => (lamOf p.1, p.2)) {p : ℝ × ℝ | p.1 < -1} :=
    hlam.prodMk continuousOn_snd
  have hk : ContinuousOn (fun p : ℝ × ℝ => kInv (lamOf p.1) p.2) {p : ℝ × ℝ | p.1 < -1} :=
    continuousOn_kInv_joint.comp hpair hpos
  have hpair2 : ContinuousOn (fun p : ℝ × ℝ => (lamOf p.1, kInv (lamOf p.1) p.2))
      {p : ℝ × ℝ | p.1 < -1} := hlam.prodMk hk
  have hpos2 : Set.MapsTo (fun p : ℝ × ℝ => (lamOf p.1, kInv (lamOf p.1) p.2))
      {p : ℝ × ℝ | p.1 < -1} {p : ℝ × ℝ | 0 < p.1} := fun p hp => lamOf_pos hp
  have hR := continuousOn_Rsech_joint.comp hpair2 hpos2
  have hX := continuousOn_Xi_joint.comp hpair2 hpos2
  have hden : ContinuousOn (fun p : ℝ × ℝ => 2 * π * Xi (lamOf p.1) (kInv (lamOf p.1) p.2))
      {p : ℝ × ℝ | p.1 < -1} := continuousOn_const.mul hX
  have hdiv := hR.div hden (fun p hp => by
    have := Xi_pos (lamOf_pos (show p.1 < -1 from hp)) (kInv (lamOf p.1) p.2)
    positivity)
  exact hdiv.congr (fun p hp => rho_eq (show p.1 < -1 from hp) p.2)

end PottsDiscontinuity.Bethe
