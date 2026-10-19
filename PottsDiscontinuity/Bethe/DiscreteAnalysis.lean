module

public import Mathlib
public import PottsDiscontinuity.Bethe.ThetaK

/-!
# Discrete Bethe matrix estimates independent of `ρ`

This file isolates the sign and calculus estimates for the phase difference used
in the discrete diagonal-dominance argument.  It does not include the later
Riemann-sum estimates involving `ρ`.
-/

@[expose] public section

open scoped BigOperators
open Set

namespace PottsDiscontinuity.Bethe

/-- The phase difference used to control the off-diagonal entries. -/
noncomputable def discreteBetheG (Δ x y : ℝ) : ℝ :=
  theta Δ x y - theta Δ (-x) y

/-- If the cosine argument is larger, the corresponding `Xi` kernel is larger. -/
theorem Xi_le_of_cos_le {μ a b : ℝ} (hμ : 0 < μ)
    (hcos : Real.cos b ≤ Real.cos a) : Xi μ b ≤ Xi μ a := by
  have hs : 0 < Real.sinh μ := Real.sinh_pos_iff.mpr hμ
  have hc : 1 < Real.cosh μ := Real.one_lt_cosh.mpr hμ.ne'
  have hda : 0 < Real.cosh μ - Real.cos a := by
    have := Real.cos_le_one a
    linarith
  have hdb : 0 < Real.cosh μ - Real.cos b := by
    have := Real.cos_le_one b
    linarith
  have hden : Real.cosh μ - Real.cos a ≤ Real.cosh μ - Real.cos b := by linarith
  unfold Xi
  exact (div_le_div_iff₀ hdb hda).2 (mul_le_mul_of_nonneg_left hden hs.le)

/-- The derivative of `G(k(α),k(β))` in `β`, written as a difference of two `Xi` kernels. -/
theorem hasDerivAt_discreteBetheG_kMap {Δ : ℝ} (hΔ : Δ < -1)
    (α β : ℝ) :
    HasDerivAt (fun t => discreteBetheG Δ (kMap (lamOf Δ) α) (kMap (lamOf Δ) t))
      (Xi (2 * lamOf Δ) (α - β) - Xi (2 * lamOf Δ) (-α - β)) β := by
  let lam := lamOf Δ
  have hlam : 0 < lam := lamOf_pos hΔ
  have hfun : (fun t => discreteBetheG Δ (kMap lam α) (kMap lam t)) =
      fun t => kMap (2 * lam) (-α - t) - kMap (2 * lam) (α - t) := by
    funext t
    unfold discreteBetheG
    rw [← kMap_neg lam α]
    rw [theta_kMap_lamOf hΔ α t, theta_kMap_lamOf hΔ (-α) t]
    ring
  rw [hfun]
  have harg₁ : HasDerivAt (fun t : ℝ => -α - t) (-1) β := by
    change HasDerivAt ((fun _ : ℝ => -α) - id) (-1) β
    simpa only [zero_sub] using (hasDerivAt_const β (-α)).sub (hasDerivAt_id β)
  have harg₂ : HasDerivAt (fun t : ℝ => α - t) (-1) β := by
    change HasDerivAt ((fun _ : ℝ => α) - id) (-1) β
    simpa only [zero_sub] using (hasDerivAt_const β α).sub (hasDerivAt_id β)
  have h₁ := (hasDerivAt_kMap (by linarith : 0 < 2 * lam) (-α - β)).comp β harg₁
  have h₂ := (hasDerivAt_kMap (by linarith : 0 < 2 * lam) (α - β)).comp β harg₂
  have hsum := h₁.sub h₂
  convert hsum using 1
  · funext t
    rfl
  · simp only [lam]
    ring

/-- The endpoint difference of `G` has a one-arctangent closed form. -/
theorem discreteBetheG_endpoint_formula {Δ : ℝ} (hΔ : Δ < -1)
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) 0) :
    discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
      4 * Real.arctan ((-Real.sin x) /
        (2 * (-Δ) * (Real.cos x - Δ))) := by
  let t := -Real.sin x
  let dm := Real.cos x - 1 - 2 * Δ
  let dp := Real.cos x + 1 - 2 * Δ
  have hsin : Real.sin x ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 hx.1
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hdm : 0 < dm := by
    dsimp [dm]
    have hc := Real.neg_one_le_cos x
    linarith
  have hdp : 0 < dp := by
    dsimp [dp]
    have hc := Real.neg_one_le_cos x
    linarith
  have hraw : discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
      4 * (Real.arctan (Real.sin x / dp) - Real.arctan (Real.sin x / dm)) := by
    unfold discreteBetheG theta
    simp only [Real.sin_zero, Real.cos_zero, Real.sin_neg, Real.cos_neg,
      Real.sin_pi, Real.cos_pi]
    simp only [sub_zero, neg_zero, neg_div, Real.arctan_neg]
    dsimp [dp, dm]
    ring_nf
  have hraw' : discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) =
      4 * (Real.arctan (t / dm) + Real.arctan (-t / dp)) := by
    rw [hraw, show Real.sin x = -t by dsimp [t]; ring]
    simp only [neg_div, Real.arctan_neg]
    ring
  rw [hraw']
  have hprod : (t / dm) * (-t / dp) < 1 := by
    have hleft : 0 ≤ t / dm := div_nonneg ht hdm.le
    have hright : -t / dp ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hdp.le
    have hmul : (t / dm) * (-t / dp) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hleft hright
    linarith
  rw [Real.arctan_add hprod]
  have harg_eq : (t / dm + -t / dp) / (1 - (t / dm) * (-t / dp)) =
      t / (2 * (-Δ) * (Real.cos x - Δ)) := by
    have hdmne : Real.cos x - 1 - 2 * Δ ≠ 0 := ne_of_gt hdm
    have hdpne : Real.cos x + 1 - 2 * Δ ≠ 0 := ne_of_gt hdp
    have hΔne : Δ ≠ 0 := ne_of_lt (lt_trans hΔ (by norm_num))
    have hcos : 0 < Real.cos x - Δ := by
      have hc := Real.neg_one_le_cos x
      linarith
    have hden : 2 * (-Δ) * (Real.cos x - Δ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num)
        (ne_of_gt (by linarith : 0 < -Δ))) hcos.ne'
    have hden2 : dm * dp + t ^ 2 ≠ 0 := by positivity
    have hdenid : dm * dp + t ^ 2 = 4 * (-Δ) * (Real.cos x - Δ) := by
      dsimp [dm, dp, t]
      nlinarith [Real.sin_sq_add_cos_sq x]
    field_simp [hdmne, hdpne, hden, hden2]
    rw [show dm * dp - -t ^ 2 = dm * dp + t ^ 2 by ring, hdenid]
    field_simp [hΔne, hcos.ne']
    ring
  exact congrArg (fun u : ℝ => 4 * Real.arctan u) harg_eq

/-- The calculus bound in Lemma 2.5.  Its constant is valid as printed when
`Δ ≤ Δ₀ < -1`; the source line stating only `Δ₀ < 1` is insufficient. -/
theorem discreteBetheG_endpoint_bound {Δ Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1)
    (hΔ : Δ ≤ Δ₀) {x : ℝ} (hx : x ∈ Icc (-Real.pi) 0) :
    discreteBetheG Δ x 0 - discreteBetheG Δ x (-Real.pi) ≤
      4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1))) ∧
    4 * Real.arctan (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1))) < 2 * Real.pi := by
  have hΔ : Δ < -1 := lt_of_le_of_lt hΔ hΔ₀
  rw [discreteBetheG_endpoint_formula hΔ hx]
  let d := -Δ
  let d₀ := -Δ₀
  let c := Real.cos x
  let t := -Real.sin x
  have hd₀ : 1 < d₀ := by dsimp [d₀]; linarith
  have hd : d₀ ≤ d := by dsimp [d, d₀]; linarith
  have hc : -1 ≤ c := by dsimp [c]; exact Real.neg_one_le_cos x
  have ht : 0 ≤ t := by
    dsimp [t]
    exact neg_nonneg.mpr (Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 hx.1)
  have hcd₀ : 0 < c + d₀ := by linarith
  have hcd : 0 < c + d := by linarith
  have hs₀ : 0 < d₀ ^ 2 - 1 := by nlinarith
  have hs : 0 < d ^ 2 - 1 := by nlinarith
  let w₀ := Real.sqrt (d₀ ^ 2 - 1)
  let w := Real.sqrt (d ^ 2 - 1)
  have hw₀ : 0 < w₀ := Real.sqrt_pos.mpr hs₀
  have hw : 0 < w := Real.sqrt_pos.mpr hs
  have hwle : w₀ ≤ w := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have htrig := Real.sin_sq_add_cos_sq x
  have hsquare : (t * w) ^ 2 ≤ (c + d) ^ 2 := by
    dsimp [t, c, w]
    rw [mul_pow, Real.sq_sqrt hs.le]
    nlinarith [sq_nonneg (Real.cos x * d + 1), Real.sin_sq_add_cos_sq x]
  have hroot : t * w ≤ c + d := by
    have hn : 0 ≤ t * w := mul_nonneg ht hw.le
    nlinarith
  have harg : t / (2 * d * (c + d)) ≤ 1 / (2 * d₀ * w₀) := by
    have hleft : t / (c + d) ≤ 1 / w :=
      (div_le_div_iff₀ hcd hw).2 (by nlinarith [hroot])
    have hdpos : 0 < d := lt_of_lt_of_le (by linarith : 0 < d₀) hd
    have hprod : d₀ * w₀ ≤ d * w := by
      exact mul_le_mul hd hwle (le_of_lt hw₀) (le_of_lt hdpos)
    have hden₀ : 0 < 2 * d₀ * w₀ := by positivity
    have hden : 0 < 2 * d * w := by positivity
    calc
      t / (2 * d * (c + d)) = (1 / (2 * d)) * (t / (c + d)) := by field_simp
      _ ≤ (1 / (2 * d)) * (1 / w) := by
        apply mul_le_mul_of_nonneg_left hleft
        positivity
      _ = 1 / (2 * d * w) := by field_simp
      _ ≤ 1 / (2 * d₀ * w₀) := by
        apply one_div_le_one_div_of_le hden₀
        nlinarith [mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)]
  have harg' : (-Real.sin x) / (2 * (-Δ) * (Real.cos x - Δ)) ≤
      1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1)) := by
    have habs : |Δ₀| = -Δ₀ := abs_of_neg (by linarith : Δ₀ < 0)
    have hleft : t / (2 * d * (c + d)) =
        (-Real.sin x) / (2 * (-Δ) * (Real.cos x - Δ)) := by
      dsimp [t, d, c]
      congr 2
    have hright : 1 / (2 * d₀ * w₀) =
        1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1)) := by
      rw [habs]
      dsimp [d₀, w₀]
      rw [show (-Δ₀) ^ 2 = Δ₀ ^ 2 by ring]
    rw [← hleft, ← hright]
    exact harg
  constructor
  · exact mul_le_mul_of_nonneg_left
      ((Real.arctan_le_arctan_iff).2 harg') (by norm_num)
  · have := Real.arctan_lt_pi_div_two
      (1 / (2 * |Δ₀| * Real.sqrt (Δ₀ ^ 2 - 1)))
    nlinarith [Real.pi_pos]

/-- Abstract Levy--Desplanques criterion: strict row diagonal dominance makes a real
square matrix invertible. -/
theorem discrete_strict_row_diagonal_dominance_invertible {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (h : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|) : A.det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  simpa only [Real.norm_eq_abs] using h i

end PottsDiscontinuity.Bethe
