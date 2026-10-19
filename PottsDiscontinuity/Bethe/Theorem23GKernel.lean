module

public import PottsDiscontinuity.Bethe.Theorem23Kernel
public import PottsDiscontinuity.Bethe.DiscreteJacobian

/-! # Uniform bounds for the kernel in the Jacobian row sums -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

/-- Antisymmetry exchanges the two partial derivatives. -/
theorem thetaPartialSecond_eq_neg_d1Theta {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    thetaPartialSecond Δ x y = -d1Theta Δ y x := by
  have heq : (fun t => theta Δ x t) = fun t => -theta Δ t x :=
    funext fun t => theta_swap Δ t x
  unfold thetaPartialSecond d1Theta
  rw [heq]
  exact ((analyticAt_theta_left hΔ y x).differentiableAt.hasDerivAt.neg).deriv

/-- Bounds and a modulus of continuity for the derivative of `G`, uniform in
the entire antiferroelectric parameter range. -/
theorem exists_uniform_discreteBetheG_deriv_bounds {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ ≤ Δ₀,
      (∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi,
        |deriv (fun t => discreteBetheG Δ x t) y| ≤ C) ∧
      (∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi,
        ∀ z ∈ Icc (-Real.pi) Real.pi,
        |deriv (fun t => discreteBetheG Δ x t) y -
          deriv (fun t => discreteBetheG Δ x t) z| ≤ C * |y - z|) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_d1Theta_bounds hΔ₀
  refine ⟨2 * C, by positivity, fun Δ hΔ => ?_⟩
  have hvalid := lt_of_le_of_lt hΔ hΔ₀
  have hneg {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
      -x ∈ Icc (-Real.pi) Real.pi := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have heq (x y : ℝ) : deriv (fun t => discreteBetheG Δ x t) y =
      -d1Theta Δ y x + d1Theta Δ y (-x) := by
    rw [deriv_discreteBetheG_right hvalid,
      thetaPartialSecond_eq_neg_d1Theta hvalid,
      thetaPartialSecond_eq_neg_d1Theta hvalid]
    ring
  constructor
  · intro x hx y hy
    rw [heq]
    calc
      _ ≤ |-d1Theta Δ y x| + |d1Theta Δ y (-x)| := abs_add_le _ _
      _ ≤ C + C := by
        rw [abs_neg]
        exact add_le_add ((hb Δ hΔ).1 y hy x hx).1
          ((hb Δ hΔ).1 y hy (-x) (hneg hx)).1
      _ = _ := by ring
  · intro x hx y hy z hz
    rw [heq, heq]
    have h₁ := (hb Δ hΔ).2 y hy x hx z hz x hx
    have h₂ := (hb Δ hΔ).2 y hy (-x) (hneg hx) z hz (-x) (hneg hx)
    simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (y - z))] at h₁ h₂
    calc
      _ = |-(d1Theta Δ y x - d1Theta Δ z x) +
          (d1Theta Δ y (-x) - d1Theta Δ z (-x))| := by congr 1; ring
      _ ≤ |-(d1Theta Δ y x - d1Theta Δ z x)| +
          |d1Theta Δ y (-x) - d1Theta Δ z (-x)| := abs_add_le _ _
      _ ≤ C * |y-z| + C * |y-z| := by rw [abs_neg]; exact add_le_add h₁ h₂
      _ = _ := by ring

end PottsDiscontinuity.Bethe
