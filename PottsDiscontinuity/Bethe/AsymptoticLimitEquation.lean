module

public import PottsDiscontinuity.Bethe.AsymptoticLimitTools
public import PottsDiscontinuity.Bethe.Prop21Tau

/-! # Identification of the limiting offset equation -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

/-- Uniqueness for a scalar multiple of (cOE), including the homogeneous
case. Adding `(1-r)τ` avoids dividing by `r`. -/
theorem eq_mul_tauCont_of_scaled_cOE {Δ r : ℝ} (hΔ : Δ < -1)
    {g : ℝ → ℝ} (hg : Continuous g)
    (heq : ∀ x ∈ Icc (-Real.pi) Real.pi,
      2 * Real.pi * g x = r * (theta Δ x (-Real.pi) + theta Δ x Real.pi) / 2 -
        ∫ y in (-Real.pi)..Real.pi, d2Theta Δ x y * g y) :
    ∀ x ∈ Icc (-Real.pi) Real.pi, g x = r * tauCont Δ x := by
  let h : ℝ → ℝ := fun x => g x + (1 - r) * tauCont Δ x
  have hh : Continuous h := hg.add ((continuous_tauCont hΔ).const_mul (1 - r))
  have hcoe : IsCOESolution Δ h := by
    intro x hx
    have hθ : Continuous (fun y => d2Theta Δ x y) :=
      (continuous_d2Theta_pair hΔ).comp (continuous_const.prodMk continuous_id)
    have hgi : IntervalIntegrable (fun y => d2Theta Δ x y * g y) volume (-Real.pi) Real.pi :=
      (hθ.mul hg).intervalIntegrable (-Real.pi) Real.pi
    have hτi : IntervalIntegrable (fun y => d2Theta Δ x y * tauCont Δ y) volume (-Real.pi) Real.pi :=
      (hθ.mul (continuous_tauCont hΔ)).intervalIntegrable (-Real.pi) Real.pi
    have hτ := tauCont_isCOESolution hΔ x hx
    unfold cOEop at hτ ⊢
    have hτ' := congrArg (fun z : ℝ => (1 - r) * z) hτ
    have hfun : (fun y => d2Theta Δ x y * h y) =
        fun y => d2Theta Δ x y * g y + (1 - r) * (d2Theta Δ x y * tauCont Δ y) := by
      funext y
      dsimp [h]
      ring
    rw [hfun, intervalIntegral.integral_add hgi (hτi.const_mul (1 - r)),
      intervalIntegral.integral_const_mul]
    dsimp [h]
    nlinarith only [heq x hx, hτ']
  have hid := eq_tauCont_of_isCOESolution_of_integrableOn hΔ
    (integrableOn_Icc_of_continuous hh) hcoe
  intro x hx
  have hi := hid x hx
  dsimp [h] at hi
  nlinarith only [hi]

end PottsDiscontinuity.Bethe
