module

public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# First derivative of the corrected T₁ phase

For an ordinary ML edge, the paired quotient is
`-exp(i(Θ(t,p)-Θ(0,p)))`. At the cyclic seam it has the additional exponent
`iNt`. This module records its derivative, including the seam contribution.
-/

@[expose] public section

open Complex

namespace PottsDiscontinuity.BetheAnsatz

/-- The corrected real phase increment in the T₁ pair ratio. -/
noncomputable def zeroRootPhaseExponent {N : ℕ} (Δ p : ℝ) (seam : Prop)
    [Decidable seam] : ℝ → ℝ :=
  (fun t => Bethe.theta Δ t p) - (fun _ => Bethe.theta Δ 0 p) +
    if seam then (fun t => (N : ℝ) * t) else 0

/-- The first-order coefficient of the corrected T₁ exponent. -/
noncomputable def zeroRootPhaseDerivative {N : ℕ} (Δ p : ℝ) (seam : Prop)
    [Decidable seam] : ℝ :=
  deriv (fun t => Bethe.theta Δ t p) 0 + if seam then (N : ℝ) else 0

/-- The exponential of the corrected T₁ phase has derivative `i` times its real slope. -/
theorem hasDerivAt_zeroRootPhaseExp {N : ℕ} {c p : ℝ} (hc : 2 < c)
    (seam : Prop) [Decidable seam] :
    HasDerivAt
      (fun t : ℝ => Complex.exp
        (I * (zeroRootPhaseExponent (N := N) (anisotropy c) p seam t : ℂ)))
      (I * (zeroRootPhaseDerivative (N := N) (anisotropy c) p seam : ℂ)) 0 := by
  let θ : ℝ → ℝ := fun t => Bethe.theta (anisotropy c) t p
  let dθ : ℝ := deriv θ 0
  have hθ :=
    (Bethe.analyticAt_theta_left (anisotropy_lt_neg_one hc) 0 p).differentiableAt.hasDerivAt
  have hshift := hθ.sub_const (θ 0)
  have hshiftC := hshift.ofReal_comp
  have htime : HasDerivAt (fun t : ℝ => (N : ℝ) * t) (N : ℝ) 0 := by
    simpa [mul_comm] using (hasDerivAt_id (0 : ℝ)).const_mul (N : ℝ)
  have htimeC := htime.ofReal_comp
  have hδC : HasDerivAt
      (fun t : ℝ => (zeroRootPhaseExponent (N := N) (anisotropy c) p seam t : ℂ))
      (zeroRootPhaseDerivative (N := N) (anisotropy c) p seam : ℂ) 0 := by
    by_cases hs : seam
    · have h := hshiftC.add htimeC
      convert h using 1
      · ext t
        simp [zeroRootPhaseExponent, θ, hs, Complex.ofReal_add, Complex.ofReal_mul, mul_comm]
      · simp [zeroRootPhaseDerivative, hs]
    · convert hshiftC using 1
      · ext t
        simp [zeroRootPhaseExponent, θ, hs]
      · simp [zeroRootPhaseDerivative, hs]
  have hδ0 : zeroRootPhaseExponent (N := N) (anisotropy c) p seam 0 = 0 := by
    by_cases hs : seam <;> simp [zeroRootPhaseExponent, hs]
  have hlin := hδC.const_mul I
  have hlin' : HasDerivAt
      (fun t : ℝ => I * (zeroRootPhaseExponent (N := N) (anisotropy c) p seam t : ℂ))
      (I * (zeroRootPhaseDerivative (N := N) (anisotropy c) p seam : ℂ)) 0 := by
    simpa [mul_comm] using hlin
  have houter := Complex.hasDerivAt_exp (0 : ℂ)
  have hcomp := HasDerivAt.comp_of_eq (0 : ℝ) houter hlin' (by simp [hδ0])
  simpa only [Function.comp_def, hδ0, Complex.exp_zero, one_mul] using hcomp

end PottsDiscontinuity.BetheAnsatz
