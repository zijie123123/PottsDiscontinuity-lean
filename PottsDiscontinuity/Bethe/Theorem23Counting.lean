module

public import PottsDiscontinuity.Bethe.DiscreteCore
public import PottsDiscontinuity.Bethe.Prop21Rho
public import PottsDiscontinuity.Bethe.Theorem23Kernel

/-! # The smooth counting function in the proof of Lemma 2.4 -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- The function `f_p` of (2.8). -/
noncomputable def betheCountingFunction (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) (x : ℝ) : ℝ :=
  (x + (∑ j : Fin n, theta Δ x (p j)) / (N : ℝ)) / (2 * Real.pi)

/-- The explicit derivative of the counting function. -/
noncomputable def betheCountingDerivative (Δ : ℝ) (N n : ℕ) (p : Fin n → ℝ) (x : ℝ) : ℝ :=
  (1 + (∑ j : Fin n, d1Theta Δ x (p j)) / (N : ℝ)) / (2 * Real.pi)

theorem hasDerivAt_betheCountingFunction {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ℕ) (p : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (betheCountingFunction Δ N n p) (betheCountingDerivative Δ N n p x) x := by
  have hsum : HasDerivAt (fun t => ∑ j : Fin n, theta Δ t (p j))
      (∑ j : Fin n, d1Theta Δ x (p j)) x := by
    exact HasDerivAt.fun_sum (fun j _ => (analyticAt_theta_left hΔ x (p j)).differentiableAt.hasDerivAt)
  exact ((hasDerivAt_id x).add (hsum.div_const (N : ℝ))).div_const (2 * Real.pi)

theorem continuous_d1Theta_left {Δ : ℝ} (hΔ : Δ < -1) (y : ℝ) :
    Continuous (fun x => d1Theta Δ x y) := by
  apply continuous_iff_continuousAt.2
  intro x
  have ht : AnalyticAt ℝ (fun t : ℝ => ((1 / Δ, t, y) : ℝ × ℝ × ℝ)) x :=
    analyticAt_const.prod (analyticAt_id.prod analyticAt_const)
  have ha : AnalyticAt ℝ (fun t => thetaFirstInv (1 / Δ) t y) x :=
    AnalyticAt.comp (f := fun t : ℝ => ((1 / Δ, t, y) : ℝ × ℝ × ℝ))
      (g := fun z : ℝ × ℝ × ℝ => thetaFirstInv z.1 z.2.1 z.2.2)
      (analyticAt_thetaFirstInv (abs_inverse_parameter_lt_one hΔ) x y) ht
  have heq : (fun t => thetaFirstInv (1 / Δ) t y) = fun t => d1Theta Δ t y :=
    funext fun t => (d1Theta_eq_thetaFirstInv hΔ t y).symm
  rw [heq] at ha
  exact ha.continuousAt

theorem continuous_betheCountingDerivative {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ℕ) (p : Fin n → ℝ) : Continuous (betheCountingDerivative Δ N n p) := by
  exact (continuous_const.add
    ((continuous_finsetSum _ (fun j _ => continuous_d1Theta_left hΔ (p j))).div_const _)).div_const _

theorem densityNorm_bddAbove_of_continuous {Δ : ℝ} (hΔ : Δ < -1)
    {f : ℝ → ℝ} (hf : Continuous f) :
    BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|) := by
  have hc : Continuous (fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|) :=
    (((continuous_Xi (lamOf_pos hΔ)).comp continuous_subtype_val).mul
      (hf.comp ((continuous_kMap (lamOf_pos hΔ)).comp continuous_subtype_val))).abs
  exact (isCompact_range hc).bddAbove

theorem countingError_bddAbove {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ℕ) (p : Fin n → ℝ) :
    BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (betheCountingDerivative Δ N n p (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|) :=
  densityNorm_bddAbove_of_continuous hΔ
    ((continuous_betheCountingDerivative hΔ N n p).sub (continuous_rho hΔ))

theorem betheCountingFunction_root_value {Δ : ℝ} {N n : ℕ} (hN : 0 < N)
    (p : Fin n → ℝ) (hBE : DiscreteBetheEquation Δ N n p) (j : Fin n) :
    betheCountingFunction Δ N n p (p j) = discreteBetheIndex n j / (N : ℝ) := by
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have h := hBE j
  unfold betheCountingFunction
  field_simp [hNc]
  linarith

theorem betheCountingFunction_period {Δ : ℝ} {N n : ℕ} (hN : 0 < N)
    (p : Fin n → ℝ) (x : ℝ) :
    betheCountingFunction Δ N n p (x + 2 * Real.pi) =
      betheCountingFunction Δ N n p x + ((N : ℝ) - (n : ℝ)) / (N : ℝ) := by
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold betheCountingFunction
  simp_rw [theta_add_two_pi_left]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hNc]
  ring

end PottsDiscontinuity.Bethe
