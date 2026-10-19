module

public import PottsDiscontinuity.Bethe.Theorem23Derivative
public import PottsDiscontinuity.Bethe.DiscreteBase
public import PottsDiscontinuity.Bethe.Theorem23Kernel

/-! # Coordinate residual at the compactified parameter -/

@[expose] public section

open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- The coordinate residual at epsilon = 1/Delta, including epsilon = 0. -/
noncomputable def discreteCoordinateResidualInv (ε : ℝ) (N n : ℕ)
    (q : Fin (n / 2) → ℝ) : Fin (n / 2) → ℝ := fun i =>
  q i - discreteBetheMapInv ε N n (discreteSymLift n q) (discreteHalfIndex n i)

theorem analyticAt_discreteCoordinateResidualInv {ε : ℝ} (hε : |ε| < 1)
    (N n : ℕ) (q : Fin (n / 2) → ℝ) :
    AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
      discreteCoordinateResidualInv z.1 N n z.2) (ε, q) := by
  have hlift : AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) => discreteSymLift n z.2) (ε, q) :=
    (discreteSymLift n).toContinuousLinearMap.analyticAt _ |>.comp analyticAt_snd
  have hm : AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
      discreteBetheMapInv z.1 N n (discreteSymLift n z.2)) (ε, q) :=
    AnalyticAt.comp (g := fun z : ℝ × (Fin n → ℝ) => discreteBetheMapInv z.1 N n z.2)
      (f := fun z : ℝ × (Fin (n / 2) → ℝ) => (z.1, discreteSymLift n z.2))
      (analyticAt_discreteBetheMapInv hε N n _) (analyticAt_fst.prod hlift)
  apply AnalyticAt.pi
  intro i
  have hqi : AnalyticAt ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) => z.2 i) (ε, q) :=
    ((ContinuousLinearMap.proj i : (Fin (n / 2) → ℝ) →L[ℝ] ℝ).analyticAt _).comp analyticAt_snd
  exact hqi.sub (((ContinuousLinearMap.proj (discreteHalfIndex n i) :
    (Fin n → ℝ) →L[ℝ] ℝ).analyticAt _).comp hm)

/-- Restricting the Frechet derivative to the state direction is the derivative
of the fixed-parameter slice. -/
theorem stateDerivative_eq_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × E → E} {t : ℝ} {q : E} (hf : DifferentiableAt ℝ F (t, q)) :
    (fderiv ℝ F (t, q)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      fderiv ℝ (fun v => F (t, v)) q :=
  (hf.hasFDerivAt.comp q (hasFDerivAt_prodMk_right t q)).fderiv.symm

theorem discreteCoordinateResidualInv_eq {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ℕ) (q : Fin (n / 2) → ℝ) :
    discreteCoordinateResidualInv (1 / Δ) N n q = discreteCoordinateResidual Δ N n q := by
  funext i
  simp only [discreteCoordinateResidualInv, discreteCoordinateResidual,
    discreteBetheResidual, discreteSymLift_half, discreteBetheMap_eq_inv hΔ]

/-- The inverse-parameter state derivative agrees with the finite-parameter
Jacobian. Parameter differentiation is not involved in this equality. -/
theorem discreteCoordinateResidualInv_stateDerivative {Δ : ℝ} (hΔ : Δ < -1)
    (N n : ℕ) (q : Fin (n / 2) → ℝ) :
    (fderiv ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
      discreteCoordinateResidualInv z.1 N n z.2) (1 / Δ, q)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Fin (n / 2) → ℝ)) =
      (Matrix.toLin' (discreteBetheMatrixA Δ N n (discreteSymLift n q))).toContinuousLinearMap := by
  rw [stateDerivative_eq_slice
    (analyticAt_discreteCoordinateResidualInv (abs_inverse_parameter_lt_one hΔ) N n q).differentiableAt]
  have heq : discreteCoordinateResidualInv (1 / Δ) N n = discreteCoordinateResidual Δ N n :=
    funext (discreteCoordinateResidualInv_eq hΔ N n)
  dsimp only
  have hs := stateDerivative_eq_slice
    (analyticAt_discreteCoordinateResidual hΔ N n q).differentiableAt
  dsimp only at hs
  rw [heq, ← hs]
  exact discreteCoordinateResidual_stateDerivative hΔ N n q

/-- At epsilon=0 the residual is the explicit affine scalar map. -/
theorem discreteCoordinateResidualInv_zero (N n : ℕ) (q : Fin (n / 2) → ℝ) :
    discreteCoordinateResidualInv 0 N n q = fun i =>
      (1 - (n : ℝ) / N) * q i - 2 * Real.pi * discreteBetheIndex n (discreteHalfIndex n i) / N := by
  have hsum := sum_eq_zero_of_mem_R_n_sym (discreteSymLift_mem n q)
  funext i
  simp only [discreteCoordinateResidualInv, discreteBetheMapInv, thetaInv_zero,
    Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, discreteSymLift_half]
  ring

/-- The state derivative at epsilon=0 is scalar multiplication by `1-n/N`. -/
theorem discreteCoordinateResidualInv_stateDerivative_zero (N n : ℕ)
    (q : Fin (n / 2) → ℝ) :
    (fderiv ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
      discreteCoordinateResidualInv z.1 N n z.2) (0, q)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Fin (n / 2) → ℝ)) =
      (1 - (n : ℝ) / N) • ContinuousLinearMap.id ℝ (Fin (n / 2) → ℝ) := by
  rw [stateDerivative_eq_slice
    (analyticAt_discreteCoordinateResidualInv (by norm_num : |(0 : ℝ)| < 1) N n q).differentiableAt]
  dsimp only
  let b : Fin (n / 2) → ℝ := fun i =>
    2 * Real.pi * discreteBetheIndex n (discreteHalfIndex n i) / N
  have heq : discreteCoordinateResidualInv 0 N n =
      fun v => (1 - (n : ℝ) / N) • v - b := by
    funext v
    exact discreteCoordinateResidualInv_zero N n v
  rw [heq]
  exact (((hasFDerivAt_id q).const_smul (1 - (n : ℝ) / N)).sub_const b).fderiv

theorem exists_discreteCoordinateResidualInv_stateEquiv_zero {N n : ℕ}
    (hN : 0 < N) (hs : 2 * n ≤ N) (q : Fin (n / 2) → ℝ) :
    ∃ e : (Fin (n / 2) → ℝ) ≃L[ℝ] (Fin (n / 2) → ℝ),
      (fderiv ℝ (fun z : ℝ × (Fin (n / 2) → ℝ) =>
        discreteCoordinateResidualInv z.1 N n z.2) (0, q)).comp
          (ContinuousLinearMap.inr ℝ ℝ (Fin (n / 2) → ℝ)) =
        (e : (Fin (n / 2) → ℝ) →L[ℝ] (Fin (n / 2) → ℝ)) := by
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hnN : (n : ℝ) < N := by exact_mod_cast (show n < N by omega)
  have ha : 0 < 1 - (n : ℝ) / N := sub_pos.mpr ((div_lt_one hNc).2 hnN)
  let e := (LinearEquiv.smulOfNeZero ℝ (Fin (n / 2) → ℝ)
    (1 - (n : ℝ) / N) ha.ne').toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  rw [discreteCoordinateResidualInv_stateDerivative_zero]
  rfl

end PottsDiscontinuity.Bethe
