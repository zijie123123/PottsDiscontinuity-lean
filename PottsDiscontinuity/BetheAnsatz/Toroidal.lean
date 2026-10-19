module

public import PottsDiscontinuity.BetheAnsatz.Cyclic
public import PottsDiscontinuity.BetheAnsatz.OneParticle

/-!
# Toroidal change of variables

Companion paper, Proposition `prop:changeOfVariables`. The test function is allowed to
be complex valued, as required by the later use in Lemma T₀. Positions may be arbitrary
integers. If `x` is increasing, the shifted positions are `(x_last-N,x_0,...,x_penultimate)`.
-/

@[expose] public section

open Finset Complex

namespace PottsDiscontinuity.BetheAnsatz

/-- The predecessor coordinates on the universal cover of the periodic row. -/
def cyclicPredecessorPositions {n : ℕ} (N : ℕ) (x : Fin (n + 1) → ℤ) :
    Fin (n + 1) → ℤ :=
  fun k => x ((finRotate (n + 1)).symm k) - if k = 0 then (N : ℤ) else 0

/-- Permuting momenta cyclically is the inverse permutation of the coordinates. -/
theorem planeWave_rotate {n : ℕ} (p : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (x : Fin (n + 1) → ℤ) :
    planeWave p (σ * finRotate (n + 1)) x =
      planeWave p σ (fun k => x ((finRotate (n + 1)).symm k)) := by
  unfold planeWave
  simpa only [Equiv.Perm.mul_apply, Equiv.symm_apply_apply] using
    (Equiv.prod_comp (finRotate (n + 1)) (fun k =>
      Complex.exp (I * (p (σ k) : ℂ) * (x ((finRotate (n + 1)).symm k) : ℂ))))

/-- The wraparound coordinate contributes precisely the inverse Bethe boundary phase. -/
theorem planeWave_cyclicPredecessorPositions {n : ℕ} (N : ℕ) (p : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (x : Fin (n + 1) → ℤ) :
    planeWave p σ (cyclicPredecessorPositions N x) =
      planeWave p (σ * finRotate (n + 1)) x * (z (p (σ 0)) ^ N)⁻¹ := by
  classical
  have hp : (z (p (σ 0)) ^ N)⁻¹ = Complex.exp (-(I * (N : ℂ) * (p (σ 0) : ℂ))) := by
    rw [z, ← Complex.exp_nat_mul, ← Complex.exp_neg]
    congr 1
    ring
  have h : ∀ k, Complex.exp (I * (p (σ k) : ℂ) * (cyclicPredecessorPositions N x k : ℂ)) =
      Complex.exp (I * (p (σ k) : ℂ) * (x ((finRotate (n + 1)).symm k) : ℂ)) *
        (if k = 0 then (z (p (σ 0)) ^ N)⁻¹ else 1) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp only [cyclicPredecessorPositions, ↓reduceIte, hp]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp only [cyclicPredecessorPositions, hk, ↓reduceIte, sub_zero, mul_one]
  rw [planeWave, planeWave_rotate]
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', mem_univ, ↓reduceIte]
  rfl

/-- The amplitude and plane-wave boundary phases cancel exactly. -/
theorem amplitude_planeWave_rotate {N n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N Δ p)
    (σ : Equiv.Perm (Fin (n + 1))) (x : Fin (n + 1) → ℤ) :
    amplitude Δ p (σ * finRotate (n + 1)) * planeWave p (σ * finRotate (n + 1)) x =
      amplitude Δ p σ * planeWave p σ (cyclicPredecessorPositions N x) := by
  rw [amplitude_rotate hΔ p hBE σ, planeWave_cyclicPredecessorPositions]
  ring

/-- Proposition `prop:changeOfVariables`, with the complex codomain used in Lemma T₀. -/
theorem toroidal_change_of_variables {N n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N Δ p)
    (x : Fin (n + 1) → ℤ) (f : Equiv.Perm (Fin (n + 1)) → ℂ) :
    (∑ σ, amplitude Δ p σ * f σ * planeWave p σ x) =
      ∑ σ, amplitude Δ p σ * f (σ * finRotate (n + 1)) *
        planeWave p σ (cyclicPredecessorPositions N x) := by
  calc
    _ = ∑ σ, amplitude Δ p (σ * finRotate (n + 1)) * f (σ * finRotate (n + 1)) *
        planeWave p (σ * finRotate (n + 1)) x :=
      (Equiv.sum_comp (Equiv.mulRight (finRotate (n + 1))) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      have h := amplitude_planeWave_rotate hΔ p hBE σ x
      calc
        _ = f (σ * finRotate (n + 1)) *
            (amplitude Δ p (σ * finRotate (n + 1)) * planeWave p (σ * finRotate (n + 1)) x) := by ring
        _ = f (σ * finRotate (n + 1)) *
            (amplitude Δ p σ * planeWave p σ (cyclicPredecessorPositions N x)) := by rw [h]
        _ = _ := by ring

end PottsDiscontinuity.BetheAnsatz
