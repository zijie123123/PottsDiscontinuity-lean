module

public import PottsDiscontinuity.BetheAnsatz.GapGeometric
public import PottsDiscontinuity.BetheAnsatz.Perturbation

/-!
# Phase factors in the zero-root perturbation

Changing one zero momentum to t multiplies a plane wave by the phase at the
coordinate occupied by that root. This records the root's position explicitly.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Perturbing a zero momentum contributes one coordinate phase to the plane wave. -/
theorem planeWave_perturbed_zero {n : ℕ} (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (hpl : p l = 0) (t : ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1) → ℤ) :
    planeWave (perturbedMomenta p l t) σ x =
      positionPhase t (x (σ.symm l)) * planeWave p σ x := by
  let k := σ.symm l
  let f : Fin (n + 1) → ℂ := fun j => Complex.exp (I * (p (σ j) : ℂ) * (x j : ℂ))
  let g : Fin (n + 1) → ℂ := fun j =>
    Complex.exp (I * (perturbedMomenta p l t (σ j) : ℂ) * (x j : ℂ))
  have hgk : g k = positionPhase t (x k) := by
    dsimp [g, k]
    rw [Equiv.apply_symm_apply, perturbedMomenta_at, hpl]
    simp only [positionPhase, zero_add]
  have hfk : f k = 1 := by
    dsimp [f, k]
    rw [Equiv.apply_symm_apply, hpl]
    simp
  have hrest : ∏ j ∈ univ.erase k, g j = ∏ j ∈ univ.erase k, f j := by
    apply Finset.prod_congr rfl
    intro j hj
    have hjk : j ≠ k := (mem_erase.mp hj).1
    have hσ : σ j ≠ l := by
      intro h
      apply hjk
      apply σ.injective
      simpa [k] using h
    have hq := perturbedMomenta_of_ne p l (σ j) t hσ
    dsimp [g, f]
    rw [hq]
  unfold planeWave
  change ∏ j, g j = positionPhase t (x k) * ∏ j, f j
  rw [← Finset.mul_prod_erase univ g (mem_univ k),
    ← Finset.mul_prod_erase univ f (mem_univ k), hgk, hfk, hrest]
  simp

end PottsDiscontinuity.BetheAnsatz
