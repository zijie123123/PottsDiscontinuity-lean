module

public import PottsDiscontinuity.BetheAnsatz.Defs
public import PottsDiscontinuity.SixVertex.TransferMatrix

/-!
# Coordinates, nonzero amplitudes, and the full-matrix/block bridge

The paper's positions `1,...,N` are our increasing `Fin N` positions plus one.
The resulting uniform phase is exactly `exp(i ∑j p_j)`, independently of the state.
The block-extension identity below is linear algebra for arbitrary vectors; it does not
assert the Bethe Ansatz for an unproved particle sector.
-/

@[expose] public section

open Finset Complex Matrix

namespace PottsDiscontinuity.BetheAnsatz

open SixVertex

theorem planeWave_add_one {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℤ) :
    planeWave p σ (fun k => x k + 1) = (∏ j, z (p j)) * planeWave p σ x := by
  have h : ∀ k, Complex.exp (I * (p (σ k) : ℂ) * ((x k + 1 : ℤ) : ℂ)) =
      z (p (σ k)) * Complex.exp (I * (p (σ k) : ℂ) * (x k : ℂ)) := by
    intro k
    rw [z, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold planeWave
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun j => z (p j))]

theorem prod_z_eq_exp_sum {n : ℕ} (p : Fin n → ℝ) :
    (∏ j, z (p j)) = Complex.exp (I * ((∑ j, p j : ℝ) : ℂ)) := by
  simp only [z]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- Adding one to every coordinate multiplies the wave by `exp(i ∑j p_j)`.
This is the exact normalization relating zero-based and one-based positions. -/
theorem coordinateWave_add_one {n : ℕ} (Δ : ℝ) (p : Fin n → ℝ)
    (x : Fin n → ℤ) :
    coordinateWave Δ p (fun k => x k + 1) =
      Complex.exp (I * ((∑ j, p j : ℝ) : ℂ)) * coordinateWave Δ p x := by
  unfold coordinateWave
  simp_rw [planeWave_add_one]
  rw [← prod_z_eq_exp_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- The change in position convention is multiplication by a nonzero scalar. -/
theorem coordinate_shift_phase_ne_zero {n : ℕ} (p : Fin n → ℝ) :
    Complex.exp (I * ((∑ j, p j : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _

/-- Evaluation of the full matrix on a zero-extended vector agrees with the block action. -/
theorem mulVec_extendByZero_apply {N n : ℕ} (c : ℝ) (v : State N n → ℂ)
    (x : State N n) :
    ((transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ extendByZero v) x.1 =
      ((transferBlock N c n).map (algebraMap ℝ ℂ) *ᵥ v) x := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr_set {y : Finset (Fin N) | y.card = n}
  · intro y hy
    change y.card = n at hy
    simp only [Matrix.map_apply, transferBlock_apply, extendByZero, hy, ↓reduceDIte]
  · intro y hy
    change y.card ≠ n at hy
    simp only [extendByZero_eq_zero v hy, mul_zero]

end PottsDiscontinuity.BetheAnsatz
