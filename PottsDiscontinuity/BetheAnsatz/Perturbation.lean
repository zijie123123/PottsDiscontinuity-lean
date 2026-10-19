module

public import PottsDiscontinuity.BetheAnsatz.GapGeometry

/-!
# Continuity of the finite gap sum under a fixed-amplitude perturbation

The amplitudes are held at the original Bethe momenta. Only the plane-wave
variables in the finite gap sum are perturbed; this is the continuity used in T₀/T₁.
-/

@[expose] public section

open Finset Complex Filter Topology

namespace PottsDiscontinuity.BetheAnsatz

/-- Replace one momentum while retaining the original parameter tuple elsewhere. -/
noncomputable def perturbedMomenta {n : ℕ} (p : Fin (n + 1) → ℝ)
    (l : Fin (n + 1)) (t : ℝ) : Fin (n + 1) → ℝ := Function.update p l (p l + t)

@[simp] theorem perturbedMomenta_at {n : ℕ} (p : Fin (n + 1) → ℝ)
    (l : Fin (n + 1)) (t : ℝ) : perturbedMomenta p l t l = p l + t := by
  simp [perturbedMomenta]

theorem perturbedMomenta_of_ne {n : ℕ} (p : Fin (n + 1) → ℝ)
    (l k : Fin (n + 1)) (t : ℝ) (hkl : k ≠ l) :
    perturbedMomenta p l t k = p k := by
  simp [perturbedMomenta, hkl]

/-- One perturbed cyclic gap sum is continuous in the moved momentum. -/
theorem continuous_cyclicGapSum_perturbed {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    Continuous (fun t : ℝ => cyclicGapSum c N x (perturbedMomenta p l t) σ) := by
  unfold cyclicGapSum distinctGapTuples gapTuples gapWeight planeWave perturbedMomenta
  fun_prop

/-- The finite amplitude-weighted sum is continuous with Aσ fixed at the original p. -/
theorem tendsto_fixedAmplitude_gapSum {N n : ℕ} (c Δ : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    Tendsto (fun t : ℝ =>
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        amplitude Δ p σ * cyclicGapSum c N x (perturbedMomenta p l t) σ)
      (𝓝 0) (𝓝 (∑ σ, amplitude Δ p σ * cyclicGapSum c N x p σ)) := by
  have hcont : Continuous (fun t : ℝ =>
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        amplitude Δ p σ * cyclicGapSum c N x (perturbedMomenta p l t) σ) := by
    apply continuous_finsetSum
    intro σ _
    exact continuous_const.mul (continuous_cyclicGapSum_perturbed c x p l σ)
  have hzero : perturbedMomenta p l 0 = p := by
    funext k
    by_cases hk : k = l
    · subst k
      simp [perturbedMomenta]
    · simp [perturbedMomenta, hk]
  convert hcont.continuousAt.tendsto using 1
  rw [hzero]

end PottsDiscontinuity.BetheAnsatz
