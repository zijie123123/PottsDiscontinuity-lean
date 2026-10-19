module

public import Mathlib

/-!
# The local free-fermion identity

Slater determinants diagonalize simultaneous independent left/right moves on
integer lifts. These are identities on the full lifted carrier. Turning them into
an eigenvector on the cyclic defect states also requires the seam/twist and
positivity arguments; no such finite-state conclusion is assumed here.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

/-- The plane-wave matrix, with positions indexing rows and momenta indexing columns. -/
noncomputable def planeWaveMatrix {k : ℕ} (z : Fin k → ℂ) (x : Fin k → ℤ) : Matrix (Fin k) (Fin k) ℂ :=
  fun b a => z a ^ x b

/-- A Slater determinant evaluated on integer lifts. -/
noncomputable def slater {k : ℕ} (z : Fin k → ℂ) (x : Fin k → ℤ) : ℂ := (planeWaveMatrix z x).det

/-- One simultaneous choice of a left or right unit step for every labelled particle. -/
def stepLift {k : ℕ} (x : Fin k → ℤ) (d : Fin k → Bool) : Fin k → ℤ :=
  fun b => x b + if d b then 1 else -1

/-- Summing all `2^k` lifted moves multiplies a Slater determinant by the product of
one-particle eigenvalues. This identity includes collision terms, which vanish. -/
theorem sum_slater_stepLift {k : ℕ} (z : Fin k → ℂ) (hz : ∀ a, z a ≠ 0)
    (x : Fin k → ℤ) :
    (∑ d : Fin k → Bool, slater z (stepLift x d)) =
      (∏ a, (z a + (z a)⁻¹)) * slater z x := by
  let g : Fin k → Bool → (Fin k → ℂ) :=
    fun b d a => z a ^ (x b + if d then 1 else -1)
  have hm := (Matrix.detRowAlternating (R := ℂ) (n := Fin k)).toMultilinearMap.map_sum g
  have he : (fun b => ∑ d : Bool, g b d) =
      (fun b a => (z a + (z a)⁻¹) * planeWaveMatrix z x b a) := by
    funext b a
    simp only [Finset.sum_apply, Fintype.sum_bool, g, Bool.false_eq_true, ↓reduceIte,
      zpow_add₀ (hz a), zpow_one, _root_.zpow_neg_one]
    unfold planeWaveMatrix
    ring
  change (Matrix.det (fun b => ∑ d : Bool, g b d)) =
    ∑ d : Fin k → Bool, slater z (stepLift x d) at hm
  rw [← hm, he]
  exact Matrix.det_mul_row (fun a => z a + (z a)⁻¹) (planeWaveMatrix z x)

/-- Consecutive, centered momenta. For `q = exp(iπ/L)` these are the momenta
`π(2a+1-k)/L`, with the antiperiodic twist when `k` is even. -/
noncomputable def centeredMomenta (k : ℕ) (q : ℂ) : Fin k → ℂ :=
  fun a => q ^ (2 * (a.val : ℤ) + 1 - (k : ℤ))

end PottsDiscontinuity.SixVertex
