module

public import PottsDiscontinuity.SixVertex.RowTransfer

/-!
# Splitting the transfer action into the two interlacing orientations

Companion paper, equation `eq:V_on_phi`. The diagonal is counted once in each orientation.
This finite identity precedes the cyclic gap reindexing and uses the actual entries of (1.5).
-/

@[expose] public section

open Finset Complex Matrix Classical

namespace PottsDiscontinuity.BetheAnsatz

open SixVertex

/-- The two weak interlacing orientations coincide only on the diagonal. -/
theorem interlacedLE_antisymm {N : ℕ} {x y : Finset (Fin N)}
    (hxy : InterlacedLE x y) (hyx : InterlacedLE y x) : x = y := by
  cases N with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    apply (eq_iff_Dd_zero x y).mpr
    intro i
    have h1 := ((interlacedLE_iff x y).mp hxy).2 i
    have h2 := ((interlacedLE_iff y x).mp hyx).2 i
    unfold Dd
    omega

/-- The entry (1.5) is the sum of its two oriented interlacing contributions. -/
theorem transferMatrix_eq_two_orientations {N : ℕ} (c : ℝ) (x y : Finset (Fin N)) :
    transferMatrix N c x y =
      (if InterlacedLE y x then c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card else 0) +
      (if InterlacedLE x y then c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card else 0) := by
  classical
  by_cases he : x = y
  · subst y
    have hi : InterlacedLE x x := (interlacedLE_iff x x).mpr
      ⟨rfl, fun _ => ⟨le_rfl, Nat.le_succ _⟩⟩
    norm_num [transferMatrix_apply_self, hi]
  · have hn : ¬ (InterlacedLE x y ∧ InterlacedLE y x) :=
      fun h => he (interlacedLE_antisymm h.1 h.2)
    rw [transferMatrix_apply]
    by_cases hxy : InterlacedLE x y <;> by_cases hyx : InterlacedLE y x
    · exact (hn ⟨hxy, hyx⟩).elim
    · simp [he, Interlaced, hxy, hyx]
    · simp [he, Interlaced, hxy, hyx]
    · simp [he, Interlaced, hxy, hyx]

end PottsDiscontinuity.BetheAnsatz
