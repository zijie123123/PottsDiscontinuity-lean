module

public import PottsDiscontinuity.TorusRC.LiftedPaths

/-! # Reflection of the actual lifted lattice and its indexed torus edges -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- Integer reflection in the horizontal line of height t/2. -/
def liftedHorizontalReflect (t : ℤ) (ht : Even t) (z : RotatedVertex) : RotatedVertex :=
  ⟨(z.val.1, t - z.val.2), by
    obtain ⟨k,hk⟩ := z.property
    obtain ⟨l,hl⟩ := ht
    exact ⟨k + l - z.val.2, by omega⟩⟩

/-- Reflection on a periodic coordinate, without choosing an integer lift. -/
def periodicReflect (hp : 0 < N) (t : ℤ) : Fin N ≃ Fin N where
  toFun j := periodicCoordinate hp (t - j.val)
  invFun j := periodicCoordinate hp (t - j.val)
  left_inv j := by
    apply Fin.ext
    apply Int.ofNat.inj
    change ((periodicCoordinate hp (t - (periodicCoordinate hp (t - j.val)).val)).val : ℤ) =
      (j.val : ℤ)
    rw [periodicCoordinate_val, periodicCoordinate_val]
    have heq := ((Int.mod_modEq (t - (j.val : ℤ)) (N : ℤ)).sub_left t).eq
    simp only [sub_sub_cancel] at heq
    rw [heq, Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)]
  right_inv j := by
    apply Fin.ext
    apply Int.ofNat.inj
    change ((periodicCoordinate hp (t - (periodicCoordinate hp (t - j.val)).val)).val : ℤ) =
      (j.val : ℤ)
    rw [periodicCoordinate_val, periodicCoordinate_val]
    have heq := ((Int.mod_modEq (t - (j.val : ℤ)) (N : ℤ)).sub_left t).eq
    simp only [sub_sub_cancel] at heq
    rw [heq, Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)]

theorem periodicReflect_periodicCoordinate (hp : 0 < N) (t z : ℤ) :
    periodicReflect hp t (periodicCoordinate hp z) = periodicCoordinate hp (t - z) := by
  apply Fin.ext
  apply Int.ofNat.inj
  change ((periodicCoordinate hp (t - (periodicCoordinate hp z).val)).val : ℤ) =
    ((periodicCoordinate hp (t - z)).val : ℤ)
  rw [periodicCoordinate_val, periodicCoordinate_val, periodicCoordinate_val]
  exact ((Int.mod_modEq z (N : ℤ)).sub_left t).eq

theorem liftedHorizontalReflect_adj (t : ℤ) (ht : Even t) {u v : RotatedVertex}
    (huv : rotatedLattice.Adj u v) :
    rotatedLattice.Adj (liftedHorizontalReflect t ht u) (liftedHorizontalReflect t ht v) := by
  refine ⟨huv.1, ?_⟩
  change |(t - u.val.2) - (t - v.val.2)| = 1
  have heq : (t - u.val.2) - (t - v.val.2) = -(u.val.2 - v.val.2) := by ring
  rw [heq, abs_neg]
  exact huv.2

theorem liftedHorizontalReflect_index (hNp : 0 < N) (hMp : 0 < M)
    (t : ℤ) (ht : Even t) {u v : RotatedVertex} (huv : rotatedLattice.Adj u v) :
    liftedEdgeIndex hNp hMp (liftedHorizontalReflect t ht u) (liftedHorizontalReflect t ht v) =
      ((liftedEdgeIndex hNp hMp u v).1,
        periodicReflect hMp (t + 1) (liftedEdgeIndex hNp hMp u v).2) := by
  have hdist := huv.2
  have hsum : max (t - u.val.2) (t - v.val.2) = t + 1 - max u.val.2 v.val.2 := by
    have hle := abs_le.mp (le_of_eq hdist)
    have hne : u.val.2 ≠ v.val.2 := by
      intro heq
      simp [heq] at hdist
    omega
  apply Prod.ext
  · rfl
  · change periodicCoordinate hMp (max (t - u.val.2) (t - v.val.2)) =
      periodicReflect hMp (t + 1) (periodicCoordinate hMp (max u.val.2 v.val.2))
    rw [hsum, periodicReflect_periodicCoordinate]

end PottsDiscontinuity.TorusRC
