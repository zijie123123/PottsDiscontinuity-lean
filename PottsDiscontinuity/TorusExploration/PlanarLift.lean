module

public import PottsDiscontinuity.CorrLength.RotatedLattice
public import PottsDiscontinuity.Torus.DiamondGraph

/-! Unrolling a horizontally exact cylinder into the rotated square lattice. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus CorrLength
variable {N M : ℕ}

/-- Integer coordinates of the lift associated with an integer seam potential. -/
def potentialLiftCoordinates (F : FaceVertex N M true → ℤ) (v : FaceVertex N M true) : ℤ × ℤ :=
  ((v.val.1.val : ℤ)+(N : ℤ)*F v,v.val.2.val)

lemma potentialLiftCoordinates_even (hN : Even N)
    (F : FaceVertex N M true → ℤ) (v : FaceVertex N M true) :
    Even ((potentialLiftCoordinates F v).1+(potentialLiftCoordinates F v).2) := by
  have hv : Even (v.val.1.val+v.val.2.val) := by
    apply Nat.even_iff.mpr
    simpa only [checker,decide_eq_true_eq] using v.property
  have hv' : Even ((v.val.1.val : ℤ)+(v.val.2.val : ℤ)) := by exact_mod_cast hv
  have hN' : Even (N : ℤ) := by exact_mod_cast hN
  convert hv'.add (hN'.mul_right (F v)) using 1; dsimp [potentialLiftCoordinates]; ring

/-- An actual rotated-lattice vertex, with unchanged cylinder height. -/
def potentialLift (hN : Even N) (F : FaceVertex N M true → ℤ)
    (v : FaceVertex N M true) : RotatedVertex :=
  ⟨potentialLiftCoordinates F v,potentialLiftCoordinates_even hN F v⟩

/-- Distinct cylinder vertices remain distinct after unrolling. -/
theorem potentialLift_injective (hN : Even N) (F : FaceVertex N M true → ℤ) :
    Function.Injective (potentialLift hN F) := by
  intro u v huv
  have hx := congrArg (fun w : RotatedVertex => w.val.1 % (N : ℤ)) huv
  have hy := congrArg (fun w : RotatedVertex => w.val.2) huv
  have hmod (w : FaceVertex N M true) :
      (potentialLift hN F w).val.1 % (N : ℤ) = w.val.1.val := by
    change ((w.val.1.val : ℤ)+(N : ℤ)*F w) % (N : ℤ) = _
    rw [Int.add_emod,Int.mul_emod]
    simp only [Int.emod_self,zero_mul,Int.zero_emod,add_zero,Int.emod_emod]
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast w.val.1.isLt)
  rw [hmod,hmod] at hx
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact_mod_cast hx
  · apply Fin.ext
    change (u.val.2.val : ℤ) = (v.val.2.val : ℤ) at hy
    exact_mod_cast hy

end PottsDiscontinuity.TorusExploration
