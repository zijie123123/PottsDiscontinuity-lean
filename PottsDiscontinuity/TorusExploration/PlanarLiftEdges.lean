module

public import PottsDiscontinuity.TorusExploration.HorizontalPotential
public import PottsDiscontinuity.TorusExploration.PlanarLift

/-! Horizontal seam potentials give genuine nearest-neighbour lifts. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus CorrLength
variable {N M : ℕ}

/-- The horizontal lifted increment is the original diagonal unit step. -/
theorem potentialLift_edge_x (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (F : FaceVertex N M true → ℤ)
    (hF : ∀ e : OpenDiamondEdge A,
      F (faceEndpoint hN hM true e.val true) - F (faceEndpoint hN hM true e.val false) =
        integerSeamCrossX e.val) (e : OpenDiamondEdge A) :
    (potentialLift hN F (faceEndpoint hN hM true e.val true)).val.1 -
      (potentialLift hN F (faceEndpoint hN hM true e.val false)).val.1 =
        if checker e.val then -1 else 1 := by
  have hf : (F (faceEndpoint hN hM true e.val true) : ℚ) -
      (F (faceEndpoint hN hM true e.val false) : ℚ) = diamondSeamCrossX e.val := by
    rw [← integerSeamCrossX_cast]
    exact_mod_cast hF e
  have hx := diamondCoordinateX_coboundary hN hM A e
  rw [diamondCoboundary_apply] at hx
  apply (Int.cast_injective (α := ℚ))
  simp only [potentialLift,potentialLiftCoordinates,Int.cast_sub,Int.cast_add,
    Int.cast_natCast,Int.cast_mul]
  cases hc : checker e.val <;> simp only [hc,Bool.false_eq_true,ite_true,ite_false,Int.cast_neg,Int.cast_one] at * <;>
    linear_combination hx + (N : ℚ)*hf

/-- Away from the seam, the lifted height decreases by exactly one. -/
theorem potentialLift_edge_y (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (F : FaceVertex N M true → ℤ) (e : OpenDiamondEdge A) (he : e.val.2.val ≠ 0) :
    (potentialLift hN F (faceEndpoint hN hM true e.val true)).val.2 -
      (potentialLift hN F (faceEndpoint hN hM true e.val false)).val.2 = -1 := by
  have hy := diamondCoordinateY_coboundary hN hM A e
  simp only [diamondSeamCrossY,he,ite_false,mul_zero,sub_zero,diamondCoboundary_apply] at hy
  change ((faceEndpoint hN hM true e.val true).val.2.val : ℤ) -
    ((faceEndpoint hN hM true e.val false).val.2.val : ℤ) = (-1 : ℤ)
  exact_mod_cast hy

/-- Every retained cylinder edge maps to a rotated-lattice edge. -/
theorem potentialLift_edge_adj (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (F : FaceVertex N M true → ℤ)
    (hF : ∀ e : OpenDiamondEdge A,
      F (faceEndpoint hN hM true e.val true) - F (faceEndpoint hN hM true e.val false) =
        integerSeamCrossX e.val) (e : OpenDiamondEdge A) (he : e.val.2.val ≠ 0) :
    rotatedLattice.Adj (potentialLift hN F (faceEndpoint hN hM true e.val false))
      (potentialLift hN F (faceEndpoint hN hM true e.val true)) := by
  suffices h : rotatedLattice.Adj
      (potentialLift hN F (faceEndpoint hN hM true e.val true))
      (potentialLift hN F (faceEndpoint hN hM true e.val false)) from h.symm
  change |_ - _|=1 ∧ |_ - _|=1
  rw [potentialLift_edge_x hN hM A F hF e,potentialLift_edge_y hN hM A F e he]
  cases hc : checker e.val <;> norm_num [hc]

end PottsDiscontinuity.TorusExploration
