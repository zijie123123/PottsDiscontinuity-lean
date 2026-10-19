module

public import PottsDiscontinuity.Torus.DiamondFullFlows
public import PottsDiscontinuity.Torus.RibbonIntersectionAlternating

/-!
# Intersection coordinates are lifted displacement

With the endpoint-false to endpoint-true orientation, every primal edge has vertical
increment minus one; its horizontal increment is minus one at a black midpoint and
plus one at a white midpoint. The explicit full-torus flows recover these coordinates
through the cellular intersection pairing.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Horizontal displacement of an indexed primal chain in the integer-lattice lift. -/
def diamondHorizontalDisplacement (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ) : ℚ :=
  ∑ e, (if checker e.val then -1 else 1) * f e

/-- Vertical displacement of an indexed primal chain in the integer-lattice lift. -/
def diamondVerticalDisplacement (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ) : ℚ :=
  -(∑ e, f e)

theorem verticalDiamondCycle_primitive (hN : Even N) (hM : Even M)
    (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive hN hM (openRCConfig N M) (verticalDiamondCycle hN hM) d =
      cornerPrimitiveValue verticalCornerFlow d.val.2 := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  rw [ribbonCornerPrimitive_corner]
  change cornerPrimitiveValue (fun q => ribbonHalfFlow hN hM (openRCConfig N M)
    (verticalDiamondFlow N M) (ribbonCornerEquiv hN hM (v, q))) p =
      cornerPrimitiveValue verticalCornerFlow (faceCorner v.val p).2
  simp_rw [verticalDiamondFlow_corner]
  cases p <;> rfl

theorem horizontalDiamondCycle_primitive (hN : Even N) (hM : Even M)
    (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive hN hM (openRCConfig N M) (horizontalDiamondCycle hN hM) d =
      cornerPrimitiveValue horizontalCornerFlow d.val.2 := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  rw [ribbonCornerPrimitive_corner]
  change cornerPrimitiveValue (fun q => ribbonHalfFlow hN hM (openRCConfig N M)
    (horizontalDiamondFlow N M) (ribbonCornerEquiv hN hM (v, q))) p =
      cornerPrimitiveValue horizontalCornerFlow (faceCorner v.val p).2
  simp_rw [horizontalDiamondFlow_corner]
  cases p <;> rfl

theorem ribbonIntersectionCoefficient_vertical (hN : Even N) (hM : Even M)
    (e : OpenDiamondEdge (openRCConfig N M)) :
    ribbonIntersectionCoefficient hN hM (openRCConfig N M) (verticalDiamondCycle hN hM) e =
      if checker e.val then -1 else 1 := by
  unfold ribbonIntersectionCoefficient
  rw [verticalDiamondCycle_primitive, verticalDiamondCycle_primitive]
  simp only [ribbonEndEquiv_val, verticalDiamondCycle, verticalDiamondFlow]
  cases hc : checker e.val <;> simp only [ribbonEnd, hc, Bool.false_eq_true,
    ite_false, ite_true, cornerPrimitiveValue, verticalCornerFlow] <;> norm_num

theorem ribbonIntersectionCoefficient_horizontal (hN : Even N) (hM : Even M)
    (e : OpenDiamondEdge (openRCConfig N M)) :
    ribbonIntersectionCoefficient hN hM (openRCConfig N M) (horizontalDiamondCycle hN hM) e = 1 := by
  unfold ribbonIntersectionCoefficient
  rw [horizontalDiamondCycle_primitive, horizontalDiamondCycle_primitive]
  simp only [ribbonEndEquiv_val, horizontalDiamondCycle, horizontalDiamondFlow]
  cases hc : checker e.val <;> simp only [ribbonEnd, hc, Bool.false_eq_true,
    ite_false, ite_true, cornerPrimitiveValue, horizontalCornerFlow] <;> norm_num

theorem ribbonIntersection_vertical_eq_displacement (hN : Even N) (hM : Even M)
    (f : diamondCycleSpace hN hM (openRCConfig N M)) :
    ribbonIntersection hN hM (openRCConfig N M) (verticalDiamondCycle hN hM) f =
      diamondHorizontalDisplacement (openRCConfig N M) f.val := by
  simp only [ribbonIntersection, ribbonIntersectionCoefficient_vertical, diamondHorizontalDisplacement]

theorem ribbonIntersection_horizontal_eq_displacement (hN : Even N) (hM : Even M)
    (f : diamondCycleSpace hN hM (openRCConfig N M)) :
    ribbonIntersection hN hM (openRCConfig N M) (horizontalDiamondCycle hN hM) f =
      -diamondVerticalDisplacement (openRCConfig N M) f.val := by
  simp only [ribbonIntersection, ribbonIntersectionCoefficient_horizontal, one_mul,
    diamondVerticalDisplacement, neg_neg]

theorem verticalDiamondCycle_displacement_x (hN : Even N) (hM : Even M) :
    diamondHorizontalDisplacement (openRCConfig N M) (verticalDiamondCycle hN hM).val = 0 := by
  rw [← ribbonIntersection_vertical_eq_displacement, ribbonIntersection_self]

theorem verticalDiamondCycle_displacement_y (hN : Even N) (hM : Even M) :
    diamondVerticalDisplacement (openRCConfig N M) (verticalDiamondCycle hN hM).val = -(N * M : ℚ) := by
  simp only [diamondVerticalDisplacement, verticalDiamondCycle, verticalDiamondFlow,
    Finset.sum_const, Finset.card_univ, card_openDiamondEdge, openCount_open,
    nsmul_eq_mul, mul_one, Nat.cast_mul]

theorem horizontalDiamondCycle_displacement_x (hN : Even N) (hM : Even M) :
    diamondHorizontalDisplacement (openRCConfig N M) (horizontalDiamondCycle hN hM).val = -(N * M : ℚ) := by
  rw [← ribbonIntersection_vertical_eq_displacement, ribbonIntersection_antisymm,
    ribbonIntersection_horizontal_eq_displacement, neg_neg, verticalDiamondCycle_displacement_y]

theorem horizontalDiamondCycle_displacement_y (hN : Even N) (hM : Even M) :
    diamondVerticalDisplacement (openRCConfig N M) (horizontalDiamondCycle hN hM).val = 0 := by
  have he := ribbonIntersection_self hN hM (openRCConfig N M) (horizontalDiamondCycle hN hM)
  rw [ribbonIntersection_horizontal_eq_displacement] at he
  exact neg_eq_zero.mp he

end PottsDiscontinuity.Torus
