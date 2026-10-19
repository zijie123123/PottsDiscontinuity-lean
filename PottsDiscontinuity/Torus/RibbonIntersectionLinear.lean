module

public import PottsDiscontinuity.Torus.RibbonIntersection

/-!
# Bilinearity of the cyclic-order intersection pairing

The normalized primitive is given by explicit linear combinations of corner flows.
Consequently the induced edge coefficient and the intersection pairing are linear.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem extendDiamondChain_add (A : RCConfig N M) (f g : OpenDiamondEdge A → ℚ)
    (v : Fin N × Fin M) :
    extendDiamondChain A (f + g) v = extendDiamondChain A f v + extendDiamondChain A g v := by
  by_cases hv : A v = true
  · simp only [extendDiamondChain, hv, dite_true, Pi.add_apply]
  · simp only [extendDiamondChain, hv, Bool.false_eq_true, dite_false, add_zero]

theorem extendDiamondChain_smul (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)
    (c : ℚ) (v : Fin N × Fin M) :
    extendDiamondChain A (c • f) v = c * extendDiamondChain A f v := by
  by_cases hv : A v = true
  · simp only [extendDiamondChain, hv, dite_true, Pi.smul_apply, smul_eq_mul]
  · simp only [extendDiamondChain, hv, Bool.false_eq_true, dite_false, mul_zero]

theorem ribbonHalfFlow_add (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g : OpenDiamondEdge A → ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM A (f + g) d =
      ribbonHalfFlow hN hM A f d + ribbonHalfFlow hN hM A g d := by
  simp only [ribbonHalfFlow, extendDiamondChain_add]
  split <;> ring

theorem ribbonHalfFlow_smul (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : OpenDiamondEdge A → ℚ) (c : ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM A (c • f) d = c * ribbonHalfFlow hN hM A f d := by
  simp only [ribbonHalfFlow, extendDiamondChain_smul]
  split <;> ring

theorem ribbonCornerPrimitive_add (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g : diamondCycleSpace hN hM A) (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive hN hM A (f + g) d =
      ribbonCornerPrimitive hN hM A f d + ribbonCornerPrimitive hN hM A g d := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  simp only [ribbonCornerPrimitive_corner, Submodule.coe_add, ribbonHalfFlow_add]
  cases p <;> simp only [cornerPrimitiveValue] <;> ring

theorem ribbonCornerPrimitive_smul (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) (c : ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive hN hM A (c • f) d = c * ribbonCornerPrimitive hN hM A f d := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  simp only [ribbonCornerPrimitive_corner, Submodule.coe_smul, ribbonHalfFlow_smul]
  cases p <;> simp only [cornerPrimitiveValue] <;> ring

theorem ribbonIntersectionCoefficient_add (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g : diamondCycleSpace hN hM A) (e : OpenDiamondEdge A) :
    ribbonIntersectionCoefficient hN hM A (f + g) e =
      ribbonIntersectionCoefficient hN hM A f e + ribbonIntersectionCoefficient hN hM A g e := by
  simp only [ribbonIntersectionCoefficient, ribbonCornerPrimitive_add, Submodule.coe_add, Pi.add_apply]
  ring

theorem ribbonIntersectionCoefficient_smul (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) (c : ℚ) (e : OpenDiamondEdge A) :
    ribbonIntersectionCoefficient hN hM A (c • f) e =
      c * ribbonIntersectionCoefficient hN hM A f e := by
  simp only [ribbonIntersectionCoefficient, ribbonCornerPrimitive_smul,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem ribbonIntersection_add_left (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g h : diamondCycleSpace hN hM A) :
    ribbonIntersection hN hM A (f + g) h =
      ribbonIntersection hN hM A f h + ribbonIntersection hN hM A g h := by
  simp only [ribbonIntersection, ribbonIntersectionCoefficient_add, add_mul, Finset.sum_add_distrib]

theorem ribbonIntersection_add_right (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g h : diamondCycleSpace hN hM A) :
    ribbonIntersection hN hM A f (g + h) =
      ribbonIntersection hN hM A f g + ribbonIntersection hN hM A f h := by
  simp only [ribbonIntersection, Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ribbonIntersection_smul_left (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g : diamondCycleSpace hN hM A) (c : ℚ) :
    ribbonIntersection hN hM A (c • f) g = c * ribbonIntersection hN hM A f g := by
  simp only [ribbonIntersection, ribbonIntersectionCoefficient_smul, mul_assoc, Finset.mul_sum]

theorem ribbonIntersection_smul_right (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g : diamondCycleSpace hN hM A) (c : ℚ) :
    ribbonIntersection hN hM A f (c • g) = c * ribbonIntersection hN hM A f g := by
  simp only [ribbonIntersection, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end PottsDiscontinuity.Torus
