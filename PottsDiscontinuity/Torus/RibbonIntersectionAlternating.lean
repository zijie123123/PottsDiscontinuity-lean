module

public import PottsDiscontinuity.Torus.RibbonIntersection

/-!
# Alternation of the cellular intersection pairing

Finite summation by parts around the vertex rotations shows antisymmetry. The
diagonal pairing is therefore zero over the rational coefficient field.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem sum_ribbonHalfFlow_weight (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : OpenDiamondEdge A → ℚ) (H : DirectedDart (checkerArrows N M) → ℚ) :
    (∑ d, H d * ribbonHalfFlow hN hM A f d) =
      ∑ e : OpenDiamondEdge A,
        (H (ribbonEndEquiv hN hM (e.val, false)) -
          H (ribbonEndEquiv hN hM (e.val, true))) * f e := by
  classical
  rw [← (ribbonEndEquiv hN hM).sum_comp]
  conv_lhs => rw [Fintype.sum_prod_type]
  have hc : (∑ e : OpenDiamondEdge A,
      (H (ribbonEndEquiv hN hM (e.val, false)) -
        H (ribbonEndEquiv hN hM (e.val, true))) * f e) =
      ∑ e : OpenDiamondEdge A,
        (H (ribbonEndEquiv hN hM (e.val, false)) -
          H (ribbonEndEquiv hN hM (e.val, true))) * extendDiamondChain A f e.val := by
    exact Finset.sum_congr rfl (fun e _ => by rw [extendDiamondChain_open A f e.val e.property])
  rw [hc, ← Finset.sum_subtype (univ.filter fun v => A v = true)
    (by intro v; simp) (fun v =>
      (H (ribbonEndEquiv hN hM (v, false)) - H (ribbonEndEquiv hN hM (v, true))) *
        extendDiamondChain A f v), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Fintype.sum_bool, ribbonHalfFlow_end, Bool.false_eq_true, ite_false, ite_true]
  cases ha : A v
  · simp only [extendDiamondChain_closed A f v ha, neg_zero, mul_zero,
      add_zero, Bool.false_eq_true, ite_false]
  · simp only [ite_true]
    ring

theorem sum_ribbonHalfFlow_mul (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g : OpenDiamondEdge A → ℚ) :
    (∑ d, ribbonHalfFlow hN hM A f d * ribbonHalfFlow hN hM A g d) =
      2 * ∑ e, f e * g e := by
  rw [sum_ribbonHalfFlow_weight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [ribbonHalfFlow_end, ribbonHalfFlow_end, extendDiamondChain_open A f e.val e.property]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  ring

theorem ribbonIntersection_corner_formula (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g : diamondCycleSpace hN hM A) :
    ribbonIntersection hN hM A f g =
      -(∑ d, ribbonCornerPrimitive hN hM A f d * ribbonHalfFlow hN hM A g.val d) -
        ∑ e, f.val e * g.val e := by
  rw [sum_ribbonHalfFlow_weight, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  unfold ribbonIntersection ribbonIntersectionCoefficient
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem sum_ribbon_primitive_products (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g : diamondCycleSpace hN hM A) :
    (∑ d, ribbonCornerPrimitive hN hM A f d * ribbonHalfFlow hN hM A g.val d) +
      (∑ d, ribbonCornerPrimitive hN hM A g d * ribbonHalfFlow hN hM A f.val d) +
        (∑ d, ribbonHalfFlow hN hM A f.val d * ribbonHalfFlow hN hM A g.val d) = 0 := by
  have hl (d : DirectedDart (checkerArrows N M)) :
      ribbonCornerPrimitive hN hM A f d * ribbonHalfFlow hN hM A g.val d +
        ribbonCornerPrimitive hN hM A g d * ribbonHalfFlow hN hM A f.val d +
          ribbonHalfFlow hN hM A f.val d * ribbonHalfFlow hN hM A g.val d =
      ribbonCornerPrimitive hN hM A f ((faceRotation hN hM).symm d) *
        ribbonCornerPrimitive hN hM A g ((faceRotation hN hM).symm d) -
          ribbonCornerPrimitive hN hM A f d * ribbonCornerPrimitive hN hM A g d := by
    have hf := ribbonCornerPrimitive_rotation_sub hN hM A f d
    have hg := ribbonCornerPrimitive_rotation_sub hN hM A g d
    rw [← hf, ← hg]
    ring
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ d, (ribbonCornerPrimitive hN hM A f ((faceRotation hN hM).symm d) *
        ribbonCornerPrimitive hN hM A g ((faceRotation hN hM).symm d) -
          ribbonCornerPrimitive hN hM A f d * ribbonCornerPrimitive hN hM A g d) :=
      Finset.sum_congr rfl (fun d _ => hl d)
    _ = 0 := by
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr ((faceRotation hN hM).symm.sum_comp
        (fun d => ribbonCornerPrimitive hN hM A f d * ribbonCornerPrimitive hN hM A g d))

/-- The cyclic-order intersection pairing is antisymmetric. -/
theorem ribbonIntersection_antisymm (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g : diamondCycleSpace hN hM A) :
    ribbonIntersection hN hM A f g = -ribbonIntersection hN hM A g f := by
  have hf := ribbonIntersection_corner_formula hN hM A f g
  have hg := ribbonIntersection_corner_formula hN hM A g f
  have hp := sum_ribbon_primitive_products hN hM A f g
  rw [sum_ribbonHalfFlow_mul] at hp
  have hc : (∑ e, g.val e * f.val e) = ∑ e, f.val e * g.val e :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [hc] at hg
  linarith

/-- Every conserved indexed flow has zero intersection with itself. -/
theorem ribbonIntersection_self (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) : ribbonIntersection hN hM A f f = 0 := by
  have he := ribbonIntersection_antisymm hN hM A f f
  linarith

end PottsDiscontinuity.Torus
