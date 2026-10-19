module

public import PottsDiscontinuity.Torus.DiamondDisplacement

/-!
# Extending subgraph cycles to the full torus

The inclusion extends indexed chains by zero on closed edges. It preserves vertex
conservation, the normalized corner primitives, the cyclic-order intersection form,
and both lifted displacement coordinates.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The fully open edge subtype is explicitly the full indexed edge carrier. -/
def fullDiamondEdgeEquiv (N M : ℕ) : OpenDiamondEdge (openRCConfig N M) ≃ Fin N × Fin M where
  toFun e := e.val
  invFun v := ⟨v, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Extend a chain to all primal edges, with coefficient zero on absent edges. -/
def fullDiamondChainExtension (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ) :
    OpenDiamondEdge (openRCConfig N M) → ℚ := fun e => extendDiamondChain A f e.val

@[simp] theorem extendDiamondChain_fullExtension (A : RCConfig N M)
    (f : OpenDiamondEdge A → ℚ) (v : Fin N × Fin M) :
    extendDiamondChain (openRCConfig N M) (fullDiamondChainExtension A f) v =
      extendDiamondChain A f v := by
  rw [extendDiamondChain_open _ _ v rfl]
  rfl

theorem ribbonHalfFlow_fullExtension (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : OpenDiamondEdge A → ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM (openRCConfig N M) (fullDiamondChainExtension A f) d =
      ribbonHalfFlow hN hM A f d := by
  rw [ribbonHalfFlow_raw, ribbonHalfFlow_raw, extendDiamondChain_fullExtension]

theorem fullDiamondChainExtension_mem (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) :
    fullDiamondChainExtension A f.val ∈ diamondCycleSpace hN hM (openRCConfig N M) := by
  rw [diamondCycleSpace_mem_iff_corners]
  intro v
  simp_rw [ribbonHalfFlow_fullExtension]
  exact sum_ribbonHalfFlow_corners hN hM A f v

/-- The actual inclusion of conserved indexed flows into the full torus cycle space. -/
def fullDiamondCycleExtension (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) : diamondCycleSpace hN hM (openRCConfig N M) :=
  ⟨fullDiamondChainExtension A f.val, fullDiamondChainExtension_mem hN hM A f⟩

theorem ribbonCornerPrimitive_fullExtension (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive hN hM (openRCConfig N M) (fullDiamondCycleExtension hN hM A f) d =
      ribbonCornerPrimitive hN hM A f d := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  rw [ribbonCornerPrimitive_corner, ribbonCornerPrimitive_corner]
  change cornerPrimitiveValue (fun q => ribbonHalfFlow hN hM (openRCConfig N M)
    (fullDiamondChainExtension A f.val) (ribbonCornerEquiv hN hM (v, q))) p = _
  simp_rw [ribbonHalfFlow_fullExtension]

theorem ribbonIntersectionCoefficient_fullExtension (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) (e : OpenDiamondEdge A) :
    ribbonIntersectionCoefficient hN hM (openRCConfig N M)
      (fullDiamondCycleExtension hN hM A f) ⟨e.val, rfl⟩ =
        ribbonIntersectionCoefficient hN hM A f e := by
  unfold ribbonIntersectionCoefficient
  rw [ribbonCornerPrimitive_fullExtension, ribbonCornerPrimitive_fullExtension]
  change _ - _ - extendDiamondChain A f.val e.val = _
  rw [extendDiamondChain_open A f.val e.val e.property]

theorem sum_fullDiamondChainExtension (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)
    (c : Fin N × Fin M → ℚ) :
    (∑ e : OpenDiamondEdge (openRCConfig N M), c e.val * fullDiamondChainExtension A f e) =
      ∑ e : OpenDiamondEdge A, c e.val * f e := by
  classical
  rw [← (fullDiamondEdgeEquiv N M).symm.sum_comp]
  change (∑ v : Fin N × Fin M, c v * extendDiamondChain A f v) = _
  have he : (∑ e : OpenDiamondEdge A, c e.val * f e) =
      ∑ e : OpenDiamondEdge A, c e.val * extendDiamondChain A f e.val :=
    Finset.sum_congr rfl (fun e _ => by rw [extendDiamondChain_open A f e.val e.property])
  rw [he, ← Finset.sum_subtype (univ.filter fun v => A v = true)
    (by intro v; simp) (fun v => c v * extendDiamondChain A f v), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  cases ha : A v
  · simp only [extendDiamondChain_closed A f v ha, mul_zero, Bool.false_eq_true, ite_false]
  · simp only [ite_true]

/-- Cellular intersection is preserved by the actual subgraph inclusion. -/
theorem ribbonIntersection_fullExtension (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f g : diamondCycleSpace hN hM A) :
    ribbonIntersection hN hM (openRCConfig N M)
      (fullDiamondCycleExtension hN hM A f) (fullDiamondCycleExtension hN hM A g) =
        ribbonIntersection hN hM A f g := by
  unfold ribbonIntersection
  change (∑ e : OpenDiamondEdge (openRCConfig N M),
    ribbonIntersectionCoefficient hN hM (openRCConfig N M) (fullDiamondCycleExtension hN hM A f) e *
      fullDiamondChainExtension A g.val e) = _
  have he := sum_fullDiamondChainExtension A g.val
    (fun v => ribbonIntersectionCoefficient hN hM (openRCConfig N M)
      (fullDiamondCycleExtension hN hM A f) ⟨v, rfl⟩)
  change (∑ e : OpenDiamondEdge (openRCConfig N M),
    ribbonIntersectionCoefficient hN hM (openRCConfig N M) (fullDiamondCycleExtension hN hM A f) e *
      fullDiamondChainExtension A g.val e) = _ at he
  rw [he]
  exact Finset.sum_congr rfl (fun e _ => by rw [ribbonIntersectionCoefficient_fullExtension])

theorem diamondHorizontalDisplacement_fullExtension (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (f : diamondCycleSpace hN hM A) :
    diamondHorizontalDisplacement (openRCConfig N M) (fullDiamondCycleExtension hN hM A f).val =
      diamondHorizontalDisplacement A f.val :=
  sum_fullDiamondChainExtension A f.val (fun v => if checker v then -1 else 1)

theorem diamondVerticalDisplacement_fullExtension (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (f : diamondCycleSpace hN hM A) :
    diamondVerticalDisplacement (openRCConfig N M) (fullDiamondCycleExtension hN hM A f).val =
      diamondVerticalDisplacement A f.val := by
  have he := sum_fullDiamondChainExtension A f.val (fun _ => 1)
  simp only [one_mul] at he
  exact congrArg Neg.neg he

end PottsDiscontinuity.Torus
