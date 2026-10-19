module

public import PottsDiscontinuity.Torus.RibbonHalfFlow

/-!
# Cyclic-order primitives of conserved half-edge flows

On each primal vertex disc the four outward flows sum to zero. Integrating around
its ordered corners therefore gives a primitive, normalized to zero at the east
corner. This normalization is explicit and uses no selected existence witness.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem sum_port (t : Port → ℚ) :
    ∑ p : Port, t p = t .west + t .east + t .south + t .north := by
  have hu : (univ : Finset Port) = {.west, .east, .south, .north} := by decide
  rw [hu]
  simp [add_assoc]

/-- The zero-east-corner primitive of a four-component zero-sum flow. -/
def cornerPrimitiveValue (t : Port → ℚ) : Port → ℚ
  | .east => 0
  | .north => -t .north
  | .west => -t .north - t .west
  | .south => t .east

theorem cornerPrimitiveValue_cw_sub (t : Port → ℚ) (ht : ∑ p : Port, t p = 0) (p : Port) :
    cornerPrimitiveValue t (cwPort p) - cornerPrimitiveValue t p = t p := by
  rw [sum_port] at ht
  cases p <;> simp only [cwPort, cornerPrimitiveValue] <;> linarith

theorem faceRotation_symm_corner (hN : Even N) (hM : Even M)
    (v : FaceVertex N M true) (p : Port) :
    (faceRotation hN hM).symm (ribbonCornerEquiv hN hM (v, p)) =
      ribbonCornerEquiv hN hM (v, cwPort p) := by
  apply (faceRotation hN hM).injective
  rw [Equiv.apply_symm_apply, faceRotation_corner]
  cases p <;> rfl

/-- The normalized primitive on every actual primal ribbon vertex. -/
def ribbonCornerPrimitive (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) (d : DirectedDart (checkerArrows N M)) : ℚ :=
  let x := (ribbonCornerEquiv hN hM).symm d
  cornerPrimitiveValue
    (fun p => ribbonHalfFlow hN hM A f.val (ribbonCornerEquiv hN hM (x.1, p))) x.2

@[simp] theorem ribbonCornerPrimitive_corner (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) (v : FaceVertex N M true) (p : Port) :
    ribbonCornerPrimitive hN hM A f (ribbonCornerEquiv hN hM (v, p)) =
      cornerPrimitiveValue
        (fun q => ribbonHalfFlow hN hM A f.val (ribbonCornerEquiv hN hM (v, q))) p := by
  simp only [ribbonCornerPrimitive, Equiv.symm_apply_apply]

/-- Differentiation around the cyclic vertex order recovers the actual half-edge flow. -/
theorem ribbonCornerPrimitive_rotation_sub (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive hN hM A f ((faceRotation hN hM).symm d) -
      ribbonCornerPrimitive hN hM A f d = ribbonHalfFlow hN hM A f.val d := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  rw [faceRotation_symm_corner, ribbonCornerPrimitive_corner, ribbonCornerPrimitive_corner]
  exact cornerPrimitiveValue_cw_sub _ (sum_ribbonHalfFlow_corners hN hM A f v) p

end PottsDiscontinuity.Torus
