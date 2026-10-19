module

public import PottsDiscontinuity.Torus.DiamondGraph
public import PottsDiscontinuity.Torus.LoopOrientation

/-!
# Corners of the primal ribbon vertices

The canonically directed medial edges are exactly the four boundary corners of every
black face. With all primal edges closed, their boundary permutation rotates these
four corners counterclockwise. This identifies the ribbon vertices without assuming
an Euler formula or a classification of embedded curves.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The face to the left of a directed medial edge slot. -/
def leftFace : Dart N M → Fin N × Fin M
  | ((i, j), .east) => (i, j)
  | ((i, j), .north) => (prv i, j)
  | ((i, j), .west) => (prv i, prv j)
  | ((i, j), .south) => (i, prv j)

/-- The counterclockwise boundary dart of a face with the specified direction. -/
def faceCorner (v : Fin N × Fin M) : Port → Dart N M
  | .east => (v, .east)
  | .north => ((nxt v.1, v.2), .north)
  | .west => ((nxt v.1, nxt v.2), .west)
  | .south => ((v.1, nxt v.2), .south)

@[simp] theorem leftFace_faceCorner (v : Fin N × Fin M) (p : Port) :
    leftFace (faceCorner v p) = v := by
  rcases v with ⟨i, j⟩
  cases p <;> simp only [faceCorner, leftFace, nxt, prv, Equiv.symm_apply_apply]

@[simp] theorem faceCorner_leftFace (d : Dart N M) :
    faceCorner (leftFace d) d.2 = d := by
  rcases d with ⟨⟨i, j⟩, p⟩
  cases p <;> simp only [faceCorner, leftFace, nxt, prv, Equiv.apply_symm_apply]

/-- The reference arrows are precisely those with a black face on the left. -/
theorem dartOut_checker_eq_leftFace (hN : Even N) (hM : Even M) (d : Dart N M) :
    dartOut (checkerArrows N M) d = checker (leftFace d) := by
  rcases d with ⟨⟨i, j⟩, p⟩
  cases p <;> simp only [dartOut, localOut, checkerArrows, ArrowConfig.left,
    ArrowConfig.right, ArrowConfig.below, ArrowConfig.above, leftFace,
    checker_prv_x hN, checker_prv_y hM, Bool.not_not]

/-- The actual ribbon-corner parametrization of canonical directed medial edges. -/
def ribbonCornerEquiv (hN : Even N) (hM : Even M) :
    FaceVertex N M true × Port ≃ DirectedDart (checkerArrows N M) where
  toFun x := ⟨faceCorner x.1.val x.2, by
    rw [dartOut_checker_eq_leftFace hN hM, leftFace_faceCorner, x.1.property]⟩
  invFun d := (⟨leftFace d.val, by
    rw [← dartOut_checker_eq_leftFace hN hM]
    exact d.property⟩, d.val.2)
  left_inv x := by
    rcases x with ⟨v, p⟩
    apply Prod.ext
    · exact Subtype.ext (leftFace_faceCorner v.val p)
    · cases p <;> rfl
  right_inv d := Subtype.ext (faceCorner_leftFace d.val)

@[simp] theorem ribbonCornerEquiv_val (hN : Even N) (hM : Even M)
    (v : FaceVertex N M true) (p : Port) :
    (ribbonCornerEquiv hN hM (v, p)).val = faceCorner v.val p := rfl

/-- Counterclockwise rotation of boundary directions around a black face. -/
def ccwPort : Port → Port
  | .east => .north
  | .north => .west
  | .west => .south
  | .south => .east

/-- Clockwise rotation, the inverse direction. -/
def cwPort : Port → Port
  | .east => .south
  | .south => .west
  | .west => .north
  | .north => .east

def ccwPortPerm : Equiv.Perm Port :=
  ⟨ccwPort, cwPort, by intro p; cases p <;> rfl, by intro p; cases p <;> rfl⟩

/-- The boundary of the disjoint primal vertex discs, before any open ribbon is attached. -/
def faceRotation (hN : Even N) (hM : Even M) :
    Equiv.Perm (DirectedDart (checkerArrows N M)) :=
  directedStep (checkerArrows N M) (fun v => checker v)
    (checkerArrows_compatible hN hM _)

theorem faceRotation_corner (hN : Even N) (hM : Even M)
    (v : FaceVertex N M true) (p : Port) :
    faceRotation hN hM (ribbonCornerEquiv hN hM (v, p)) =
      ribbonCornerEquiv hN hM (v, ccwPort p) := by
  apply Subtype.ext
  change stepPerm (fun v : Fin N × Fin M => checker v) (faceCorner v.val p) =
    faceCorner v.val (ccwPort p)
  rcases v with ⟨⟨i, j⟩, hv⟩
  cases p <;> simp only [faceCorner, stepPerm_apply, strandReverse, edgeReverse,
    nxt, prv, Equiv.symm_apply_apply, checker_nxt_x hN, checker_nxt_y hM,
    hv, Bool.not_true, Bool.not_false, ccwPort, pairedPort]

theorem faceRotation_pow_corner (hN : Even N) (hM : Even M)
    (v : FaceVertex N M true) (p : Port) (n : ℕ) :
    (faceRotation hN hM ^ n) (ribbonCornerEquiv hN hM (v, p)) =
      ribbonCornerEquiv hN hM (v, (ccwPortPerm ^ n) p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, faceRotation_corner]
    rw [pow_succ', Equiv.Perm.mul_apply]
    rfl

/-- The vertex cycles of the ribbon rotation are exactly the primal face vertices. -/
theorem sameCycle_faceRotation (hN : Even N) (hM : Even M)
    (d e : DirectedDart (checkerArrows N M)) :
    (faceRotation hN hM).SameCycle d e ↔ leftFace d.val = leftFace e.val := by
  constructor
  · apply sameCycle_invariant (faceRotation hN hM) (fun d => leftFace d.val)
    intro x
    obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective x
    rw [faceRotation_corner]
    simp only [ribbonCornerEquiv_val, leftFace_faceCorner]
  · intro hde
    obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
    obtain ⟨⟨w, q⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective e
    have hvw : v = w := Subtype.ext (by
      simpa only [ribbonCornerEquiv_val, leftFace_faceCorner] using hde)
    subst w
    have hc : ∀ p q : Port, ∃ n : Fin 4, (ccwPortPerm ^ n.val) p = q := by decide
    obtain ⟨n, hn⟩ := hc p q
    refine ⟨(n.val : ℤ), ?_⟩
    rw [zpow_natCast, faceRotation_pow_corner, hn]

end PottsDiscontinuity.Torus
