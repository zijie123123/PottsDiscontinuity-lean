module

public import PottsDiscontinuity.Torus.DiamondDualTranslation
public import PottsDiscontinuity.Torus.PermutationCycleTransport
public import PottsDiscontinuity.Torus.RibbonEdges

/-!
# The actual primal/dual loop correspondence

Reverse a medial dart and translate it horizontally. This preserves the canonical
directed carrier and intertwines primal boundary traversal with inverse translated
dual traversal. It identifies the individual boundary loops, not just their count.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Horizontal translation of medial incident-edge slots. -/
def shiftDart (d : Dart N M) : Dart N M := ((nxt d.1.1, d.1.2), d.2)

def unshiftDart (d : Dart N M) : Dart N M := ((prv d.1.1, d.1.2), d.2)

def dartShiftPerm (N M : ℕ) : Equiv.Perm (Dart N M) where
  toFun := shiftDart
  invFun := unshiftDart
  left_inv d := by rcases d with ⟨⟨i, j⟩, p⟩; simp only [shiftDart, unshiftDart, nxt, prv, Equiv.symm_apply_apply]
  right_inv d := by rcases d with ⟨⟨i, j⟩, p⟩; simp only [shiftDart, unshiftDart, nxt, prv, Equiv.apply_symm_apply]

theorem shiftDart_edgeReverse (d : Dart N M) :
    shiftDart (edgeReverse d) = edgeReverse (shiftDart d) := by
  rcases d with ⟨⟨i, j⟩, p⟩
  cases p <;> simp only [shiftDart, edgeReverse, nxt, prv, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply]

theorem dartOut_shiftDart (hN : Even N) (hM : Even M) (d : Dart N M) :
    dartOut (checkerArrows N M) (shiftDart d) = !dartOut (checkerArrows N M) d := by
  rcases d with ⟨⟨i, j⟩, p⟩
  change dartOut (checkerArrows N M) ((nxt i, j), p) =
    !dartOut (checkerArrows N M) ((i, j), p)
  cases p <;> simp only [dartOut_checker_at hN hM, checker_nxt_x hN, Bool.not_not]

theorem rcSmoothing_translatedDual_shift (hN : Even N) (A : RCConfig N M) (v : Fin N × Fin M) :
    rcSmoothing (translatedDualConfig A) (nxt v.1, v.2) = rcSmoothing A v := by
  unfold rcSmoothing translatedDualConfig
  rw [checker_nxt_x hN, shiftRCConfig_nxt]
  change Bool.xor (!checker v) (!A v) = Bool.xor (checker v) (A v)
  cases checker v <;> cases A v <;> rfl

theorem shiftDart_strandReverse_dual (hN : Even N) (A : RCConfig N M) (d : Dart N M) :
    shiftDart (strandReverse (rcSmoothing A) d) =
      strandReverse (rcSmoothing (translatedDualConfig A)) (shiftDart d) := by
  rcases d with ⟨v, p⟩
  change ((nxt v.1, v.2), pairedPort (rcSmoothing A v) p) =
    ((nxt v.1, v.2), pairedPort (rcSmoothing (translatedDualConfig A) (nxt v.1, v.2)) p)
  rw [rcSmoothing_translatedDual_shift hN]

/-- Reversal followed by horizontal translation of all medial darts. -/
def dualDartTransport (N M : ℕ) : Equiv.Perm (Dart N M) :=
  (edgePerm N M).trans (dartShiftPerm N M)

theorem dartOut_dualDartTransport (hN : Even N) (hM : Even M) (d : Dart N M) :
    dartOut (checkerArrows N M) (dualDartTransport N M d) = dartOut (checkerArrows N M) d := by
  change dartOut (checkerArrows N M) (shiftDart (edgeReverse d)) = _
  rw [dartOut_shiftDart hN hM, dartOut_edgeReverse, Bool.not_not]

/-- The primal/dual dart correspondence on the actual canonical outgoing edges. -/
def dualDirectedEquiv (hN : Even N) (hM : Even M) :
    Equiv.Perm (DirectedDart (checkerArrows N M)) :=
  (dualDartTransport N M).subtypeEquiv (fun d => by rw [dartOut_dualDartTransport hN hM])

@[simp] theorem dualDirectedEquiv_val (hN : Even N) (hM : Even M)
    (d : DirectedDart (checkerArrows N M)) :
    (dualDirectedEquiv hN hM d).val = shiftDart (edgeReverse d.val) := rfl

theorem dualDartTransport_step (hN : Even N) (A : RCConfig N M) (d : Dart N M) :
    dualDartTransport N M (stepPerm (rcSmoothing A) d) =
      (stepPerm (rcSmoothing (translatedDualConfig A))).symm (dualDartTransport N M d) := by
  change shiftDart (edgeReverse (stepPerm (rcSmoothing A) d)) =
    (stepPerm (rcSmoothing (translatedDualConfig A))).symm (shiftDart (edgeReverse d))
  rw [edgeReverse_step, stepPerm_symm_apply, stepPerm_symm_apply,
    shiftDart_edgeReverse, shiftDart_strandReverse_dual hN]

theorem dualDirectedEquiv_boundary (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (d : DirectedDart (checkerArrows N M)) :
    dualDirectedEquiv hN hM (ribbonBoundary hN hM A d) =
      (ribbonBoundary hN hM (translatedDualConfig A)).symm (dualDirectedEquiv hN hM d) := by
  rw [ribbonBoundary_eq_directedStep, ribbonBoundary_eq_directedStep]
  apply Subtype.ext
  exact dualDartTransport_step hN A d.val

/-- Individual primal boundary loops are the reversed translated dual boundary loops. -/
def dualBoundaryLoopEquiv (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    RibbonBoundaryComponent hN hM A ≃ RibbonBoundaryComponent hN hM (translatedDualConfig A) :=
  permutationCycleEquivOfInverseIntertwining _ _ (dualDirectedEquiv hN hM)
    (dualDirectedEquiv_boundary hN hM A)

theorem rcLoopCount_translatedDual (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    rcLoopCount hN hM A = rcLoopCount hN hM (translatedDualConfig A) := by
  calc
    _ = Nat.card (RibbonBoundaryComponent hN hM A) := (card_ribbonBoundaryComponent hN hM A).symm
    _ = Nat.card (RibbonBoundaryComponent hN hM (translatedDualConfig A)) :=
      Nat.card_congr (dualBoundaryLoopEquiv hN hM A)
    _ = _ := card_ribbonBoundaryComponent hN hM _

end PottsDiscontinuity.Torus
