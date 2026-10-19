module

public import PottsDiscontinuity.Torus.RibbonCorners
public import PottsDiscontinuity.Torus.LoopStatistics

/-!
# The cellular boundary permutation

Open primal ribbons interchange the two corner slots at their medial midpoint.
Composing this edge pairing with the vertex rotation gives exactly the smoothing
permutation, including small periods and parallel indexed edges.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Switching from closed to open ribbons at their indexed medial midpoints. -/
def ribbonSwitch (A : RCConfig N M) (d : Dart N M) : Dart N M :=
  strandReverse (rcSmoothing A) (strandReverse (fun v => checker v) d)

theorem ribbonSwitch_involutive (A : RCConfig N M) :
    Function.Involutive (ribbonSwitch A) := by
  have ht : ∀ (c a : Bool) (p : Port),
      pairedPort (Bool.xor c a) (pairedPort c
        (pairedPort (Bool.xor c a) (pairedPort c p))) = p := by decide
  rintro ⟨v, p⟩
  exact Prod.ext rfl (ht (checker v) (A v) p)

theorem ribbonSwitch_eq_self_iff (A : RCConfig N M) (d : Dart N M) :
    ribbonSwitch A d = d ↔ A d.1 = false := by
  have ht : ∀ (c a : Bool) (p : Port),
      pairedPort (Bool.xor c a) (pairedPort c p) = p ↔ a = false := by decide
  rcases d with ⟨v, p⟩
  simpa only [ribbonSwitch, strandReverse, rcSmoothing, Prod.mk.injEq,
    true_and] using ht (checker v) (A v) p

theorem dartOut_ribbonSwitch (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (d : Dart N M) :
    dartOut (checkerArrows N M) (ribbonSwitch A d) =
      dartOut (checkerArrows N M) d := by
  unfold ribbonSwitch
  rw [dartOut_strandReverse (checkerArrows_compatible hN hM _),
    dartOut_strandReverse (checkerArrows_compatible hN hM _), Bool.not_not]

/-- The edge pairing fixes closed slots and interchanges the two sides of each open ribbon. -/
def ribbonEdgePairing (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Equiv.Perm (DirectedDart (checkerArrows N M)) :=
  let e : Equiv.Perm (Dart N M) :=
    ⟨ribbonSwitch A, ribbonSwitch A,
      ribbonSwitch_involutive A, ribbonSwitch_involutive A⟩
  e.subtypeEquiv (fun d => by
    change dartOut (checkerArrows N M) d = true ↔
      dartOut (checkerArrows N M) (ribbonSwitch A d) = true
    rw [dartOut_ribbonSwitch hN hM])

@[simp] theorem ribbonEdgePairing_val (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (d : DirectedDart (checkerArrows N M)) :
    (ribbonEdgePairing hN hM A d).val = ribbonSwitch A d.val := rfl

theorem ribbonEdgePairing_involutive (hN : Even N) (hM : Even M)
    (A : RCConfig N M) : Function.Involutive (ribbonEdgePairing hN hM A) := by
  intro d
  exact Subtype.ext (ribbonSwitch_involutive A d.val)

theorem ribbonEdgePairing_eq_self_iff (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (d : DirectedDart (checkerArrows N M)) :
    ribbonEdgePairing hN hM A d = d ↔ A d.val.1 = false := by
  rw [Subtype.ext_iff, ribbonEdgePairing_val, ribbonSwitch_eq_self_iff]

/-- Boundary traversal of the primal vertex discs with their open ribbons attached. -/
def ribbonBoundary (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Equiv.Perm (DirectedDart (checkerArrows N M)) :=
  (faceRotation hN hM).trans (ribbonEdgePairing hN hM A)

/-- The ribbon boundary and the medial smoothing agree as permutations, not merely in count. -/
theorem ribbonBoundary_eq_directedStep (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    ribbonBoundary hN hM A = directedStep (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM _) := by
  apply Equiv.ext
  intro d
  apply Subtype.ext
  change strandReverse (rcSmoothing A)
      (strandReverse (fun v => checker v)
        (strandReverse (fun v => checker v) (edgeReverse d.val))) =
    strandReverse (rcSmoothing A) (edgeReverse d.val)
  rw [strandReverse_involutive]

/-- Boundary components of the actual open ribbon subgraph. -/
abbrev RibbonBoundaryComponent (hN : Even N) (hM : Even M) (A : RCConfig N M) :=
  Quotient (Equiv.Perm.SameCycle.setoid (ribbonBoundary hN hM A))

/-- Identification of every boundary component with its RC loop. -/
def ribbonBoundaryLoopEquiv (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    RibbonBoundaryComponent hN hM A ≃ Loop hN hM (rcSmoothing A) := by
  unfold RibbonBoundaryComponent Loop DirectedLoop
  rw [ribbonBoundary_eq_directedStep]

theorem card_ribbonBoundaryComponent (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    Nat.card (RibbonBoundaryComponent hN hM A) = rcLoopCount hN hM A := by
  rw [Nat.card_congr (ribbonBoundaryLoopEquiv hN hM A), Nat.card_eq_fintype_card]
  rfl

end PottsDiscontinuity.Torus
