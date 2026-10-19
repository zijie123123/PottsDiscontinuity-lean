module

public import PottsDiscontinuity.Torus.RibbonEdges

/-!
# Attaching one indexed ribbon

Changing one primal edge composes the boundary permutation with the transposition
of its two ends. This is the combinatorial cut-and-join operation needed to count
boundary components under ribbon attachment.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Toggle one indexed primal edge. -/
def toggleEdge (A : RCConfig N M) (v : Fin N × Fin M) : RCConfig N M :=
  Function.update A v (!A v)

@[simp] theorem toggleEdge_at (A : RCConfig N M) (v : Fin N × Fin M) :
    toggleEdge A v v = !A v := by simp only [toggleEdge, Function.update_self]

theorem toggleEdge_away (A : RCConfig N M) {v w : Fin N × Fin M} (h : w ≠ v) :
    toggleEdge A v w = A w := Function.update_of_ne h _ _

@[simp] theorem toggleEdge_toggleEdge (A : RCConfig N M) (v : Fin N × Fin M) :
    toggleEdge (toggleEdge A v) v = A := by
  funext w
  by_cases hw : w = v
  · subst w
    simp only [toggleEdge_at, Bool.not_not]
  · rw [toggleEdge_away _ hw, toggleEdge_away _ hw]

/-- The transposition of the two distinct slots of one indexed ribbon. -/
def ribbonEndSwap (hN : Even N) (hM : Even M) (v : Fin N × Fin M) :
    Equiv.Perm (DirectedDart (checkerArrows N M)) :=
  Equiv.swap (ribbonEndEquiv hN hM (v, false)) (ribbonEndEquiv hN hM (v, true))

theorem ribbonEndSwap_end (hN : Even N) (hM : Even M)
    (v w : Fin N × Fin M) (b : Bool) :
    ribbonEndSwap hN hM v (ribbonEndEquiv hN hM (w, b)) =
      ribbonEndEquiv hN hM (w, if w = v then !b else b) := by
  by_cases hw : w = v
  · subst w
    cases b <;> simp only [ribbonEndSwap, Equiv.swap_apply_left,
      Equiv.swap_apply_right, ite_true, Bool.not_false, Bool.not_true]
  · have h₀ : ribbonEndEquiv hN hM (w, b) ≠ ribbonEndEquiv hN hM (v, false) := by
      intro he
      exact hw (congrArg Prod.fst ((ribbonEndEquiv hN hM).injective he))
    have h₁ : ribbonEndEquiv hN hM (w, b) ≠ ribbonEndEquiv hN hM (v, true) := by
      intro he
      exact hw (congrArg Prod.fst ((ribbonEndEquiv hN hM).injective he))
    simp only [ribbonEndSwap, Equiv.swap_apply_of_ne_of_ne h₀ h₁, hw, ite_false]

theorem ribbonEdgePairing_toggle (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M) :
    ribbonEdgePairing hN hM (toggleEdge A v) =
      ribbonEndSwap hN hM v * ribbonEdgePairing hN hM A := by
  apply Equiv.ext
  intro d
  obtain ⟨⟨w, b⟩, rfl⟩ := (ribbonEndEquiv hN hM).surjective d
  rw [Equiv.Perm.mul_apply, ribbonEdgePairing_end, ribbonEdgePairing_end,
    ribbonEndSwap_end]
  by_cases hw : w = v
  · subst w
    simp only [toggleEdge_at, ite_true]
    have ht : ∀ a b : Bool, Bool.xor (!a) b = !(Bool.xor a b) := by decide
    rw [ht]
  · rw [toggleEdge_away _ hw]
    simp only [hw, ite_false]

/-- Toggling an indexed primal edge cuts or joins its two boundary strands. -/
theorem ribbonBoundary_toggle (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M) :
    ribbonBoundary hN hM (toggleEdge A v) =
      ribbonEndSwap hN hM v * ribbonBoundary hN hM A := by
  apply Equiv.ext
  intro d
  change ribbonEdgePairing hN hM (toggleEdge A v) (faceRotation hN hM d) = _
  rw [ribbonEdgePairing_toggle]
  rfl

end PottsDiscontinuity.Torus
