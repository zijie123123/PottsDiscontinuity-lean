module

public import PottsDiscontinuity.Torus.PermutationSurgery
public import PottsDiscontinuity.Torus.RibbonAttachment
public import PottsDiscontinuity.Torus.RibbonConnectivity

/-!
# Boundary counts under ribbon surgery

The general permutation cut-and-join theorem applies to the actual RC loops.
Every boundary lies within a single ribbon component, so joining two components
necessarily joins two distinct boundary cycles.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem ribbonEnds_ne (hN : Even N) (hM : Even M) (v : Fin N × Fin M) :
    ribbonEndEquiv hN hM (v, false) ≠ ribbonEndEquiv hN hM (v, true) := by
  intro he
  have hb := congrArg Prod.snd ((ribbonEndEquiv hN hM).injective he)
  exact Bool.false_ne_true hb

theorem permutationCycleCount_ribbonBoundary (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    permutationCycleCount (ribbonBoundary hN hM A) = rcLoopCount hN hM A :=
  card_ribbonBoundaryComponent hN hM A

theorem ribbonConnected_boundary_step (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (d : DirectedDart (checkerArrows N M)) :
    RibbonConnected hN hM A d (ribbonBoundary hN hM A d) := by
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.rel _ _ (Or.inl (Equiv.Perm.SameCycle.rfl.apply_right)))
    (Relation.EqvGen.rel _ _ (Or.inr rfl))

/-- Each boundary cycle is contained in a connected component of the open ribbon subgraph. -/
theorem ribbonConnected_of_boundary_sameCycle (hN : Even N) (hM : Even M)
    (A : RCConfig N M) {d e : DirectedDart (checkerArrows N M)}
    (h : (ribbonBoundary hN hM A).SameCycle d e) : RibbonConnected hN hM A d e := by
  have he : (Quotient.mk _ d : RibbonComponent hN hM A) = Quotient.mk _ e :=
    sameCycle_invariant (ribbonBoundary hN hM A) (fun x => Quotient.mk _ x)
      (fun x => Quotient.sound
        (Relation.EqvGen.symm _ _ (ribbonConnected_boundary_step hN hM A x))) h
  exact Quotient.exact he

theorem rcLoopCount_toggle_split (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M)
    (h : (ribbonBoundary hN hM A).SameCycle
      (ribbonEndEquiv hN hM (v, false)) (ribbonEndEquiv hN hM (v, true))) :
    rcLoopCount hN hM (toggleEdge A v) = rcLoopCount hN hM A + 1 := by
  rw [← permutationCycleCount_ribbonBoundary, ribbonBoundary_toggle]
  exact (permutationCycleCount_swap_split _ (ribbonEnds_ne hN hM v) h).trans
    (congrArg (· + 1) (permutationCycleCount_ribbonBoundary hN hM A))

theorem rcLoopCount_toggle_join (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M)
    (h : ¬(ribbonBoundary hN hM A).SameCycle
      (ribbonEndEquiv hN hM (v, false)) (ribbonEndEquiv hN hM (v, true))) :
    rcLoopCount hN hM (toggleEdge A v) + 1 = rcLoopCount hN hM A := by
  rw [← permutationCycleCount_ribbonBoundary, ribbonBoundary_toggle]
  exact (permutationCycleCount_swap_join _ h).trans
    (permutationCycleCount_ribbonBoundary hN hM A)

end PottsDiscontinuity.Torus
