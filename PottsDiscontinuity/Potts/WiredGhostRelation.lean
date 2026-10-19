module

public import PottsDiscontinuity.Potts.WiredConnectionEvents

/-! Exact marked-component relation in the conditioned outer ghost representation. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical
noncomputable section

/-- A fixed genuine boundary vertex, also for the singleton box. -/
def boxBoundaryAnchor (n : ℕ) : ↥(box n : Set (ℤ × ℤ)) :=
  ⟨cornerPoint n (true, true), cornerPoint_mem n (true, true)⟩

theorem boxBoundaryAnchor_mem (n : ℕ) : (boxBoundaryAnchor n).val ∈ vertexBoundary (box n) := by
  rw [mem_vertexBoundary_box_iff]
  exact ⟨(boxBoundaryAnchor n).property, Or.inr (Or.inl rfl)⟩

/-- Read the ghost as the fixed wired-boundary representative. -/
def wiredRepresentative (n : ℕ) : Option ↥(box n : Set (ℤ × ℤ)) → ↥(box n : Set (ℤ × ℤ)) :=
  fun a => a.elim (boxBoundaryAnchor n) id

/-- Adjoining a deterministic boundary ghost gives exactly the original wired
component relation, with the ghost represented by any fixed boundary vertex. -/
theorem wiredObservation_reachableSetoid (n : ℕ)
    (C : FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :
    (wiredObservationGraph n C).reachableSetoid =
      (FK.componentSetoid _ (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box n)}) C).comap
        (wiredRepresentative n) := by
  let G := squareLattice.induce (box n : Set (ℤ × ℤ))
  let B : Set ↥(box n : Set (ℤ × ℤ)) := {x | x.val ∈ vertexBoundary (box n)}
  let R := (wiredObservationGraph n C).reachableSetoid
  have hcomp : FK.componentSetoid G (FK.BoundaryCondition.wired B) C ≤ R.comap some := by
    apply FK.componentSetoid_le
    · intro x y hxy
      exact (FK.reachableSetoid_le_of_adj (FK.openGraph G C) (R.comap some)
        (fun hxy => (show (wiredObservationGraph n C).Adj (some _) (some _) from hxy).reachable)) hxy
    · intro x y hxy
      rcases (FK.BoundaryCondition.wired_rel B x y).mp hxy with rfl | ⟨hx, hy⟩
      · exact R.refl (some x)
      · exact (show (wiredObservationGraph n C).Adj (some x) none from hx).reachable.trans
          (show (wiredObservationGraph n C).Adj none (some y) from hy).reachable
  have hbridge (a : Option ↥(box n : Set (ℤ × ℤ))) : R a (some (wiredRepresentative n a)) := by
    cases a with
    | none => exact (show (wiredObservationGraph n C).Adj none (some (boxBoundaryAnchor n)) from
        boxBoundaryAnchor_mem n).reachable
    | some x => exact R.refl (some x)
  apply le_antisymm
  · apply FK.reachableSetoid_le_of_adj
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact hab.elim
      | some y =>
        exact FK.boundary_component G (FK.BoundaryCondition.wired B) C
          (Or.inr ⟨boxBoundaryAnchor_mem n, hab⟩)
    | some x =>
      cases b with
      | none =>
        exact FK.boundary_component G (FK.BoundaryCondition.wired B) C
          (Or.inr ⟨hab, boxBoundaryAnchor_mem n⟩)
      | some y =>
        exact FK.actualConnected_component G (FK.BoundaryCondition.wired B) C
          (show (FK.openGraph G C).Adj x y from hab).reachable
  · intro a b hab
    exact R.trans (hbridge a) (R.trans (hcomp hab) (R.symm (hbridge b)))

/-- Collapse the full outer ghost and the wired shell to the literal inner ghost. -/
def collapseOuterGhost (n : ℕ) : Option ↥(box (n + 1) : Set (ℤ × ℤ)) →
    Option ↥(box n : Set (ℤ × ℤ)) := fun a => a.elim none (collapseOuterBox n)

/-- The finite ghost representation preserves marked connection data, including
connections to the ghost, after the four corner edges are closed. -/
theorem restored_wiredObservation_reachableSetoid (n : ℕ) (hn : 0 < n)
    (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
    (wiredObservationGraph (n + 1)
      (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η))).reachableSetoid =
      (ghostOpenGraph (box n) ω).reachableSetoid.comap (collapseOuterGhost n) := by
  rw [wiredObservation_reachableSetoid]
  change (FK.componentSetoid _ (outerBoxWiring n)
    (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η))).comap (wiredRepresentative (n + 1)) = _
  rw [outer_componentSetoid_eq_ghost_comap]
  have hf : collapseOuterBox n ∘ wiredRepresentative (n + 1) = collapseOuterGhost n := by
    funext a
    cases a with
    | none => exact (collapseOuterBox_eq_none_iff n _).mpr (boxBoundaryAnchor_mem (n + 1))
    | some x => rfl
  change (ghostOpenGraph (box n) ω).reachableSetoid.comap
    (collapseOuterBox n ∘ wiredRepresentative (n + 1)) = _
  rw [hf]

end
end PottsDiscontinuity.Potts
