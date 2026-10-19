/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.Model

/-!
# Finite FK events and actual open connectivity

Every configuration has positive mass. Consequently a finite event has zero
probability exactly when it is empty. Connectivity here always uses actual open
graph edges, even if the boundary partition wires the endpoints together.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance eventEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet

attribute [local instance] configurationMeasurableSpace

theorem law_support (q : Parameters) (ξ : BoundaryCondition V) :
    (law G q ξ).support = Set.univ := by
  ext A
  simp only [PMF.mem_support_iff, Set.mem_univ, iff_true]
  exact (law_pos G q ξ A).ne'

theorem measure_eq_zero_iff (q : Parameters) (ξ : BoundaryCondition V)
    (s : Set (Configuration G)) : measure G q ξ s = 0 ↔ s = ∅ := by
  rw [measure, PMF.toMeasure_apply_eq_zero_iff _ MeasurableSpace.measurableSet_top,
    law_support]
  simp

theorem measure_pos_iff (q : Parameters) (ξ : BoundaryCondition V)
    (s : Set (Configuration G)) : 0 < measure G q ξ s ↔ s.Nonempty := by
  rw [pos_iff_ne_zero, ne_eq, measure_eq_zero_iff, Set.nonempty_iff_ne_empty]

/-- The actual open path event between two original vertices. -/
def connectivityEvent (u v : V) : Set (Configuration G) :=
  {A | ActualConnected G A u v}

end

end PottsDiscontinuity.FK
