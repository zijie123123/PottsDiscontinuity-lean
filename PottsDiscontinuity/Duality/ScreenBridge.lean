module

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.BondStates
public import PottsDiscontinuity.Frozen.Defs.RCInfiniteOpenGraph

/-! The copied whole-plane geometry uses the exact frozen open graph. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK FK.Medial

/-- Equality of the literal edge-state graph and the frozen open graph. -/
theorem wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph (ω : LatticeConfiguration) :
    wholePlaneOpenPrimalGraph ω = rcInfiniteOpenGraph ω := by
  ext u v
  rw [rcInfiniteOpenGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    exact ⟨⟨squareLattice.mem_edgeSet.mpr hadj, hopen⟩, hadj.ne⟩
  · rintro ⟨⟨he, hopen⟩, _⟩
    exact ⟨squareLattice.mem_edgeSet.mp he, hopen⟩

end PottsDiscontinuity.Duality
