module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.RCOpenGraph
public import PottsDiscontinuity.Frozen.Defs.VertexBoundary

/-!
# Definition `rcWiredClusterCount` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

open Classical in
/-- `k₁(ω)`: the number of clusters when all clusters intersecting `∂V` count as one. -/
noncomputable def rcWiredClusterCount (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℕ :=
  Nat.card {c : (rcOpenGraph V ω).ConnectedComponent //
      ∀ x : (V : Set (ℤ × ℤ)), (rcOpenGraph V ω).connectedComponentMk x = c →
        x.1 ∉ vertexBoundary V} +
    if ∃ c : (rcOpenGraph V ω).ConnectedComponent,
        ∃ x : (V : Set (ℤ × ℤ)), (rcOpenGraph V ω).connectedComponentMk x = c ∧
          x.1 ∈ vertexBoundary V then 1 else 0

end PottsDiscontinuity
