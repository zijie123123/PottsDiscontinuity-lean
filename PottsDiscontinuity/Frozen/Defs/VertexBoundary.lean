module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.SquareLattice

/-!
# Definition `vertexBoundary` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- `∂V`: the vertices of `V` having at least one neighbour in `ℤ²` outside of `V`. -/
def vertexBoundary (V : Finset (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {x | x ∈ V ∧ ∃ y, squareLattice.Adj x y ∧ y ∉ V}

end PottsDiscontinuity
