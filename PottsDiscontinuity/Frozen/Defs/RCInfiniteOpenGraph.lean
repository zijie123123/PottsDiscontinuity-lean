module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.SquareLattice

/-!
# Definition `rcInfiniteOpenGraph` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- The open subgraph of `ℤ²` of an infinite-volume configuration `ω ∈ {0,1}^{E(ℤ²)}`. -/
def rcInfiniteOpenGraph (ω : squareLattice.edgeSet → Bool) : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ squareLattice.edgeSet, ω ⟨e, h⟩ = true}

end PottsDiscontinuity
