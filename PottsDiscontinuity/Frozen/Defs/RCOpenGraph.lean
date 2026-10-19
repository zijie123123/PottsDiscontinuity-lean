module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.SquareLattice

/-!
# Definition `rcOpenGraph` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- The open subgraph of a percolation configuration `ω ∈ {0,1}^E` on the finite subgraph
`G = (V, E)` of `ℤ²` induced by `V` (vertex set `V`, open edges `{e ∈ E : ω(e) = 1}`). -/
def rcOpenGraph (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    SimpleGraph (V : Set (ℤ × ℤ)) :=
  SimpleGraph.fromEdgeSet
    {e | ∃ h : e ∈ (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet, ω ⟨e, h⟩ = true}

end PottsDiscontinuity
