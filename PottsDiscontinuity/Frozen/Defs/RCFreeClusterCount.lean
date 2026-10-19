module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.RCOpenGraph

/-!
# Definition `rcFreeClusterCount` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- `k₀(ω)`: the number of clusters (connected components, isolated vertices included). -/
noncomputable def rcFreeClusterCount (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℕ :=
  Nat.card (rcOpenGraph V ω).ConnectedComponent

end PottsDiscontinuity
