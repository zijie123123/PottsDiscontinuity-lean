module

public import Mathlib

/-!
# Definition `squareLattice` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- The square lattice `ℤ²`: vertices `x = (x₁, x₂)`, edges between nearest neighbours. -/
def squareLattice : SimpleGraph (ℤ × ℤ) where
  Adj x y := |x.1 - y.1| + |x.2 - y.2| = 1
  symm := ⟨fun x y h => by rwa [abs_sub_comm y.1, abs_sub_comm y.2]⟩
  loopless := ⟨fun x h => by simp at h⟩

end PottsDiscontinuity
