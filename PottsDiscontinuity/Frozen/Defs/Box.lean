module

public import Mathlib

/-!
# Definition `box` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- The box `Λₙ = [-n, n]² ∩ ℤ²`. -/
def box (n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n

end PottsDiscontinuity
