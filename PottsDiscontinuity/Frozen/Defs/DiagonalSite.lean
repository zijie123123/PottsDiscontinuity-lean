module

public import Mathlib

/-!
# Definition `diagonalSite` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- `xₙ`: the site of `ℤ²` with both coordinates equal to `⌊n/2⌋`. -/
def diagonalSite (n : ℕ) : ℤ × ℤ :=
  (((n / 2 : ℕ) : ℤ), ((n / 2 : ℕ) : ℤ))

end PottsDiscontinuity
