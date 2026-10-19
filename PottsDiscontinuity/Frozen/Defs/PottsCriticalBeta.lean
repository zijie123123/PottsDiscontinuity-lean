module

public import Mathlib

/-!
# Definition `pottsCriticalBeta` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- `β_c(q) = log(1 + √q)`: the value of the critical inverse temperature stated on p. 2
(identified in [3]); criticality itself is not asserted here. -/
noncomputable def pottsCriticalBeta (q : ℕ) : ℝ :=
  Real.log (1 + Real.sqrt q)

end PottsDiscontinuity
