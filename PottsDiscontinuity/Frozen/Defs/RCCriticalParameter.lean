module

public import Mathlib

/-!
# Definition `rcCriticalParameter` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- `p_c(q) = √q / (1 + √q)` for `q ≥ 1`, as an element of `[0, 1]`: the value of the critical
parameter stated on p. 4 (identified in [3]); criticality itself is not asserted here. -/
noncomputable def rcCriticalParameter (q : Set.Ici (1 : ℝ)) : Set.Icc (0 : ℝ) 1 :=
  ⟨Real.sqrt q / (1 + Real.sqrt q),
    div_nonneg (Real.sqrt_nonneg _) (by positivity),
    (div_le_one (by positivity)).2 (by linarith)⟩

end PottsDiscontinuity
