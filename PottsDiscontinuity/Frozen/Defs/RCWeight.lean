module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.RCFreeClusterCount
public import PottsDiscontinuity.Frozen.Defs.RCWiredClusterCount

/-!
# Definition `rcWeight` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- The unnormalized weight `p^{o(ω)} (1-p)^{c(ω)} q^{kᵢ(ω)}`, `i ∈ {0, 1}`. -/
noncomputable def rcWeight (V : Finset (ℤ × ℤ)) (p q : ℝ) (i : Fin 2)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℝ :=
  p ^ Nat.card {e // ω e = true} * (1 - p) ^ Nat.card {e // ω e = false} *
    q ^ (if i = 0 then rcFreeClusterCount V ω else rcWiredClusterCount V ω)

end PottsDiscontinuity
