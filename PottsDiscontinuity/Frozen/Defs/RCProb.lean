module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.RCWeight

/-!
# Definition `rcProb` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

open Classical in
/-- The finite-volume random-cluster measure `φⁱ_{G,p,q}(ω) = weight / Zⁱ(G,p,q)`, for the
source parameter range `p ∈ [0, 1]`, `q > 0`. -/
noncomputable def rcProb (V : Finset (ℤ × ℤ)) (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (i : Fin 2) (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℝ :=
  rcWeight V p q i ω / ∑ ω', rcWeight V p q i ω'

end PottsDiscontinuity
