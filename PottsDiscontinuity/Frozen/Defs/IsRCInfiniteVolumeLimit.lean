module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.Box
public import PottsDiscontinuity.Frozen.Defs.RCProb

/-!
# Definition `IsRCInfiniteVolumeLimit` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

open Classical in
/-- `μ` is the infinite-volume random-cluster measure with boundary condition `i`: the
probability measure on `{0,1}^{E(ℤ²)}` to which `φⁱ_{Λₙ,p,q}` converge weakly, tested on all
finite-dimensional cylinder events. The finite volumes are the boxes `Λₙ` (author ruling R1). -/
def IsRCInfiniteVolumeLimit (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (i : Fin 2)
    (μ : Measure (squareLattice.edgeSet → Bool)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (A : Finset squareLattice.edgeSet) (ξ : squareLattice.edgeSet → Bool),
      Tendsto
        (fun n : ℕ =>
          ∑ ω : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet → Bool,
            if ∀ e ∈ A, ∃ f : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet,
                Sym2.map Subtype.val f.1 = e.1 ∧ ω f = ξ e
            then rcProb (box n) p q i ω else 0)
        atTop (𝓝 (μ.real {ω | ∀ e ∈ A, ω e = ξ e}))

end PottsDiscontinuity
