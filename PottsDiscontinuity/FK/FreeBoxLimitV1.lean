/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.FreeBoxLimit

@[expose] public section

open MeasureTheory Filter Topology
namespace PottsDiscontinuity.FK

theorem freeBoxLimit_existsUnique (q : Parameters) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration,
      ∀ (c : ℕ → LatticeVertex) (r : ℕ → ℕ),
        (∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1))) →
        (∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) →
        Tendsto (fun n => boxProbabilityMeasure q (c n) (r n)) atTop (𝓝 μ) :=
by exact PottsDiscontinuity.FK.Internal.freeBoxLimit_existsUnique

end PottsDiscontinuity.FK
