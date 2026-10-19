/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.BoxLaw
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Sequences

/-!
# Subsequence compactness for the actual finite-box configuration laws

The whole-lattice edge-state space is a countable product of the discrete finite
space Bool. Its probability measures carry their usual topology of weak
convergence. Complete mathlib compactness and metrizability theorems yield
subsequential limits for the actual closed-extended box laws. No uniqueness or
full-volume convergence is claimed here, and this is not tightness of rescaled
interface curves or loop collections.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open MeasureTheory Filter Topology
noncomputable section

/-- The original free FK box PMF on the natural product measurable space. -/
def boxProbabilityMeasure (q : Parameters) (c : LatticeVertex) (r : ℕ) :
    ProbabilityMeasure LatticeConfiguration :=
  ⟨(boxLaw q c r).toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩

end
end PottsDiscontinuity.FK
