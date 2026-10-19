/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.BoxCompactness
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Actual finite all-open cylinders

The events refer to finitely many original whole-lattice edges. They are clopen
in the natural product topology, so weak limits preserve their probabilities.
Their finite-box probabilities are exactly the corresponding original FK events.
No existence or uniqueness of a full infinite-volume limit is asserted here.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open Set MeasureTheory Filter Topology
noncomputable section

namespace LatticeConfiguration

/-- All edges of this finite original lattice-edge set are open. -/
def allOpen (F : Finset squareLattice.edgeSet) : Set LatticeConfiguration :=
  {ω | ∀ e ∈ F, ω e = true}

@[simp] theorem allOpen_empty : allOpen ∅ = Set.univ := by
  ext ω
  simp [allOpen]

@[simp] theorem allOpen_insert (e : squareLattice.edgeSet) (F : Finset squareLattice.edgeSet) :
    allOpen (insert e F) = {ω | ω e = true} ∩ allOpen F := by
  classical
  ext ω
  simp [allOpen]

/-- These actual finite-edge events are simultaneously open and closed. -/
theorem allOpen_isClopen (F : Finset squareLattice.edgeSet) : IsClopen (allOpen F) := by
  classical
  induction F using Finset.induction_on with
  | empty => rw [allOpen_empty]; exact isClopen_univ
  | insert e F he ih =>
    rw [allOpen_insert]
    exact ((isClopen_discrete ({true} : Set Bool)).preimage (continuous_apply e)).inter ih

/-- A weakly convergent family has convergent probabilities for each genuine
finite all-open cylinder, since its boundary is empty. -/
theorem tendsto_allOpen_of_weak {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure LatticeConfiguration}
    {μ : ProbabilityMeasure LatticeConfiguration} (hμ : Tendsto μs l (𝓝 μ))
    (F : Finset squareLattice.edgeSet) :
    Tendsto (fun i => μs i (allOpen F)) l (𝓝 (μ (allOpen F))) :=
  ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ (allOpen_isClopen F)

end LatticeConfiguration


attribute [local instance] configurationMeasurableSpace

/-- Restricting a finite all-open cylinder to a box configuration tests literal
inclusion of the selected original edges in its embedded open-edge set. -/
theorem boxConfiguration_mem_allOpen (c : LatticeVertex) (r : ℕ)
    (A : Configuration (boxGraph c r)) (F : Finset squareLattice.edgeSet) :
    boxConfiguration c r A ∈ LatticeConfiguration.allOpen F ↔
      F ⊆ A.map (boxEdgeEmbedding c r) := by
  simp only [LatticeConfiguration.allOpen, Set.mem_ofPred_eq,
    boxConfiguration_open_iff, Finset.subset_iff]

/-- The probability on the common carrier equals the original normalized
finite FK measure of the exact all-open event. -/
theorem boxProbabilityMeasure_allOpen (q : Parameters) (c : LatticeVertex) (r : ℕ)
    (F : Finset squareLattice.edgeSet) :
    (boxProbabilityMeasure q c r : Measure LatticeConfiguration) (LatticeConfiguration.allOpen F) =
      measure (boxGraph c r) q (BoundaryCondition.free ∅)
        {A | F ⊆ A.map (boxEdgeEmbedding c r)} := by
  change ((law (boxGraph c r) q (BoundaryCondition.free ∅)).map
    (boxConfiguration c r)).toMeasure _ = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  congr 1
  ext A
  exact boxConfiguration_mem_allOpen c r A F

end
end PottsDiscontinuity.FK
