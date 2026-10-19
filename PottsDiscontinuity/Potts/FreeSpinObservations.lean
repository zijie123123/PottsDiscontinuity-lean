module

public import PottsDiscontinuity.Potts.FreeCylinderPartition
public import PottsDiscontinuity.Potts.PottsWeakLimit
public import PottsDiscontinuity.Potts.SpinObservation

/-! General finite observations of any free Potts box limit. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
local instance freeObservationVertexDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq ↥(V : Set (ℤ × ℤ)) := fun _ _ => Classical.propDecidable _
local instance freeObservationVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype ↥(V : Set (ℤ × ℤ)) := Fintype.ofFinite _
local instance freeObservationEdgeDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet := fun _ _ => Classical.propDecidable _
local instance freeObservationEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _

/-- The colouring formula holds for any finite family of observations, including
repeated vertices, under any frozen free Potts box limit. -/
theorem free_spin_observation_formula {A : Type*} [Fintype A]
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (φ : ProbabilityMeasure FK.LatticeConfiguration)
    (hφ : Tendsto (fun n => FK.boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n) atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q)) (hμ : IsPottsInfiniteVolumeLimit q β 0 μ.toMeasure)
    (v : A → ℤ × ℤ) (ξ : A → Set.Icc 1 q) :
    μ.toMeasure.real (spinObservationEvent q v ξ) =
      partitionExpectation φ.toMeasure (infiniteFreePartition v) (fun R => clusterCylinderProbability R id ξ) := by
  have hp := free_partitionExpectation_tendsto (fkParameters q hq β hβ) φ hφ v
    (fun R => clusterCylinderProbability R id ξ)
  have hfinite : Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ 0 n).toMeasure.real
      (spinObservationEvent q v ξ)) atTop
      (𝓝 (partitionExpectation φ.toMeasure (infiniteFreePartition v) (fun R => clusterCylinderProbability R id ξ))) := by
    apply hp.congr'
    have hs : ∀ᶠ n : ℕ in atTop, ∀ a, v a ∈ box n :=
      Filter.eventually_all.mpr (fun a => FK.eventually_mem_box (v a))
    filter_upwards [hs] with n hn
    exact ((pottsBoxProbabilityMeasure_observed q hq β hβ 0 n v hn ξ).trans
      (potts_free_cylinder_eq_partitionExpectation q hq β hβ n v hn ξ)).symm
  have hw := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    (box_tendsto_of_isPottsInfiniteVolumeLimit q hq β hβ 0 μ hμ) (spinObservationEvent_isClopen q v ξ)
  have hr : Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ 0 n).toMeasure.real
      (spinObservationEvent q v ξ)) atTop (𝓝 (μ.toMeasure.real (spinObservationEvent q v ξ))) := by
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hw
  exact tendsto_nhds_unique hr hfinite

end
end PottsDiscontinuity.Potts
