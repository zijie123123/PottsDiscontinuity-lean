module

public import PottsDiscontinuity.Potts.GhostCylinderPartition
public import PottsDiscontinuity.Potts.PottsWeakLimit
public import PottsDiscontinuity.Potts.SpinObservation

/-! General finite marked observations of any literal positive-boundary Potts limit. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
local instance wiredObservationLiteralDecidable (n : ℕ) : DecidableEq (LiteralBond (box n)) :=
  fun _ _ => Classical.propDecidable _
local instance wiredObservationBoundary (n : ℕ) : Fintype (BoundaryVertex (box n)) := Fintype.ofFinite _

theorem wired_spin_observation_formula {A : Type*} [Fintype A]
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (φ : ProbabilityMeasure FK.LatticeConfiguration)
    (hφ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n) atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q)) (hμ : IsPottsInfiniteVolumeLimit q β i μ.toMeasure)
    (v : A → ℤ × ℤ) (ξ : A → Set.Icc 1 q) :
    μ.toMeasure.real (spinObservationEvent q v ξ) =
      partitionExpectation φ.toMeasure (infiniteWiredPartition (Option.map v))
        (fun R => pinnedClusterCylinderProbability R some ξ none (boundaryColor q i hi)) := by
  have hp := wired_partitionExpectation_tendsto q hq β hβ φ hφ (Option.map v)
    (fun R => pinnedClusterCylinderProbability R some ξ none (boundaryColor q i hi))
  have hfinite : Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ i n).toMeasure.real
      (spinObservationEvent q v ξ)) atTop
      (𝓝 (partitionExpectation φ.toMeasure (infiniteWiredPartition (Option.map v))
        (fun R => pinnedClusterCylinderProbability R some ξ none (boundaryColor q i hi)))) := by
    apply hp.congr'
    have hs : ∀ᶠ n : ℕ in atTop, ∀ a, v a ∈ box n :=
      Filter.eventually_all.mpr (fun a => FK.eventually_mem_box (v a))
    filter_upwards [hs, eventually_gt_atTop 0] with n hn hn0
    exact ((pottsBoxProbabilityMeasure_observed q hq β hβ i n v hn ξ).trans
      (potts_ghost_cylinder_eq_partitionExpectation q hq β hβ i hi n hn0 v hn ξ)).symm
  have hw := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    (box_tendsto_of_isPottsInfiniteVolumeLimit q hq β hβ i μ hμ) (spinObservationEvent_isClopen q v ξ)
  have hr : Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ i n).toMeasure.real
      (spinObservationEvent q v ξ)) atTop (𝓝 (μ.toMeasure.real (spinObservationEvent q v ξ))) := by
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hw
  exact tendsto_nhds_unique hr hfinite

end
end PottsDiscontinuity.Potts
