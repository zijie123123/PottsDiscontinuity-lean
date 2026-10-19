module

public import PottsDiscontinuity.Potts.FreeBoxObservation
public import PottsDiscontinuity.Potts.FreeConnectionEvents
public import PottsDiscontinuity.Potts.MonotoneEventLimits

/-! Free connection-data limits use actual connections, without merging. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

/-- Every finite collection of free connections converges to the actual
open-graph connections under the free box limit. -/
theorem free_connection_moments_tendsto (θ : FK.Parameters)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (F : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    Tendsto (fun n => (closedBoxProbabilityMeasure θ n).toMeasure.real (freeDataEvent n F))
      atTop (𝓝 (μ.toMeasure.real (infiniteFreeDataEvent F))) := by
  rw [← iUnion_freeDataEvent F]
  apply increasing_event_diagonal_tendsto _ μ _ (freeDataEvent_monotone F)
  · intro m
    have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ (freeDataEvent_isClopen m F)
    simpa only [closedBoxProbabilityMeasure_eq_free, ProbabilityMeasure.measureReal_eq_coe_coeFn,
      Function.comp_def] using NNReal.continuous_coe.continuousAt.tendsto.comp ht
  · intro n
    rw [freeDataEvent_eq_observation]
    simp only [Measure.real]
    rw [closedBoxProbabilityMeasure_observation θ (Nat.le_refl n), nestedBoxEvent_refl]
    exact free_observation_le_limit θ μ hμ n (freeDataFiniteEvent n F) (freeDataFiniteEvent_upper n F)

end
end PottsDiscontinuity.Potts
