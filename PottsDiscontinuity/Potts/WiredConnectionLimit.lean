module

public import PottsDiscontinuity.Potts.WiredConnectionEvents
public import PottsDiscontinuity.Potts.MonotoneEventLimits

/-! Convergence of wired connection data with every infinite cluster merged. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

/-- Every finite collection of required wired connections converges to the
corresponding merged infinite-cluster event. No infinite-cluster uniqueness is used. -/
theorem wired_connection_moments_tendsto (θ : FK.Parameters)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) :
    Tendsto (fun n => (openBoxProbabilityMeasure θ n).toMeasure.real (wiredDataEvent n F))
      atTop (𝓝 (μ.toMeasure.real (infiniteMergedDataEvent F))) := by
  rw [← iInter_wiredDataEvent F]
  apply decreasing_event_diagonal_tendsto _ μ _ (wiredDataEvent_antitone F)
    (fun n => (wiredDataEvent_isClopen n F).isOpen.measurableSet)
  · intro m
    have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ (wiredDataEvent_isClopen m F)
    simpa only [openBoxProbabilityMeasure_eq_wired, ProbabilityMeasure.measureReal_eq_coe_coeFn,
      Function.comp_def] using NNReal.continuous_coe.continuousAt.tendsto.comp ht
  · intro n
    rw [wiredDataEvent_eq_observation]
    simp only [Measure.real]
    rw [openBoxProbabilityMeasure_observation_self]
    exact wired_limit_observation_le θ μ hμ n (wiredDataFiniteEvent n F) (wiredDataFiniteEvent_upper n F)

end
end PottsDiscontinuity.Potts
