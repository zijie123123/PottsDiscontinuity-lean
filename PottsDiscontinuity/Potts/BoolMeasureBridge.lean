module

public import PottsDiscontinuity.FK.IncreasingEvents

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance boolBridgeEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
attribute [local instance] FK.configurationMeasurableSpace

/-- The exact finite FK event probability on the Boolean carrier. -/
theorem fk_measureReal_eq_bool_sum (θ : FK.Parameters) (ξ : FK.BoundaryCondition V)
    (S : Set (FK.Configuration G)) :
    (FK.measure G θ ξ S).toReal =
      ∑ ω : G.edgeSet → Bool,
        if FK.boolConfigurationEquiv G ω ∈ S then
          FK.configurationProbability G θ ξ (FK.boolConfigurationEquiv G ω) else 0 := by
  rw [FK.measure_toReal_eq_indicator_sum, ← (FK.boolConfigurationEquiv G).sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : FK.boolConfigurationEquiv G ω ∈ S <;> simp [Set.indicator, h]

/-- Real event probabilities are finite sums of the original PMF masses. -/
theorem finite_pmf_measureReal_sum {E : Type*} [Fintype E] [MeasurableSpace E]
    [DiscreteMeasurableSpace E] (p : PMF E) (S : Set E) :
    p.toMeasure.real S = ∑ e : E, if e ∈ S then (p e).toReal else 0 := by
  rw [Measure.real, PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro e _
    by_cases he : e ∈ S <;> simp [Set.indicator, he]
  · intro e _
    by_cases he : e ∈ S <;> simp [Set.indicator, he, p.apply_ne_top]

end
end PottsDiscontinuity.Potts
