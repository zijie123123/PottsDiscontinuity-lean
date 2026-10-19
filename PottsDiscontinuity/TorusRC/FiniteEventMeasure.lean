module

public import PottsDiscontinuity.TorusRC.FiniteConnectionTransport
public import PottsDiscontinuity.TorusRC.CylinderFiberComparison
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Event expectations and lower semicontinuity of connection probabilities -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.TorusRC

open CorrLength FK

noncomputable section

/-- The finite event expectation is exactly the real measure of the event. -/
theorem torusRCFiberEventProbability_eq_measureReal {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α) (E : Set α) :
    torusRCFiberEventProbability p E = p.toMeasure.real E := by
  classical
  unfold torusRCFiberEventProbability FiniteProbability.expectation Measure.real
  rw [PMF.toMeasure_apply_fintype,ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ E <;> simp [Set.indicator,ha]
  · intro a _
    by_cases ha : a ∈ E <;> simp [Set.indicator,ha,p.apply_ne_top a]

attribute [local instance] configurationMeasurableSpace

local instance eventMeasureBoxEdges (c : LatticeVertex) (r : ℕ) :
    Fintype (boxGraph c r).edgeSet := Fintype.ofFinite _

/-- The finite induced-box connection event has the exact probability of the
finite-witness event under the closed-extended finite-box law. -/
theorem boxProbabilityMeasure_connection_eq (θ : Parameters) (c : LatticeVertex)
    (r : ℕ) (u v : BoxVertex c r) :
    (boxProbabilityMeasure θ c r).toMeasure.real (connectionEvent u.val v.val) =
      torusRCFiberEventProbability (law (boxGraph c r) θ (BoundaryCondition.free ∅))
        {A | ActualConnected (boxGraph c r) A u v} := by
  rw [torusRCFiberEventProbability_eq_measureReal]
  unfold Measure.real
  change (((law (boxGraph c r) θ (BoundaryCondition.free ∅)).map
    (boxConfiguration c r)).toMeasure (connectionEvent u.val v.val)).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top (connectionEvent_isMeasurableSet _ _)]
  congr 1
  congr 1
  ext A
  exact boxConfiguration_connection_iff c r A u v

/-- Finite-witness connection is an open event in the edge product topology. -/
theorem connectionEvent_isOpen (u v : LatticeVertex) : IsOpen (connectionEvent u v) := by
  rw [connectionEvent_eq_iUnion_connectionApprox]
  exact isOpen_iUnion fun k => (connectionApprox_isClopen u v k).isOpen

/-- Weak convergence makes every strict lower bound on an open-event limit
probability hold eventually for the finite measures. -/
theorem open_probability_eventually_gt {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    (μs : ℕ → ProbabilityMeasure Ω) (μ : ProbabilityMeasure Ω)
    (hweak : Tendsto μs atTop (𝓝 μ)) (E : Set Ω) (hE : IsOpen E)
    (t : ℝ) (ht : 0 ≤ t) (htμ : t < μ.toMeasure.real E) :
    ∀ᶠ k in atTop, t < (μs k).toMeasure.real E := by
  have hlt : ENNReal.ofReal t < μ.toMeasure E :=
    (ENNReal.ofReal_lt_iff_lt_toReal ht (measure_ne_top _ _)).mpr htμ
  have hlower := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hE
  have h := eventually_lt_of_lt_liminf (hlt.trans_le hlower)
  filter_upwards [h] with k hk
  exact (ENNReal.ofReal_lt_iff_lt_toReal ht (measure_ne_top _ _)).mp hk

end
end PottsDiscontinuity.TorusRC
