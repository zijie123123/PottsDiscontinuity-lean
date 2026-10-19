module

public import PottsDiscontinuity.Potts.BoxObservation

/-! Free finite-volume observations and their infinite-volume domination. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
attribute [local instance] FK.configurationMeasurableSpace

/-- Closed exterior extension of an actual free finite configuration. -/
def closedExtension (V : Finset (ℤ × ℤ))
    (C : FK.Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) : FK.LatticeConfiguration :=
  fun e => decide (∃ f, FK.frozenEdgeEmbedding V f = e ∧ f ∈ C)

@[simp] theorem closedExtension_at (V : Finset (ℤ × ℤ))
    (C : FK.Configuration (squareLattice.induce (V : Set (ℤ × ℤ))))
    (f : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet) :
    closedExtension V C (FK.frozenEdgeEmbedding V f) = decide (f ∈ C) := by
  have h : (∃ g, FK.frozenEdgeEmbedding V g = FK.frozenEdgeEmbedding V f ∧ g ∈ C) ↔ f ∈ C := by
    constructor
    · rintro ⟨g, hg, hmem⟩
      exact (FK.frozenEdgeEmbedding V).injective hg ▸ hmem
    · exact fun hf => ⟨f, rfl, hf⟩
  simp only [closedExtension, h]

def closedBoxProbabilityMeasure (θ : FK.Parameters) (n : ℕ) : ProbabilityMeasure FK.LatticeConfiguration :=
  FK.frozenExtendedProbabilityMeasure θ (box n) 0 (closedExtension (box n))

theorem closedBoxProbabilityMeasure_eq_free (θ : FK.Parameters) (n : ℕ) :
    closedBoxProbabilityMeasure θ n = FK.boxProbabilityMeasure θ (0, 0) n := by
  unfold closedBoxProbabilityMeasure
  rw [← FK.latticeBox_origin_eq_box n]
  have hext : closedExtension (FK.latticeBox (0, 0) n) = FK.boxConfiguration (0, 0) n := by
    funext C e
    unfold closedExtension FK.boxConfiguration
    apply Bool.decide_congr
    constructor
    · rintro ⟨f, hf, hmem⟩
      exact Finset.mem_map.mpr ⟨f, hmem, hf⟩
    · rintro h
      obtain ⟨f, hmem, hf⟩ := Finset.mem_map.mp h
      exact ⟨f, hf, hmem⟩
  rw [hext, FK.frozenExtendedProbabilityMeasure_free]

theorem boxObservation_closedExtension {m n : ℕ} (h : m ≤ n)
    (C : FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :
    boxObservation m (closedExtension (box n) C) =
      FK.embeddedConfigurationRestriction _ _ (nestedBoxEmbedding h) (nestedBox_map_le h) C := by
  ext e
  unfold boxObservation
  rw [FK.mem_embeddedConfigurationRestriction, FK.mem_boolConfigurationEquiv]
  rw [← nestedEdgeEmbedding_compatible h e, closedExtension_at, decide_eq_true_eq]

theorem closedBoxProbabilityMeasure_observation (θ : FK.Parameters) {m n : ℕ} (h : m ≤ n)
    (S : Set (FK.Configuration (squareLattice.induce (box m : Set (ℤ × ℤ))))) :
    (closedBoxProbabilityMeasure θ n).toMeasure (boxObservationEvent m S) =
      FK.measure _ θ (FK.BoundaryCondition.free {x | x.val ∈ vertexBoundary (box n)})
        (nestedBoxEvent h S) := by
  change (((FK.law _ θ (FK.frozenBoundaryCondition (box n) 0)).map
    (closedExtension (box n))).toMeasure _) = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    (boxObservationEvent_isClopen m S).isOpen.measurableSet]
  congr 1
  ext C
  exact congrArg (fun A => A ∈ S) (boxObservation_closedExtension h C) |>.to_iff

private theorem free_nested_event_comparison (θ : FK.Parameters) {m n : ℕ} (h : m ≤ n)
    (S : Set (FK.Configuration (squareLattice.induce (box m : Set (ℤ × ℤ))))) (hS : IsUpperSet S) :
    (FK.measure _ θ (FK.BoundaryCondition.free {x | x.val ∈ vertexBoundary (box m)}) S).toReal ≤
      (FK.measure _ θ (FK.BoundaryCondition.free {x | x.val ∈ vertexBoundary (box n)})
        (nestedBoxEvent h S)).toReal := by
  let ind := S.indicator (fun _ => (1 : ℝ))
  have hi0 : ∀ C, 0 ≤ ind C := by intro C; by_cases h : C ∈ S <;> simp [ind, h]
  have him : Monotone ind := by
    intro C D hCD
    by_cases hC : C ∈ S
    · have hD := hS hCD hC
      simp [ind, hC, hD]
    · simp only [ind, Set.indicator_of_notMem hC]
      exact hi0 D
  have hc := FK.embedded_free_expectation_le _ _ (nestedBoxEmbedding h) (nestedBox_map_le h)
    θ {x | x.val ∈ vertexBoundary (box m)} {x | x.val ∈ vertexBoundary (box n)} ind hi0 him
  simp only [FK.measure_toReal_eq_indicator_sum]
  unfold FK.FiniteProbability.expectation at hc
  simp only [FK.law_apply, ENNReal.toReal_ofReal (FK.configurationProbability_pos _ _ _ _).le] at hc
  exact hc

/-- Increasing finite free events are dominated by the free box limit. -/
theorem free_observation_le_limit (θ : FK.Parameters)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (m : ℕ) (S : Set (FK.Configuration (squareLattice.induce (box m : Set (ℤ × ℤ)))))
    (hS : IsUpperSet S) :
    (FK.measure _ θ (FK.BoundaryCondition.free {x | x.val ∈ vertexBoundary (box m)}) S).toReal ≤
      μ.toMeasure.real (boxObservationEvent m S) := by
  have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ
    (boxObservationEvent_isClopen m S)
  have hreal : Tendsto (fun n => (closedBoxProbabilityMeasure θ n).toMeasure.real
      (boxObservationEvent m S)) atTop (𝓝 (μ.toMeasure.real (boxObservationEvent m S))) := by
    simpa only [closedBoxProbabilityMeasure_eq_free, ProbabilityMeasure.measureReal_eq_coe_coeFn,
      Function.comp_def] using NNReal.continuous_coe.continuousAt.tendsto.comp ht
  apply ge_of_tendsto hreal
  filter_upwards [eventually_ge_atTop m] with n hn
  rw [Measure.real, closedBoxProbabilityMeasure_observation θ hn]
  exact free_nested_event_comparison θ hn S hS

@[simp] theorem boxObservation_closedExtension_self (n : ℕ)
    (C : FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))) :
    boxObservation n (closedExtension (box n) C) = C := by
  ext e
  unfold boxObservation
  rw [FK.mem_boolConfigurationEquiv, closedExtension_at, decide_eq_true_eq]

end
end PottsDiscontinuity.Potts
