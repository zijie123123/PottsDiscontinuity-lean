/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.FreeBoxLimitV1

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.FK.Internal

noncomputable section

attribute [local instance] configurationMeasurableSpace

theorem boxConfiguration_mono (c : LatticeVertex) (r : ℕ)
    {A B : Configuration (boxGraph c r)} (hAB : A ≤ B) :
    boxConfiguration c r A ≤ boxConfiguration c r B := by
  classical
  have hmap : A.map (boxEdgeEmbedding c r) ⊆ B.map (boxEdgeEmbedding c r) :=
    (Finset.map_subset_map).2 hAB
  intro e
  by_cases hA : e ∈ A.map (boxEdgeEmbedding c r)
  · have hB : e ∈ B.map (boxEdgeEmbedding c r) := hmap hA
    simp [boxConfiguration, hA, hB]
  · simp [boxConfiguration, hA]

private theorem boxProbabilityMeasure_apply_preimage (q : Parameters)
    (c : LatticeVertex) (r : ℕ) (s : Set LatticeConfiguration)
    (hs : MeasurableSet s) :
    (boxProbabilityMeasure q c r : Measure LatticeConfiguration) s =
      measure (boxGraph c r) q (BoundaryCondition.free ∅)
        {A | boxConfiguration c r A ∈ s} := by
  change ((law (boxGraph c r) q (BoundaryCondition.free ∅)).map
    (boxConfiguration c r)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

private theorem boxProbabilityMeasure_finite_positive_association
    (q : Parameters) (c : LatticeVertex) (r : ℕ)
    (s t : Set LatticeConfiguration) (hsUpper : IsUpperSet s)
    (htUpper : IsUpperSet t) (hsMeas : MeasurableSet s) (htMeas : MeasurableSet t) :
    (boxProbabilityMeasure q c r : Measure LatticeConfiguration).real s *
      (boxProbabilityMeasure q c r : Measure LatticeConfiguration).real t ≤
        (boxProbabilityMeasure q c r : Measure LatticeConfiguration).real (s ∩ t) := by
  let sbox : Set (Configuration (boxGraph c r)) :=
    {A | boxConfiguration c r A ∈ s}
  let tbox : Set (Configuration (boxGraph c r)) :=
    {A | boxConfiguration c r A ∈ t}
  have hsbox : IsUpperSet sbox := by
    intro A B hAB hA
    exact hsUpper (boxConfiguration_mono c r hAB) hA
  have htbox : IsUpperSet tbox := by
    intro A B hAB hA
    exact htUpper (boxConfiguration_mono c r hAB) hA
  have h := measure_positive_association q (BoundaryCondition.free ∅) sbox tbox hsbox htbox
  have hS := boxProbabilityMeasure_apply_preimage q c r s hsMeas
  have hT := boxProbabilityMeasure_apply_preimage q c r t htMeas
  have hST := boxProbabilityMeasure_apply_preimage q c r (s ∩ t) (hsMeas.inter htMeas)
  have hsets : sbox ∩ tbox = {A | boxConfiguration c r A ∈ s ∩ t} := by
    ext A
    simp [sbox, tbox]
  rw [Measure.real_def, Measure.real_def, Measure.real_def]
  rw [hS, hT, hST]
  rw [hsets] at h
  exact h

/-- Positive association under the unique free-box law for any two increasing clopen events of the original lattice configuration space. -/
theorem freeBoxLimit_clopen_positive_association (q : Parameters)
    (s t : Set LatticeConfiguration) (hsClopen : IsClopen s)
    (htClopen : IsClopen t) (hsUpper : IsUpperSet s) (htUpper : IsUpperSet t) :
    (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q) s : ℝ) *
      (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q) t : ℝ) ≤
        (Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q) (s ∩ t) : ℝ) := by
  let μ : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)
  have hweak : Tendsto (fun n => boxProbabilityMeasure q (0, 0) n) atTop (𝓝 μ) :=
    (Classical.choose_spec (PottsDiscontinuity.FK.freeBoxLimit_existsUnique q)).1
      (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  have hS : Tendsto (fun n => boxProbabilityMeasure q (0, 0) n s) atTop (𝓝 (μ s)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak hsClopen
  have hT : Tendsto (fun n => boxProbabilityMeasure q (0, 0) n t) atTop (𝓝 (μ t)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak htClopen
  have hST : Tendsto (fun n => boxProbabilityMeasure q (0, 0) n (s ∩ t)) atTop
      (𝓝 (μ (s ∩ t))) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak
      (hsClopen.inter htClopen)
  have hSreal : Tendsto (fun n =>
      (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) s : NNReal) : ℝ)) atTop
      (𝓝 ((μ s : NNReal) : ℝ)) :=
    (NNReal.continuous_coe.continuousAt.tendsto).comp hS
  have hTreal : Tendsto (fun n =>
      (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) t : NNReal) : ℝ)) atTop
      (𝓝 ((μ t : NNReal) : ℝ)) :=
    (NNReal.continuous_coe.continuousAt.tendsto).comp hT
  have hSTreal : Tendsto (fun n =>
      (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) (s ∩ t) : NNReal) : ℝ)) atTop
      (𝓝 ((μ (s ∩ t) : NNReal) : ℝ)) :=
    (NNReal.continuous_coe.continuousAt.tendsto).comp hST
  have hprod : Tendsto (fun n =>
      (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) s : NNReal) : ℝ) *
        (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) t : NNReal) : ℝ)) atTop
      (𝓝 (((μ s : NNReal) : ℝ) * ((μ t : NNReal) : ℝ))) := hSreal.mul hTreal
  have hfinite (n : ℕ) :
      (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) s : NNReal) : ℝ) *
        (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) t : NNReal) : ℝ) ≤
          (((boxProbabilityMeasure q (0, 0) n : ProbabilityMeasure LatticeConfiguration) (s ∩ t) : NNReal) : ℝ) := by
    have h := boxProbabilityMeasure_finite_positive_association q (0, 0) n s t
      hsUpper htUpper hsClopen.2.measurableSet htClopen.2.measurableSet
    simpa [ProbabilityMeasure.measureReal_eq_coe_coeFn] using h
  have hlimit := le_of_tendsto_of_tendsto' hprod hSTreal hfinite
  simpa [μ] using hlimit

end
end PottsDiscontinuity.FK.Internal
