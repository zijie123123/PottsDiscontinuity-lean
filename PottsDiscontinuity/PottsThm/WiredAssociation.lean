module

public import PottsDiscontinuity.FK.WiredBoxLaw
public import PottsDiscontinuity.FK.IncreasingEvents

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK

noncomputable section

attribute [local instance] configurationMeasurableSpace

private theorem wiredBoxConfiguration_mono (c : LatticeVertex) (r : ℕ)
    {A B : Configuration (boxGraph c r)} (hAB : A ≤ B) :
    wiredBoxConfiguration c r A ≤ wiredBoxConfiguration c r B := by
  intro e
  by_cases hA : wiredBoxConfiguration c r A e = true
  · have hprop := (wiredBoxConfiguration_open_iff c r A e).mp hA
    have hpropB : ∀ f, boxEdgeEmbedding c r f = e → f ∈ B := by
      intro f hf
      exact hAB (hprop f hf)
    have hB : wiredBoxConfiguration c r B e = true :=
      (wiredBoxConfiguration_open_iff c r B e).mpr hpropB
    simp [hA, hB]
  · have hAfalse : wiredBoxConfiguration c r A e = false := by
      cases h : wiredBoxConfiguration c r A e <;> simp_all
    simp [hAfalse]

private theorem wiredBoxProbabilityMeasure_apply_preimage
    (θ : Parameters) (c : LatticeVertex) (r : ℕ) (s : Set LatticeConfiguration)
    (hs : MeasurableSet s) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration) s =
      measure (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))
        {A | wiredBoxConfiguration c r A ∈ s} := by
  change ((law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))).map
    (wiredBoxConfiguration c r)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

private theorem wiredBoxProbabilityMeasure_finite_positive_association
    (θ : Parameters) (c : LatticeVertex) (r : ℕ)
    (s t : Set LatticeConfiguration) (hsUpper : IsUpperSet s)
    (htUpper : IsUpperSet t) (hsMeas : MeasurableSet s) (htMeas : MeasurableSet t) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real s *
      (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real t ≤
        (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real (s ∩ t) := by
  let sbox : Set (Configuration (boxGraph c r)) :=
    {A | wiredBoxConfiguration c r A ∈ s}
  let tbox : Set (Configuration (boxGraph c r)) :=
    {A | wiredBoxConfiguration c r A ∈ t}
  have hsbox : IsUpperSet sbox := by
    intro A B hAB hA
    exact hsUpper (wiredBoxConfiguration_mono c r hAB) hA
  have htbox : IsUpperSet tbox := by
    intro A B hAB hA
    exact htUpper (wiredBoxConfiguration_mono c r hAB) hA
  have h := measure_positive_association θ
    (BoundaryCondition.wired (boxVertexBoundary c r)) sbox tbox hsbox htbox
  have hS := wiredBoxProbabilityMeasure_apply_preimage θ c r s hsMeas
  have hT := wiredBoxProbabilityMeasure_apply_preimage θ c r t htMeas
  have hST := wiredBoxProbabilityMeasure_apply_preimage θ c r (s ∩ t)
    (hsMeas.inter htMeas)
  have hsets : sbox ∩ tbox =
      {A | wiredBoxConfiguration c r A ∈ s ∩ t} := by
    ext A
    simp [sbox, tbox]
  rw [Measure.real_def, Measure.real_def, Measure.real_def]
  rw [hS, hT, hST]
  rw [hsets] at h
  exact h

/-- Positive association for increasing clopen events under every actual wired
infinite-volume limit. -/
theorem wired_clopen_positive_association (θ : Parameters)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 φ))
    (s t : Set LatticeConfiguration) (hsClopen : IsClopen s)
    (htClopen : IsClopen t) (hsUpper : IsUpperSet s) (htUpper : IsUpperSet t) :
    φ.toMeasure.real s * φ.toMeasure.real t ≤ φ.toMeasure.real (s ∩ t) := by
  have hS : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n s) atTop
      (𝓝 (φ s)) := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hφ hsClopen
  have hT : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n t) atTop
      (𝓝 (φ t)) := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hφ htClopen
  have hST : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n (s ∩ t)) atTop
      (𝓝 (φ (s ∩ t))) := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hφ
        (hsClopen.inter htClopen)
  have hSreal : Tendsto (fun n =>
      (((wiredBoxProbabilityMeasure θ (0, 0) n s : NNReal) : ℝ))) atTop
      (𝓝 ((φ s : NNReal) : ℝ)) :=
    (NNReal.continuous_coe.continuousAt.tendsto).comp hS
  have hTreal : Tendsto (fun n =>
      (((wiredBoxProbabilityMeasure θ (0, 0) n t : NNReal) : ℝ))) atTop
      (𝓝 ((φ t : NNReal) : ℝ)) :=
    (NNReal.continuous_coe.continuousAt.tendsto).comp hT
  have hSTreal : Tendsto (fun n =>
      (((wiredBoxProbabilityMeasure θ (0, 0) n (s ∩ t) : NNReal) : ℝ))) atTop
      (𝓝 ((φ (s ∩ t) : NNReal) : ℝ)) :=
    (NNReal.continuous_coe.continuousAt.tendsto).comp hST
  have hprod : Tendsto (fun n =>
      (((wiredBoxProbabilityMeasure θ (0, 0) n s : NNReal) : ℝ) *
        ((wiredBoxProbabilityMeasure θ (0, 0) n t : NNReal) : ℝ))) atTop
      (𝓝 (((φ s : NNReal) : ℝ) * ((φ t : NNReal) : ℝ))) := hSreal.mul hTreal
  have hfinite (n : ℕ) :
      (((wiredBoxProbabilityMeasure θ (0, 0) n s : NNReal) : ℝ) *
        ((wiredBoxProbabilityMeasure θ (0, 0) n t : NNReal) : ℝ)) ≤
        ((wiredBoxProbabilityMeasure θ (0, 0) n (s ∩ t) : NNReal) : ℝ) := by
    have h := wiredBoxProbabilityMeasure_finite_positive_association θ (0, 0) n s t
      hsUpper htUpper hsClopen.2.measurableSet htClopen.2.measurableSet
    simpa [ProbabilityMeasure.measureReal_eq_coe_coeFn] using h
  have hlim := le_of_tendsto_of_tendsto' hprod hSTreal hfinite
  have hrealS : φ.toMeasure.real s = (φ s : ℝ) := by
    exact ProbabilityMeasure.measureReal_eq_coe_coeFn φ s
  have hrealT : φ.toMeasure.real t = (φ t : ℝ) := by
    exact ProbabilityMeasure.measureReal_eq_coe_coeFn φ t
  have hrealST : φ.toMeasure.real (s ∩ t) = (φ (s ∩ t) : ℝ) := by
    exact ProbabilityMeasure.measureReal_eq_coe_coeFn φ (s ∩ t)
  simpa only [hrealS, hrealT, hrealST] using hlim

end
end PottsDiscontinuity.PottsThm
