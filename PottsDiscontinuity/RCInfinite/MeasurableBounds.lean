module

public import PottsDiscontinuity.RCInfinite.CylinderApproximation
public import PottsDiscontinuity.RCInfinite.FiniteEnergy

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped symmDiff ENNReal

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section

theorem exists_supportedCylinder_real_approx (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    (E : Set Edge) {A : Set LatticeConfiguration} (hA : MeasurableSet A) (hdep : DependsOn E A)
    {ε : ℝ} (hε : 0 < ε) : ∃ C, SupportedCylinder E C ∧ μ.real (C ∆ A) < ε := by
  obtain ⟨C, hC, hCA⟩ := exists_supportedCylinder_approx μ E hA hdep (ENNReal.ofReal_pos.mpr hε)
  refine ⟨C, hC, ?_⟩
  have ht := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hCA
  simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using ht

theorem abs_inter_measureReal_sub_le (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    {A B D : Set LatticeConfiguration} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hD : MeasurableSet D) :
    |μ.real (A ∩ D) - μ.real (B ∩ D)| ≤ μ.real (A ∆ B) := by
  have h := abs_measureReal_sub_le_symmDiff μ (hA.inter hD) (hB.inter hD)
  have hsub : (A ∩ D) ∆ (B ∩ D) ⊆ A ∆ B := by
    intro x hx
    simp only [mem_symmDiff, mem_inter_iff] at hx ⊢
    tauto
  exact h.trans (measureReal_mono hsub)

theorem supported_lower_bound_extend (μ : Measure LatticeConfiguration) [IsFiniteMeasure μ]
    (E : Set Edge) {D : Set LatticeConfiguration} (hD : MeasurableSet D)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hbound : ∀ C, SupportedCylinder E C → c * μ.real C ≤ μ.real (C ∩ D))
    {B : Set LatticeConfiguration} (hB : MeasurableSet B) (hdep : DependsOn E B) :
    c * μ.real B ≤ μ.real (B ∩ D) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨C, hC, hCB⟩ := exists_supportedCylinder_real_approx μ E hB hdep
    (show 0 < ε / 4 by positivity)
  have hmass := abs_measureReal_sub_le_symmDiff μ hC.isCylinder.measurableSet hB
  have hjoint := abs_inter_measureReal_sub_le μ hC.isCylinder.measurableSet hB hD
  have hCbound := hbound C hC
  have hmass' : μ.real B ≤ μ.real C + μ.real (C ∆ B) := by
    linarith [(abs_le.mp hmass).1]
  have hscale := mul_le_mul_of_nonneg_left hmass' hc0
  have hscalediff : c * μ.real (C ∆ B) ≤ μ.real (C ∆ B) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (measureReal_nonneg (μ := μ) (s := C ∆ B))]
  nlinarith [(abs_le.mp hjoint).2]

theorem openEnergy_le_one (θ : Parameters) : openEnergy θ ≤ 1 := by
  unfold openEnergy
  apply (div_le_iff₀ (add_pos (edgeParameter_pos θ)
    (mul_pos (one_sub_edgeParameter_pos θ) (clusterWeight_pos θ)))).mpr
  nlinarith [mul_nonneg (one_sub_edgeParameter_pos θ).le (clusterWeight_nonneg θ)]

/-- Full measurable finite energy, obtained from supported cylinder
approximation without assuming a limiting conditional specification. -/
theorem measurable_finite_energy (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (e : Edge) {B : Set LatticeConfiguration} (hB : MeasurableSet B)
    (hind : DependsOn ({e}ᶜ) B) :
    openEnergy θ * μ.real B ≤ μ.real (B ∩ {ω | ω e = true}) ∧
    (1 - edgeParameter θ) * μ.real B ≤ μ.real (B ∩ {ω | ω e = false}) := by
  have : IsProbabilityMeasure μ := hμ.1
  constructor
  · apply supported_lower_bound_extend μ ({e}ᶜ) (isCylinder_coordinate e true).measurableSet
      (openEnergy θ) (openEnergy_pos θ).le (openEnergy_le_one θ) _ hB hind
    intro C hC
    exact (cylinder_finite_energy θ i μ hμ e hC.isCylinder hC.dependsOn).1
  · apply supported_lower_bound_extend μ ({e}ᶜ) (isCylinder_coordinate e false).measurableSet
      (1 - edgeParameter θ) (one_sub_edgeParameter_pos θ).le (by linarith [edgeParameter_pos θ])
      _ hB hind
    intro C hC
    exact (cylinder_finite_energy θ i μ hμ e hC.isCylinder hC.dependsOn).2

theorem measurable_finite_energy_uniform (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (e : Edge) {B : Set LatticeConfiguration} (hB : MeasurableSet B)
    (hind : DependsOn ({e}ᶜ) B) (b : Bool) :
    energyBound θ * μ.real B ≤ μ.real (B ∩ {ω | ω e = b}) := by
  have h := measurable_finite_energy θ i μ hμ e hB hind
  cases b
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) measureReal_nonneg).trans h.2
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) measureReal_nonneg).trans h.1

end
end PottsDiscontinuity.RCInfinite
