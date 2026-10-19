module

public import PottsDiscontinuity.RCInfinite.SpatialComparison

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PottsDiscontinuity.RCInfinite
open FK

theorem wired_limit_joint_le (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (m : ℕ) (F : Finset Edge) (hF : (F : Set Edge) ⊆ boxEdges (0, 0) m)
    (B : Set LatticeConfiguration) (hB : IsCylinder B)
    (hout : DependsOn (boxEdges (0, 0) m)ᶜ B) :
    μ.real (LatticeConfiguration.allOpen F ∩ B) ≤
      (wiredBoxProbabilityMeasure θ (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) * μ.real B := by
  apply le_of_tendsto_of_tendsto
    (tendsto_cylinder_probability θ 1 μ hμ ((isCylinder_allOpen F).inter hB))
    (tendsto_const_nhds.mul (tendsto_cylinder_probability θ 1 μ hμ hB))
  filter_upwards [eventually_ge_atTop m] with n hn
  simpa only [boxMeasure_wired] using
    wired_box_joint_le θ (latticeBox_mono (0, 0) hn) F hF B hB.measurableSet hout

theorem free_limit_joint_ge (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (m : ℕ) (F : Finset Edge) (hF : (F : Set Edge) ⊆ boxEdges (0, 0) m)
    (B : Set LatticeConfiguration) (hB : IsCylinder B)
    (hout : DependsOn (boxEdges (0, 0) m)ᶜ B) :
    (boxProbabilityMeasure θ (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) * μ.real B ≤
      μ.real (LatticeConfiguration.allOpen F ∩ B) := by
  apply le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul (tendsto_cylinder_probability θ 0 μ hμ hB))
    (tendsto_cylinder_probability θ 0 μ hμ ((isCylinder_allOpen F).inter hB))
  filter_upwards [eventually_ge_atTop m] with n hn
  simpa only [boxMeasure_free] using
    free_box_joint_ge θ (latticeBox_mono (0, 0) hn) F hF B hB.measurableSet hout

section Arithmetic
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem abs_covariance_le_of_upper (A B : Set X) (hB : MeasurableSet B) (u : ℝ)
    (h : μ.real (A ∩ B) ≤ u * μ.real B)
    (hc : μ.real (A ∩ Bᶜ) ≤ u * μ.real Bᶜ) :
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ u - μ.real A := by
  have hsumB : μ.real B + μ.real Bᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := μ) hB
  have hsumA : μ.real (A ∩ B) + μ.real (A ∩ Bᶜ) = μ.real A := by
    have ht := measureReal_inter_add_sdiff (μ := μ) (s := A) (t := B) hB
    simpa only [sdiff_eq_compl_inter, inter_comm] using ht
  have hbc : μ.real Bᶜ = 1 - μ.real B := by linarith
  have hjc : μ.real (A ∩ Bᶜ) = μ.real A - μ.real (A ∩ B) := by linarith
  rw [hbc, hjc] at hc
  have hδ : 0 ≤ u - μ.real A := by nlinarith [h, hc]
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hδ (measureReal_nonneg (μ := μ) (s := B))]
  · nlinarith [mul_nonneg hδ (sub_nonneg.mpr (measureReal_le_one (μ := μ) (s := B)))]

theorem abs_covariance_le_of_lower (A B : Set X) (hB : MeasurableSet B) (l : ℝ)
    (h : l * μ.real B ≤ μ.real (A ∩ B))
    (hc : l * μ.real Bᶜ ≤ μ.real (A ∩ Bᶜ)) :
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ μ.real A - l := by
  have hsumB : μ.real B + μ.real Bᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := μ) hB
  have hsumA : μ.real (A ∩ B) + μ.real (A ∩ Bᶜ) = μ.real A := by
    have ht := measureReal_inter_add_sdiff (μ := μ) (s := A) (t := B) hB
    simpa only [sdiff_eq_compl_inter, inter_comm] using ht
  have hbc : μ.real Bᶜ = 1 - μ.real B := by linarith
  have hjc : μ.real (A ∩ Bᶜ) = μ.real A - μ.real (A ∩ B) := by linarith
  rw [hbc, hjc] at hc
  have hδ : 0 ≤ μ.real A - l := by nlinarith [h, hc]
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hδ (sub_nonneg.mpr (measureReal_le_one (μ := μ) (s := B)))]
  · nlinarith [mul_nonneg hδ (measureReal_nonneg (μ := μ) (s := B))]

end Arithmetic

/-- Uniform decorrelation from the exterior of a box. The right side is the
single-cylinder box-limit error and is independent of the exterior event. -/
theorem cylinder_exterior_covariance_bound (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (m : ℕ) (F : Finset Edge) (hF : (F : Set Edge) ⊆ boxEdges (0, 0) m)
    (B : Set LatticeConfiguration) (hB : IsCylinder B)
    (hout : DependsOn (boxEdges (0, 0) m)ᶜ B) :
    |μ.real (LatticeConfiguration.allOpen F ∩ B) -
      μ.real (LatticeConfiguration.allOpen F) * μ.real B| ≤
      |(boxMeasure θ i (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) - μ.real (LatticeConfiguration.allOpen F)| := by
  have : IsProbabilityMeasure μ := hμ.1
  fin_cases i
  · have h := abs_covariance_le_of_lower μ _ B hB.measurableSet _
      (free_limit_joint_ge θ μ hμ m F hF B hB hout)
      (free_limit_joint_ge θ μ hμ m F hF Bᶜ hB.compl hout.compl)
    have hh := neg_le_abs
      ((boxProbabilityMeasure θ (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) - μ.real (LatticeConfiguration.allOpen F))
    simp only [neg_sub] at hh
    simpa [boxMeasure] using h.trans hh
  · simpa [boxMeasure] using (abs_covariance_le_of_upper μ _ B hB.measurableSet _
      (wired_limit_joint_le θ μ hμ m F hF B hB hout)
      (wired_limit_joint_le θ μ hμ m F hF Bᶜ hB.compl hout.compl)).trans
        (le_abs_self _)

end PottsDiscontinuity.RCInfinite
