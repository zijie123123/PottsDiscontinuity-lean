module

public import PottsDiscontinuity.RCInfinite.LimitComparison
public import PottsDiscontinuity.RCInfinite.TranslationSupport
public import PottsDiscontinuity.RCInfinite.CylinderApproximation

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped symmDiff

namespace PottsDiscontinuity.RCInfinite
open FK

def covariance (μ : Measure LatticeConfiguration) (A B : Set LatticeConfiguration) : ℝ :=
  μ.real (A ∩ B) - μ.real A * μ.real B

theorem covariance_change_right (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    {A B C : Set LatticeConfiguration} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    |covariance μ A B - covariance μ A C| ≤ 2 * μ.real (B ∆ C) := by
  have hdiff := abs_measureReal_sub_le_symmDiff μ hB hC
  have hjoint := abs_measureReal_sub_le_symmDiff μ (hA.inter hB) (hA.inter hC)
  have hsub : (A ∩ B) ∆ (A ∩ C) ⊆ B ∆ C := by
    intro x hx
    simp only [mem_symmDiff, mem_inter_iff] at hx ⊢
    tauto
  have hjoint' : |μ.real (A ∩ B) - μ.real (A ∩ C)| ≤ μ.real (B ∆ C) :=
    hjoint.trans (measureReal_mono hsub)
  have hprod : |μ.real A * (μ.real B - μ.real C)| ≤ μ.real (B ∆ C) := by
    rw [abs_mul, abs_of_nonneg measureReal_nonneg]
    have hm := mul_le_mul_of_nonneg_left hdiff (measureReal_nonneg (μ := μ) (s := A))
    nlinarith [mul_nonneg (sub_nonneg.mpr (measureReal_le_one (μ := μ) (s := A)))
      (measureReal_nonneg (μ := μ) (s := B ∆ C))]
  calc
    |covariance μ A B - covariance μ A C| =
        |(μ.real (A ∩ B) - μ.real (A ∩ C)) - μ.real A * (μ.real B - μ.real C)| := by
          unfold covariance
          congr 1
          ring
    _ ≤ |μ.real (A ∩ B) - μ.real (A ∩ C)| + |μ.real A * (μ.real B - μ.real C)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (μ.real (A ∩ B) - μ.real (A ∩ C)) 0 (μ.real A * (μ.real B - μ.real C))
    _ ≤ μ.real (B ∆ C) + μ.real (B ∆ C) := add_le_add hjoint' hprod
    _ = 2 * μ.real (B ∆ C) := by ring

theorem allOpen_cylinder_covariance_tendsto_zero (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (F : Finset Edge) {B : Set LatticeConfiguration} (hB : IsCylinder B) :
    Tendsto (fun n : ℕ => covariance μ (LatticeConfiguration.allOpen F)
      ((edgeTranslate ((n : ℤ), 0)) ⁻¹' B)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have herror : Tendsto (fun m =>
      |(boxMeasure θ i (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) - μ.real (LatticeConfiguration.allOpen F)|)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      ((tendsto_cylinder_probability θ i μ hμ (isCylinder_allOpen F)).sub
        (tendsto_const_nhds (x := μ.real (LatticeConfiguration.allOpen F)))).abs
  have herr := herror.eventually (gt_mem_nhds hε)
  obtain ⟨m, hFm, hm⟩ := ((eventually_finset_in_box F).and herr).exists
  filter_upwards [eventually_cylinder_translate_outside m hB] with n hn
  have hbound := cylinder_exterior_covariance_bound θ i μ hμ m F hFm
    ((edgeTranslate ((n : ℤ), 0)) ⁻¹' B) (hB.preimage_translate _) hn
  simpa only [Real.dist_eq, sub_zero, covariance] using hbound.trans_lt hm

/-- Mixing of every all-open generator against any measurable event, along
horizontal translations. This already suffices for full translation ergodicity. -/
theorem allOpen_measurable_covariance_tendsto_zero (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (F : Finset Edge) {B : Set LatticeConfiguration} (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ => covariance μ (LatticeConfiguration.allOpen F)
      ((edgeTranslate ((n : ℤ), 0)) ⁻¹' B)) atTop (𝓝 0) := by
  have : IsProbabilityMeasure μ := hμ.1
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C, hC, hCB⟩ := exists_cylinder_approx μ hB (show 0 < ε / 4 by positivity)
  have hlim := allOpen_cylinder_covariance_tendsto_zero θ i μ hμ F hC
  have hevent := (Metric.tendsto_nhds.mp hlim) (ε / 2) (half_pos hε)
  filter_upwards [hevent] with n hn
  let a : LatticeVertex := ((n : ℤ), 0)
  have hchange := covariance_change_right μ (isCylinder_allOpen F).measurableSet
    ((edgeTranslate_measurable a) hB) ((edgeTranslate_measurable a) hC.measurableSet)
  have hmass : μ.real (((edgeTranslate a) ⁻¹' B) ∆ ((edgeTranslate a) ⁻¹' C)) =
      μ.real (C ∆ B) := by
    rw [← Set.preimage_symmDiff, limit_translate_real θ i μ hμ a (hB.symmDiff hC.measurableSet),
      symmDiff_comm]
  rw [hmass] at hchange
  have htriangle := abs_sub_le (covariance μ (LatticeConfiguration.allOpen F) ((edgeTranslate a) ⁻¹' B))
    (covariance μ (LatticeConfiguration.allOpen F) ((edgeTranslate a) ⁻¹' C)) 0
  simp only [sub_zero, Real.dist_eq] at hn ⊢
  simp only [sub_zero] at htriangle
  change |covariance μ (LatticeConfiguration.allOpen F) ((edgeTranslate a) ⁻¹' B)| < ε
  nlinarith [htriangle, hchange]

theorem allOpen_measurable_joint_tendsto (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (F : Finset Edge) {B : Set LatticeConfiguration} (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ => μ.real (LatticeConfiguration.allOpen F ∩
      (edgeTranslate ((n : ℤ), 0)) ⁻¹' B)) atTop
      (𝓝 (μ.real (LatticeConfiguration.allOpen F) * μ.real B)) := by
  have h := (allOpen_measurable_covariance_tendsto_zero θ i μ hμ F hB).add
    (tendsto_const_nhds (x := μ.real (LatticeConfiguration.allOpen F) * μ.real B))
  have hmean (n : ℕ) := limit_translate_real θ i μ hμ ((n : ℤ), 0) hB
  simpa only [covariance, hmean, sub_add_cancel, zero_add] using h

end PottsDiscontinuity.RCInfinite
