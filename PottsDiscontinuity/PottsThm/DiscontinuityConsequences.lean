module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.Discontinuity
public import PottsDiscontinuity.PottsThm.CriticalParameters

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.Duality

theorem free_no_infinite_clusters (θ : FK.Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (hzero : μ (Duality.infiniteClusterAt 0) = 0) :
    μ Duality.existsInfiniteCluster = 0 := by
  have hsite (x : LatticeVertex) : μ (RCInfinite.infiniteAt x) = 0 := by
    have htrans := congrArg (fun ν : Measure LatticeConfiguration =>
      ν (RCInfinite.infiniteAt x))
      (isRCInfiniteVolumeLimit_interior_translation_invariant θ 0 μ hμ x)
    rw [Measure.map_apply (RCInfinite.edgeTranslate_measurable x)
      (RCInfinite.measurableSet_infiniteAt x)] at htrans
    have hpre : (RCInfinite.edgeTranslate x) ⁻¹' RCInfinite.infiniteAt x =
        RCInfinite.infiniteAt 0 := by
      simpa [latticeTranslate] using (RCInfinite.infiniteAt_preimage x 0)
    rw [hpre] at htrans
    simpa [Duality.infiniteClusterAt_eq_infiniteAt] using htrans.symm.trans hzero
  have hunion : μ RCInfinite.infiniteClusterEvent = 0 := by
    rw [RCInfinite.infiniteClusterEvent_eq_iUnion]
    apply measure_iUnion_null
    intro x
    exact hsite x
  simpa [Duality.existsInfiniteCluster_eq_infiniteClusterEvent] using hunion

/-- The positive RC rate premise gives the free no-infinite-cluster and wired
positive-origin conclusions at the exact Potts critical parameters. -/
theorem rc_discontinuity_of_positive_rate (q : ℕ) (hq : 4 < q)
    (φ₀ φ₁ : ProbabilityMeasure LatticeConfiguration)
    (hφ₀ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 0 φ₀.toMeasure)
    (hφ₁ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 1 φ₁.toMeasure)
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
      (φ₀.toMeasure.real
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
      atTop (𝓝 L)) :
    φ₀.toMeasure (infiniteClusterAt 0) = 0 ∧
      0 < φ₁.toMeasure (infiniteClusterAt 0) := by
  let qR : Set.Ici (1 : ℝ) := ⟨(q : ℝ), by
    change (1 : ℝ) ≤ (q : ℝ)
    exact_mod_cast (show 1 ≤ q by omega)⟩
  have hparams := fkCritical_toP_toQ q hq
  have hφ₀' : IsRCInfiniteVolumeLimit (FK.criticalParameters qR).toP
      (FK.criticalParameters qR).toQ 0 φ₀.toMeasure := by
    have hh := hφ₀
    rw [(fkCritical_toP_toQ q hq).1, (fkCritical_toP_toQ q hq).2] at hh
    simpa [qR] using hh
  have hφ₁' : IsRCInfiniteVolumeLimit (FK.criticalParameters qR).toP
      (FK.criticalParameters qR).toQ 1 φ₁.toMeasure := by
    have hh := hφ₁
    rw [(fkCritical_toP_toQ q hq).1, (fkCritical_toP_toQ q hq).2] at hh
    simpa [qR] using hh
  have hrate' : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
      (Duality.twoPoint φ₀.toMeasure (diagonalSite n))) atTop (𝓝 L) := by
    apply hrate.congr'
    filter_upwards with n
    have hevent : Duality.connectionEvent (0, 0) (diagonalSite n) =
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} := by
      ext ω
      simp [Duality.connectionEvent, Duality.cluster]
    simp only [Duality.twoPoint, Measure.real_def]
    rw [← hevent]
    rfl
  exact ⟨
    (Duality.critical_discontinuity_of_pos_diagonal_rate qR φ₀.toMeasure φ₁.toMeasure
      hφ₀' hφ₁' L hL hrate').1,
    (Duality.critical_discontinuity_of_pos_diagonal_rate qR φ₀.toMeasure φ₁.toMeasure
      hφ₀' hφ₁' L hL hrate').2.1⟩

end PottsDiscontinuity.PottsThm
