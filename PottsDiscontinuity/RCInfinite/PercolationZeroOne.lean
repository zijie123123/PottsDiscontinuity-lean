module

public import PottsDiscontinuity.RCInfinite.ClusterEvents
public import PottsDiscontinuity.RCInfinite.ErgodicLimits

@[expose] public section

open MeasureTheory Set

namespace PottsDiscontinuity.RCInfinite
open FK

theorem infiniteAt_measure_eq_origin
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit p q i μ)
    (x : LatticeVertex) : μ (infiniteAt x) = μ (infiniteAt (0, 0)) := by
  have hpre : (edgeTranslate x) ⁻¹' infiniteAt x = infiniteAt (0, 0) := by
    simpa [latticeTranslate] using infiniteAt_preimage x (0, 0)
  have hmap := congrArg (fun ν : Measure LatticeConfiguration => ν (infiniteAt x))
    (translation_invariant p q hq i μ hμ x)
  rw [Measure.map_apply (edgeTranslate_measurable x) (measurableSet_infiniteAt x), hpre] at hmap
  exact hmap.symm

/-- Countable union and translation invariance identify positivity of the
existence event with positivity at the origin; uniqueness is not needed. -/
theorem infiniteCluster_pos_iff_origin_pos
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit p q i μ) :
    0 < μ infiniteClusterEvent ↔ 0 < μ (infiniteAt (0, 0)) := by
  constructor
  · intro hpos
    by_contra hn
    have hz : μ (infiniteAt (0, 0)) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hn)
    have hzero : μ infiniteClusterEvent = 0 := by
      rw [infiniteClusterEvent_eq_iUnion]
      apply measure_iUnion_null
      intro x
      rw [infiniteAt_measure_eq_origin p q hq i μ hμ x, hz]
    exact hpos.ne' hzero
  · intro hpos
    exact hpos.trans_le (measure_mono (by
      intro ω hω
      exact ⟨(0, 0), hω⟩))

theorem infiniteCluster_zero_one
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit p q i μ) :
    μ infiniteClusterEvent = 0 ∨ μ infiniteClusterEvent = 1 := by
  have : IsProbabilityMeasure μ := hμ.1
  exact (isRCInfiniteVolumeLimit_edge_ergodic p q hq i μ hμ).zero_one
    measurableSet_infiniteClusterEvent infiniteClusterEvent_invariant

/-- The infinite cluster exists almost surely exactly when the origin has a
positive probability of lying in an infinite cluster. -/
theorem infiniteCluster_eq_one_iff_origin_pos
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit p q i μ) :
    μ infiniteClusterEvent = 1 ↔ 0 < μ (infiniteAt (0, 0)) := by
  constructor
  · intro h
    apply (infiniteCluster_pos_iff_origin_pos p q hq i μ hμ).mp
    rw [h]
    exact zero_lt_one
  · intro h
    rcases infiniteCluster_zero_one p q hq i μ hμ with hz | ho
    · exact ((infiniteCluster_pos_iff_origin_pos p q hq i μ hμ).mpr h).ne' hz |>.elim
    · exact ho

end PottsDiscontinuity.RCInfinite
