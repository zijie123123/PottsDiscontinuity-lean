module

public import PottsDiscontinuity.Duality.ZeroOne
public import PottsDiscontinuity.RCInfinite.PercolationZeroOne

/-! The proved zero–one law for infinite-volume random-cluster measures
(`RCInfinite/PercolationZeroOne.lean`), on the exact cluster events of the planar-duality
library (`Duality/`). -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK MeasureTheory

lemma infiniteClusterAt_eq_infiniteAt (v : LatticeVertex) :
    infiniteClusterAt v = RCInfinite.infiniteAt v := rfl

lemma existsInfiniteCluster_eq_infiniteClusterEvent :
    existsInfiniteCluster = RCInfinite.infiniteClusterEvent := rfl

/-- The zero–one input is now discharged for every frozen free or wired limit. -/
theorem existsInfiniteCluster_zero_one (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) :
    μ existsInfiniteCluster = 0 ∨ μ existsInfiniteCluster = 1 :=
  RCInfinite.infiniteCluster_zero_one θ.toP θ.toQ θ.property i μ hμ

/-- Positive origin percolation implies almost-sure existence, with no ergodicity premise. -/
theorem existsInfiniteCluster_eq_one_of_origin_pos (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (hpos : 0 < μ (infiniteClusterAt 0)) : μ existsInfiniteCluster = 1 :=
  existsInfiniteCluster_eq_one_of_zero_one μ 0 hpos (existsInfiniteCluster_zero_one θ i μ hμ)

/-- Positivity for the existence event is equivalent to positivity at the origin. -/
theorem existsInfiniteCluster_pos_iff_origin_pos (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) :
    0 < μ existsInfiniteCluster ↔ 0 < μ (infiniteClusterAt 0) :=
  RCInfinite.infiniteCluster_pos_iff_origin_pos θ.toP θ.toQ θ.property i μ hμ

end PottsDiscontinuity.Duality
