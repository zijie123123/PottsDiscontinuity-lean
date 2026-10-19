/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverPrimalCycleTurnSum
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleLocalTurning
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleBoundaryDefect
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open Classical

/-- The genuine primal quarter-turn sum of an actual named simple-cycle
filling is `4` or `-4`, according to its single actual orientation sign. -/
theorem parafermionicCoverPrimalCycleTurnSum_eq_four_or_neg_four
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    parafermionicCoverPrimalCycleTurnSum p hp = 4 ∨
      parafermionicCoverPrimalCycleTurnSum p hp = -4 := by
  obtain ⟨k, hk, hlocal⟩ := parafermionicCoverSimpleCycleLocalTurning hn p hp
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  have hturn :=
    parafermionicCoverPrimalCycleTurnSum_eq_support_sum_of_local_eq p hp
      (fun v => k * (2 -
        ((parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card : ℤ)))
      (by
        intro v hv
        simpa [S] using hlocal v hv)
  have hboundary := parafermionicCoverSimpleCycleFilling_boundary_defect hn p hp
  have hboundarySupport :
      Finset.sum p.support.toFinset (fun v => (2 : ℤ) -
        ((parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card : ℤ)) = 4 := by
    rw [← parafermionicCoverSimpleCycleFillingSet_boundarySupport_toFinset hn p hp]
    exact hboundary
  have htotal : parafermionicCoverPrimalCycleTurnSum p hp = k * 4 := by
    rw [hturn]
    calc
      Finset.sum p.support.toFinset (fun v =>
          k * (2 -
            ((parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card : ℤ))) =
        k * Finset.sum p.support.toFinset (fun v => (2 : ℤ) -
          ((parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card : ℤ)) := by
            rw [← Finset.mul_sum]
      _ = k * 4 := by rw [hboundarySupport]
  rcases hk with hk | hk
  · right
    simpa [hk] using htotal
  · left
    simpa [hk] using htotal

end PottsDiscontinuity.TorusTopology.Planar.Medial
