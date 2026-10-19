/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarFiniteCompassFan
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedCornerCoefficient
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedCornerNeighbors

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

/-- Away from the support of the actual selected boundary graph, every
oriented boundary coefficient based at the vertex vanishes. -/
theorem parafermionicCoverFiniteFaceSetBoundaryCoefficient_eq_zero_of_not_support
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v w : ParafermionicCoverBoxVertex n)
    (hv : v ∉ (parafermionicCoverFiniteFaceSetBoundaryGraph S).support) :
    parafermionicCoverFaceBoundaryCoefficient S v w = 0 := by
  by_contra hcoeff
  have hedge :=
    (parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff S v w).mp
      hcoeff
  have hadj : (parafermionicCoverFiniteFaceSetBoundaryGraph S).Adj v w := by
    simpa only [SimpleGraph.mem_edgeSet] using hedge
  exact hv ((parafermionicCoverFiniteFaceSetBoundaryGraph S).mem_support.mpr
    ⟨w, hadj⟩)

/-- At a vertex outside the selected boundary support, each compass-sector
boundary is zero. Existing face incidence supplies both compass neighbors
when they are in the box; outside neighbors exclude the corresponding actual
selected corners. -/
theorem parafermionicCoverFiniteFaceSelectedCorners_sectorBoundary_eq_zero_of_not_support
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n)
    (hv : v ∉ (parafermionicCoverFiniteFaceSetBoundaryGraph S).support)
    (d : Fin 4) :
    compassSectorBoundary (parafermionicCoverFiniteFaceSelectedCorners S v) d = 0 := by
  by_cases hneighbor : parafermionicCoverCompassNeighbor v.1 d ∈
      parafermionicCoverBoxVertices n
  · let w : ParafermionicCoverBoxVertex n :=
      ⟨parafermionicCoverCompassNeighbor v.1 d, hneighbor⟩
    have hcoeff :=
      parafermionicCoverFiniteFaceSetBoundaryCoefficient_eq_zero_of_not_support
        S v w hv
    have hformula :=
      parafermionicCoverFaceBoundaryCoefficient_eq_selectedCornerIndicators
        S v w d rfl
    rw [hcoeff] at hformula
    simpa [compassSectorBoundary] using hformula.symm
  · have hmissing :=
      parafermionicCoverFiniteFaceSelectedCorners_missing_of_outside_neighbor
        S v d hneighbor
    simp [compassSectorBoundary, hmissing.1, hmissing.2]

/-- Every actual selected corner is present at an original-union vertex away
from the selected boundary support. -/
theorem parafermionicCoverFiniteFaceSelectedCorners_eq_univ_of_mem_unionCarrier_not_support
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n)
    (hvcar : v ∈ parafermionicCoverFiniteFaceUnionCarrier S)
    (hvsupp : v ∉ (parafermionicCoverFiniteFaceSetBoundaryGraph S).support) :
    parafermionicCoverFiniteFaceSelectedCorners S v = Finset.univ ∧
      (parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card = 4 := by
  have hzero : ∀ d : Fin 4,
      compassSectorBoundary (parafermionicCoverFiniteFaceSelectedCorners S v) d = 0 :=
    fun d => parafermionicCoverFiniteFaceSelectedCorners_sectorBoundary_eq_zero_of_not_support
      S v hvsupp d
  have hempty_or_univ := compassSectorBoundary_zero_eq_empty_or_univ
    (parafermionicCoverFiniteFaceSelectedCorners S v) hzero
  have hnonempty :
      (parafermionicCoverFiniteFaceSelectedCorners S v).Nonempty :=
    (parafermionicCoverFiniteFaceSelectedCorners_nonempty_iff_unionCarrier S v).2 hvcar
  rcases hempty_or_univ with hempty | huniv
  · exact False.elim ((Finset.nonempty_iff_ne_empty.mp hnonempty) hempty)
  · constructor
    · exact huniv
    · rw [← parafermionicCoverFiniteFaceSelectedCorners_card, huniv]
      simp

end PottsDiscontinuity.TorusTopology.Planar.Medial
