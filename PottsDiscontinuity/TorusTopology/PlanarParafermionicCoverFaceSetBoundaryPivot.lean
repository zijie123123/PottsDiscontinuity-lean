/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedFaceIncidence

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

/-- A maximal-height actual face contributes its own top pivot to the
symmetric-difference boundary of the selected actual face family. -/
theorem parafermionicCoverFiniteFaceSetBoundaryGraph_maximal_pivot_mem
    {n : ℕ} (T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (i : ParafermionicCoverFiniteFaceTopIndex n) (hi : i ∈ T)
    (hmax : ∀ j ∈ T,
      parafermionicCoverFiniteFaceTopRank n j ≤
        parafermionicCoverFiniteFaceTopRank n i) :
    parafermionicCoverFiniteFaceTopPivot n i ∈
      (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet := by
  classical
  let e := parafermionicCoverFiniteFaceTopPivot n i
  have hiEdge : e ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
    have hmem := parafermionicCoverFiniteFaceTopEdgeBox_mem_boundaryGraph i.1 i.2
    have heq : parafermionicCoverFiniteFaceTopEdgeBox i.1 i.2 = e := by
      simp [e, parafermionicCoverFiniteFaceTopPivot,
        parafermionicCoverFiniteFaceTopEdgeBox]
    simpa [heq] using hmem
  have hselected : i ∈ parafermionicCoverFiniteFaceSelectedIncidentFaces T e := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hi⟩
    simp only [parafermionicCoverFiniteFaceIncidentFaces, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hiEdge
  have hsubset :
      parafermionicCoverFiniteFaceSelectedIncidentFaces T e ⊆ {i} := by
    intro j hj
    have hjData : j ∈ T ∧ e ∈
        (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := by
      simpa [parafermionicCoverFiniteFaceSelectedIncidentFaces,
        parafermionicCoverFiniteFaceIncidentFaces, and_comm] using hj
    have hclass := parafermionicCoverFiniteFacePivot_boundary_classification j i
      (by simpa [e] using hjData.2)
    have hji : j = i := by
      rcases hclass with heq | hlt
      · exact heq.symm
      · exact False.elim ((not_lt_of_ge (hmax j hjData.1)) hlt)
    simp [hji]
  have hcard :
      (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card = 1 := by
    have hle := Finset.card_le_card hsubset
    have hpos : 0 <
        (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card :=
      Finset.card_pos.mpr ⟨i, hselected⟩
    simp only [Finset.card_singleton] at hle
    omega
  exact (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
    T e).2 hcard

/-- Every nonempty finite actual face family has a boundary edge equal to an
actual top pivot of one of its faces. -/
theorem parafermionicCoverFiniteFaceSetBoundaryGraph_exists_pivot
    {n : ℕ} (T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (hT : T.Nonempty) :
    ∃ i ∈ T, parafermionicCoverFiniteFaceTopPivot n i ∈
      (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet := by
  classical
  obtain ⟨i0, hi0⟩ := hT
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image T
    (parafermionicCoverFiniteFaceTopRank n) ⟨i0, hi0⟩
  exact ⟨i, hi,
    parafermionicCoverFiniteFaceSetBoundaryGraph_maximal_pivot_mem T i hi hmax⟩

end PottsDiscontinuity.TorusTopology.Planar.Medial
