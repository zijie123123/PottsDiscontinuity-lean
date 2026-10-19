/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceBoundaryGraph
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFacePivotGeometry
public import PottsDiscontinuity.TorusTopology.PlanarFiniteEvenTriangularElimination
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph
open scoped symmDiff

@[instance_reducible] noncomputable def coverChainLocallyFiniteOfFintype {V : Type*} [Fintype V]
    (G : SimpleGraph V) : LocallyFinite G := fun v =>
  Fintype.ofInjective (fun x : G.neighborSet v => x.1) Subtype.val_injective

private theorem coverFiniteFacePivot_boundary_classification {n : ℕ}
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (hij : parafermionicCoverFiniteFaceTopPivot n j ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet) :
    j = i ∨ parafermionicCoverFiniteFaceTopRank n j <
      parafermionicCoverFiniteFaceTopRank n i := by
  have hraw := Set.mem_image_of_mem (Sym2.map Subtype.val) hij
  rw [parafermionicCoverFiniteFaceBoundaryGraph_actualEdgeSet] at hraw
  rw [parafermionicCoverFiniteFaceTopPivot_map] at hraw
  change parafermionicCoverFiniteFaceTopEdge j.1 ∈
    {parafermionicCoverFiniteFaceBottomEdge i.1,
     parafermionicCoverFiniteFaceRightEdge i.1,
     parafermionicCoverFiniteFaceTopEdge i.1,
     parafermionicCoverFiniteFaceLeftEdge i.1} at hraw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hraw
  rcases hraw with hbottom | hright | htop | hleft
  · have hheight : j.1.1.2 < i.1.1.2 := by
      by_contra hnot
      have hle : i.1.1.2 ≤ j.1.1.2 := by omega
      exact (parafermionicCoverFiniteFaceBottomEdge_ne_topEdge_of_height_le
        i.2 j.2 hle) hbottom.symm
    exact Or.inr (parafermionicCoverFiniteFaceTopRank_strict_height n hheight)
  · exact False.elim ((parafermionicCoverFiniteFaceRightEdge_ne_topEdge
      i.2 j.2) hright.symm)
  · exact Or.inl (Subtype.ext (parafermionicCoverFiniteFaceTopEdge_injective
      n j.2 i.2 htop))
  · exact False.elim ((parafermionicCoverFiniteFaceLeftEdge_ne_topEdge
      i.2 j.2) hleft.symm)

theorem parafermionicCoverFiniteFaceChainDecomposition {n : ℕ} (hn : 1 ≤ n)
    (H : SimpleGraph (ParafermionicCoverBoxVertex n))
    (hle : H ≤ parafermionicCoverBoxGraph n)
    (hHeven : ∀ v, Even (H.neighborSet v).ncard) :
    ∃ L : List (ParafermionicCoverFiniteFaceTopIndex n),
      L.Nodup ∧
      faceSymmDiffList
        (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L = H := by
  classical
  let : Fintype (ParafermionicCoverBoxVertex n) := Fintype.ofFinite _
  let : Fintype (ParafermionicCoverFiniteFaceTopIndex n) := Fintype.ofFinite _
  let : LocallyFinite (parafermionicCoverBoxGraph n) :=
    coverChainLocallyFiniteOfFintype (parafermionicCoverBoxGraph n)
  let : LocallyFinite H := coverChainLocallyFiniteOfFintype H
  let F : ParafermionicCoverFiniteFaceTopIndex n →
      SimpleGraph (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2
  let : ∀ i, LocallyFinite (F i) := fun i => coverChainLocallyFiniteOfFintype (F i)
  let p : ParafermionicCoverFiniteFaceTopIndex n →
      Sym2 (ParafermionicCoverBoxVertex n) :=
    parafermionicCoverFiniteFaceTopPivot n
  let rank : ParafermionicCoverFiniteFaceTopIndex n → ℕ :=
    parafermionicCoverFiniteFaceTopRank n
  have hFle : ∀ i, F i ≤ parafermionicCoverBoxGraph n := by
    intro i
    exact parafermionicCoverFiniteFaceBoundaryGraph_le_boxGraph i.1 i.2
  have hFeven : ∀ i v, Even ((F i).degree v) := by
    intro i v
    have he := parafermionicCoverFiniteFaceBoundaryGraph_even_degree i.1 i.2 v
    simpa only [F, parafermionicCoverFiniteFaceBoundaryDegree,
      SimpleGraph.ncard_neighborSet] using he
  have hpG : ∀ i, p i ∈ (parafermionicCoverBoxGraph n).edgeSet := by
    intro i
    exact parafermionicCoverFiniteFaceTopPivot_mem_edgeSet n i
  have hpF : ∀ i, p i ∈ (F i).edgeSet := by
    intro i
    have hmem := parafermionicCoverFiniteFaceTopEdgeBox_mem_boundaryGraph i.1 i.2
    have heq : parafermionicCoverFiniteFaceTopEdgeBox i.1 i.2 = p i := by
      simp [p, parafermionicCoverFiniteFaceTopPivot,
        parafermionicCoverFiniteFaceTopEdgeBox]
    simpa [F, heq] using hmem
  have hpInj : Function.Injective p := by
    exact parafermionicCoverFiniteFaceTopPivot_injective n
  have htri : ∀ i j, p j ∈ (F i).edgeSet → j = i ∨ rank j < rank i := by
    intro i j h
    exact coverFiniteFacePivot_boundary_classification i j (by simpa [F, p] using h)
  have hacyclic :
      ((parafermionicCoverBoxGraph n).deleteEdges (Set.range p)).IsAcyclic := by
    simpa [p] using parafermionicCoverBoxGraph_deleteTopPivots_isAcyclic n hn
  have hHevenDegree : ∀ v, Even (H.degree v) := by
    intro v
    simpa only [SimpleGraph.ncard_neighborSet] using hHeven v
  exact exists_faceSymmDiffList_of_even_subgraph
    (parafermionicCoverBoxGraph n) F p rank
    hFle hFeven hpF htri hacyclic H hle hHevenDegree

end PottsDiscontinuity.TorusTopology.Planar.Medial
