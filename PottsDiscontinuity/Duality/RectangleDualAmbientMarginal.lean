/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleDualAmbient
public import PottsDiscontinuity.FK.SubgraphComparison

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

theorem rectangleDualAmbient_law_restrict_to_dual
    (a : LatticeVertex) (w h : ℕ) (q : Parameters) :
    (law (rectangleDualAmbientGraph a w h) q (rectangleDualBoundaryCondition a w h)).map
      (subgraphConfigurationRestriction (rectangleDualGraph_le_ambient a w h)) =
    law (rectangleDualGraph a w h) q (rectangleDualBoundaryCondition a w h) := by
  classical
  have hfiniteSet : (rectangleDualExpanded a w h : Set LatticeVertex).Finite :=
    Finset.finite_toSet _
  let rectangleDualAmbientVertexFinite : Finite (RectangleDualVertex a w h) := hfiniteSet
  let H := rectangleDualAmbientGraph a w h
  let G := rectangleDualGraph a w h
  let hGH : G ≤ H := rectangleDualGraph_le_ambient a w h
  let rectangleDualAmbientEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _
  let R := subgraphRemovedEdges G H
  have hR : ∀ (u v : RectangleDualVertex a w h) (huv : H.Adj u v),
      (⟨s(u, v), H.mem_edgeSet.mpr huv⟩ : H.edgeSet) ∈ R →
        (rectangleDualBoundaryCondition a w h).partition.r u v := by
    intro u v huv he
    rw [rectangleDualBoundaryCondition_rel]
    right
    have hnot : ¬ G.Adj u v := by
      intro hadj
      have hedge : s(u, v) ∈ G.edgeSet := G.mem_edgeSet.mpr hadj
      have hremoved := (mem_subgraphRemovedEdges (G := G) (H := H) _).mp he
      exact hremoved (by simpa using hedge)
    exact rectangleDualAmbient_extraEdge_endpoints_boundary a w h u v huv hnot
  have hremove := law_map_remove H q (rectangleDualBoundaryCondition a w h) R hR
  have hsubgraph := law_subgraphRemaining_map hGH q (rectangleDualBoundaryCondition a w h)
  calc
    (law H q (rectangleDualBoundaryCondition a w h)).map
        (subgraphConfigurationRestriction hGH) =
      ((law H q (rectangleDualBoundaryCondition a w h)).map
        (fun C => (configurationSplitEquiv H R C).1)).map
          ((subgraphRemainingConfigurationEquiv hGH).symm) := by
        rw [PMF.map_comp]
        congr 1
        funext C
        simpa only [Function.comp_apply, R] using
          (subgraphRemainingConfigurationEquiv_symm_split hGH C).symm
    _ = ((law G q (rectangleDualBoundaryCondition a w h)).map
        (subgraphRemainingConfigurationEquiv hGH)).map
          (subgraphRemainingConfigurationEquiv hGH).symm := by
        rw [hremove, hsubgraph]
    _ = law G q (rectangleDualBoundaryCondition a w h) := by
        rw [PMF.map_comp]
        have heq : ((subgraphRemainingConfigurationEquiv hGH).symm ∘
            subgraphRemainingConfigurationEquiv hGH) = id := by
          funext A
          exact Equiv.symm_apply_apply (subgraphRemainingConfigurationEquiv hGH) A
        rw [heq, PMF.map_id]

end

end PottsDiscontinuity.FK
