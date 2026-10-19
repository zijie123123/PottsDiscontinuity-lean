/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceBoundaryGraph
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFacePivotGeometry
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

private theorem reachable_of_sym2_pair_eq {V : Type*} (G : SimpleGraph V)
    {e : Sym2 V} {x y : V} (he : e = s(x,y))
    (h : G.Reachable x y) : G.Reachable e.out.1 e.out.2 := by
  have hout : s(e.out.1,e.out.2) = s(x,y) := by
    rw [Sym2.mk, e.out_eq, he]
  rcases Sym2.eq_iff.mp hout with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · simpa [h₁,h₂] using h
  · simpa [h₁,h₂] using h.symm

/-- The three nonpivot sides of an actual retained lifted face connect the
endpoints of its top pivot after deleting that pivot alone. -/
theorem parafermionicCoverFiniteFaceTopPivot_bypass {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    ((parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).deleteEdges
      {parafermionicCoverFiniteFaceTopPivot n i}).Reachable
        (parafermionicCoverFiniteFaceTopPivot n i).out.1
        (parafermionicCoverFiniteFaceTopPivot n i).out.2 := by
  classical
  let f := i.1
  let hf := i.2
  let b0 : ParafermionicCoverBoxVertex n :=
    ⟨f, (parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
      (e := (f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2))
      (by simp [parafermionicCoverFiniteFaceDarts])).1⟩
  let b1 : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
      (parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
        (e := (f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2))
        (by simp [parafermionicCoverFiniteFaceDarts])).2⟩
  let b2 : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1⟩
  let b3 : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2⟩
  let G := parafermionicCoverFiniteFaceBoundaryGraph f hf
  let p := parafermionicCoverFiniteFaceTopPivot n i
  have hp : p = s(b2,b3) := by
    simp [p, parafermionicCoverFiniteFaceTopPivot, b2, b3, f]
  have hmapRight : Sym2.map Subtype.val (s(b1,b2)) =
      parafermionicCoverFiniteFaceRightEdge f := by
    simp [b1, b2, parafermionicCoverFiniteFaceRightEdge, Sym2.map_mk]
  have hmapBottom : Sym2.map Subtype.val (s(b0,b1)) =
      parafermionicCoverFiniteFaceBottomEdge f := by
    simp [b0, b1, parafermionicCoverFiniteFaceBottomEdge, Sym2.map_mk]
  have hmapLeft : Sym2.map Subtype.val (s(b3,b0)) =
      parafermionicCoverFiniteFaceLeftEdge f := by
    simp [b0, b3, parafermionicCoverFiniteFaceLeftEdge, Sym2.map_mk]
  have hEdgeOfRaw (e : Sym2 (ParafermionicCoverBoxVertex n))
      (he : Sym2.map Subtype.val e ∈
        ({parafermionicCoverFiniteFaceBottomEdge f,
         parafermionicCoverFiniteFaceRightEdge f,
         parafermionicCoverFiniteFaceTopEdge f,
         parafermionicCoverFiniteFaceLeftEdge f} :
          Set (Sym2 ParafermionicCoverVertex))) : e ∈ G.edgeSet := by
    have himg : Sym2.map Subtype.val e ∈
        Sym2.map Subtype.val '' G.edgeSet := by
      rw [parafermionicCoverFiniteFaceBoundaryGraph_actualEdgeSet]
      exact he
    rcases (Set.mem_image _ _ _).mp himg with ⟨e', he', heq⟩
    have heq' : e' = e := Sym2.map.injective Subtype.val_injective heq
    simpa [heq'] using he'
  have hright : G.Adj b1 b2 := by
    apply (SimpleGraph.mem_edgeSet G).mp
    apply hEdgeOfRaw
    rw [hmapRight]
    simp
  have hbottom : G.Adj b0 b1 := by
    apply (SimpleGraph.mem_edgeSet G).mp
    apply hEdgeOfRaw
    rw [hmapBottom]
    simp
  have hleft : G.Adj b3 b0 := by
    apply (SimpleGraph.mem_edgeSet G).mp
    apply hEdgeOfRaw
    rw [hmapLeft]
    simp
  have hright_ne : s(b1,b2) ≠ p := by
    intro he
    have hm := (hmapRight.symm.trans (congrArg (Sym2.map Subtype.val) he)).trans
      (parafermionicCoverFiniteFaceTopPivot_map n i)
    have hraw : parafermionicCoverFiniteFaceRightEdge f =
        parafermionicCoverFiniteFaceTopEdge f := by simpa using hm
    exact parafermionicCoverFiniteFaceRightEdge_ne_topEdge hf hf hraw
  have hbottom_ne : s(b0,b1) ≠ p := by
    intro he
    have hm := (hmapBottom.symm.trans (congrArg (Sym2.map Subtype.val) he)).trans
      (parafermionicCoverFiniteFaceTopPivot_map n i)
    have hraw : parafermionicCoverFiniteFaceBottomEdge f =
        parafermionicCoverFiniteFaceTopEdge f := by simpa using hm
    exact parafermionicCoverFiniteFaceBottomEdge_ne_topEdge_of_height_le hf hf (le_rfl) hraw
  have hleft_ne : s(b3,b0) ≠ p := by
    intro he
    have hm := (hmapLeft.symm.trans (congrArg (Sym2.map Subtype.val) he)).trans
      (parafermionicCoverFiniteFaceTopPivot_map n i)
    have hraw : parafermionicCoverFiniteFaceLeftEdge f =
        parafermionicCoverFiniteFaceTopEdge f := by simpa using hm
    exact parafermionicCoverFiniteFaceLeftEdge_ne_topEdge hf hf hraw
  have hright' : (G.deleteEdges {p}).Adj b2 b1 := by
    apply (SimpleGraph.deleteEdges_adj).2
    have hne : s(b2,b1) ≠ p := by
      intro he
      apply hright_ne
      calc
        s(b1,b2) = s(b2,b1) := Sym2.eq_swap
        _ = p := he
    exact ⟨hright.symm, by simpa using hne⟩
  have hbottom' : (G.deleteEdges {p}).Adj b1 b0 := by
    apply (SimpleGraph.deleteEdges_adj).2
    have hne : s(b1,b0) ≠ p := by
      intro he
      apply hbottom_ne
      calc
        s(b0,b1) = s(b1,b0) := Sym2.eq_swap
        _ = p := he
    exact ⟨hbottom.symm, by simpa using hne⟩
  have hleft' : (G.deleteEdges {p}).Adj b0 b3 := by
    apply (SimpleGraph.deleteEdges_adj).2
    have hne : s(b0,b3) ≠ p := by
      intro he
      apply hleft_ne
      calc
        s(b3,b0) = s(b0,b3) := Sym2.eq_swap
        _ = p := he
    exact ⟨hleft.symm, by simpa using hne⟩
  have hwalk : (G.deleteEdges {p}).Walk b2 b3 :=
    Walk.cons hright' (Walk.cons hbottom' (Walk.cons hleft' Walk.nil))
  exact reachable_of_sym2_pair_eq (G.deleteEdges {p}) (e := p) (x := b2) (y := b3) hp hwalk.reachable

end PottsDiscontinuity.TorusTopology.Planar.Medial
