/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetEdgeCount
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceUnionConnectivity

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

theorem parafermionicCoverSimpleCycleFillingSet_boundaryEdges_card_eq_length
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    (parafermionicCoverFiniteFaceSetBoundaryEdges
      (parafermionicCoverSimpleCycleFillingSet hn p hp)).card = p.length := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  have hB : parafermionicCoverFiniteFaceSetBoundaryGraph S =
      p.toSubgraph.spanningCoe :=
    parafermionicCoverSimpleCycleFillingSet_boundary_eq hn p hp
  have hEdgeSet : (parafermionicCoverFiniteFaceSetBoundaryGraph S).edgeSet =
      p.edgeSet := by
    rw [hB, SimpleGraph.Subgraph.edgeSet_spanningCoe,
      SimpleGraph.Walk.edgeSet_toSubgraph]
  have hfin : parafermionicCoverFiniteFaceSetBoundaryEdges S = p.edges.toFinset := by
    change (Finset.univ.filter fun e => e ∈
      (parafermionicCoverFiniteFaceSetBoundaryGraph S).edgeSet) = _
    ext e
    simp [hEdgeSet, SimpleGraph.Walk.edgeSet]
  rw [hfin, List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
    SimpleGraph.Walk.length_edges]


private theorem faceSetBoundaryGraph_le_unionGraph {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    parafermionicCoverFiniteFaceSetBoundaryGraph S ≤
      parafermionicCoverFiniteFaceUnionGraph S := by
  classical
  intro v w hadj
  have hcard :=
    (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
      S (s(v,w))).mp ((parafermionicCoverFiniteFaceSetBoundaryGraph S).mem_edgeSet.mpr hadj)
  have hpos : 0 < (parafermionicCoverFiniteFaceSelectedIncidentFaces S (s(v,w))).card := by
    rw [hcard]
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_filter.mp hi with ⟨hinc, hiS⟩
  rcases Finset.mem_filter.mp hinc with ⟨_, hiEdge⟩
  exact ⟨i, hiS,
    (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp hiEdge⟩

theorem parafermionicCoverSimpleCycleFillingSet_boundarySupport_subset_unionCarrier
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    (parafermionicCoverFiniteFaceSetBoundaryGraph
      (parafermionicCoverSimpleCycleFillingSet hn p hp)).support ⊆
      parafermionicCoverFiniteFaceUnionCarrier
        (parafermionicCoverSimpleCycleFillingSet hn p hp) := by
  intro v hv
  rcases hv with ⟨w, hvw⟩
  exact ⟨w, faceSetBoundaryGraph_le_unionGraph _ hvw⟩

theorem parafermionicCoverSimpleCycleFillingSet_boundarySupport_card_eq_length
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    Nat.card (parafermionicCoverFiniteFaceSetBoundaryGraph
      (parafermionicCoverSimpleCycleFillingSet hn p hp)).support = p.length := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let B := parafermionicCoverFiniteFaceSetBoundaryGraph S
  have hB : B = p.toSubgraph.spanningCoe :=
    parafermionicCoverSimpleCycleFillingSet_boundary_eq hn p hp
  have hsupport : B.support = {v | v ∈ p.support} := by
    ext v
    constructor
    · rintro ⟨w, hvw⟩
      have hvw' : p.toSubgraph.Adj v w := by
        simpa [hB, SimpleGraph.Subgraph.spanningCoe_adj] using hvw
      exact p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hvw')
    · intro hv
      rcases (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil).mp hv with
        ⟨e, he, hve⟩
      induction e using Sym2.inductionOn with
      | hf a b =>
          have hab : p.toSubgraph.Adj a b :=
            SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr he
          rcases Sym2.mem_iff.mp hve with hva | hvb
          · subst a
            exact ⟨b, by simpa [hB, SimpleGraph.Subgraph.spanningCoe_adj] using hab⟩
          · subst b
            exact ⟨a, by simpa [hB, SimpleGraph.Subgraph.spanningCoe_adj] using hab.symm⟩
  have htailLen : p.support.tail.length = p.length := by
    have hlen := p.length_support
    rw [← p.cons_tail_support] at hlen
    simp only [List.length_cons] at hlen
    omega
  have htailFin : p.support.tail.toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, htailLen]
  have huTail : u ∈ p.support.tail := p.end_mem_tail_support hp.not_nil
  have hsupportFin : p.support.toFinset = p.support.tail.toFinset := by
    calc
      p.support.toFinset = (u :: p.support.tail).toFinset :=
        congrArg List.toFinset p.cons_tail_support.symm
      _ = p.support.tail.toFinset := by
        rw [List.toFinset_cons]
        exact Finset.insert_eq_of_mem (List.mem_toFinset.mpr huTail)
  have hsupportSet : B.support = (p.support.toFinset : Set _) := by
    rw [hsupport]
    ext v
    simp
  have hcard : Nat.card p.support.toFinset = p.length := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hsupportFin, htailFin]
  rw [hsupportSet]
  change Nat.card p.support.toFinset = p.length
  exact hcard

end PottsDiscontinuity.TorusTopology.Planar.Medial
