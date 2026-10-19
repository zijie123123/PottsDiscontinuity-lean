/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace/import relocation; the face cycle is chosen from unique existence, fixed by its complete ordered vertex list. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaceCycles
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceTopEdges
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

private theorem coverFace_box_mem (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    f ∈ parafermionicCoverBoxFinset n := by
  exact (Finset.mem_filter.mp hf).1

 theorem coverFace_base_mem (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    f ∈ parafermionicCoverBoxVertices n := by
  have h := parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
    (e := (f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)) (by simp [parafermionicCoverFiniteFaceDarts])
  exact h.1

 theorem existsUniqueFaceActualCycle {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    ∃! w : (parafermionicCoverBoxGraph n).Walk ⟨f, coverFace_base_mem n f hf⟩
        ⟨f, coverFace_base_mem n f hf⟩,
      w.IsCycle ∧ w.length = 4 ∧ w.support.map Subtype.val =
        [f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
          parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
          parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2, f] := by
  obtain ⟨w,hw⟩ := parafermionicCoverFiniteOrdinaryFace_has_cycle n f
    (coverFace_box_mem n f hf) hf
  refine ⟨w,hw,?_⟩
  intro q hq
  apply SimpleGraph.Walk.ext_support
  apply Function.Injective.list_map Subtype.val_injective
  exact hq.2.2.trans hw.2.2.symm

 noncomputable def coverFaceActualCycle {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    (parafermionicCoverBoxGraph n).Walk ⟨f, coverFace_base_mem n f hf⟩
      ⟨f, coverFace_base_mem n f hf⟩ :=
  Classical.choose (existsUniqueFaceActualCycle f hf).exists

private theorem coverFaceActualCycle_spec {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    (coverFaceActualCycle f hf).IsCycle ∧
      (coverFaceActualCycle f hf).length = 4 ∧
      (coverFaceActualCycle f hf).support.map Subtype.val =
        [f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
          parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
          parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2, f] :=
  by simpa only [coverFaceActualCycle] using Classical.choose_spec (existsUniqueFaceActualCycle f hf).exists

 def coverFaceB0 {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) : ParafermionicCoverBoxVertex n :=
  ⟨f, coverFace_base_mem n f hf⟩

 def coverFaceB1 {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) : ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
    (parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
      (e := (f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2))
      (by simp [parafermionicCoverFiniteFaceDarts])).2⟩

 def coverFaceB2 {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) : ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1⟩

 def coverFaceB3 {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) : ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2,
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2⟩

@[irreducible] noncomputable def parafermionicCoverFiniteFaceBoundaryGraph {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    SimpleGraph (ParafermionicCoverBoxVertex n) :=
  (coverFaceActualCycle f hf).toSubgraph.spanningCoe

theorem parafermionicCoverFiniteFaceBoundaryGraph_le_boxGraph {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    parafermionicCoverFiniteFaceBoundaryGraph f hf ≤ parafermionicCoverBoxGraph n :=
  by
    unfold parafermionicCoverFiniteFaceBoundaryGraph
    exact (coverFaceActualCycle f hf).toSubgraph.spanningCoe_le

theorem parafermionicCoverFiniteFaceBoundaryGraph_edgeSet {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    (parafermionicCoverFiniteFaceBoundaryGraph f hf).edgeSet =
      {s(coverFaceB0 f hf, coverFaceB1 f hf),
       s(coverFaceB1 f hf, coverFaceB2 f hf),
       s(coverFaceB2 f hf, coverFaceB3 f hf),
       s(coverFaceB3 f hf, coverFaceB0 f hf)} := by
  have hsup := coverFaceActualCycle_spec f hf
  have hs : (coverFaceActualCycle f hf).support =
      [coverFaceB0 f hf, coverFaceB1 f hf, coverFaceB2 f hf, coverFaceB3 f hf, coverFaceB0 f hf] := by
    apply Function.Injective.list_map Subtype.val_injective
    simpa [coverFaceB0, coverFaceB1, coverFaceB2, coverFaceB3] using hsup.2.2
  rw [parafermionicCoverFiniteFaceBoundaryGraph, SimpleGraph.Subgraph.edgeSet_spanningCoe,
    SimpleGraph.Walk.edgeSet_toSubgraph]
  change (fun e => e ∈ (coverFaceActualCycle f hf).edges) = _
  rw [SimpleGraph.Walk.edges_eq_zipWith_support, hs]
  ext e
  change e ∈ [s(coverFaceB0 f hf, coverFaceB1 f hf),
      s(coverFaceB1 f hf, coverFaceB2 f hf),
      s(coverFaceB2 f hf, coverFaceB3 f hf),
      s(coverFaceB3 f hf, coverFaceB0 f hf)] ↔
    e ∈ ({s(coverFaceB0 f hf, coverFaceB1 f hf),
      s(coverFaceB1 f hf, coverFaceB2 f hf),
      s(coverFaceB2 f hf, coverFaceB3 f hf),
      s(coverFaceB3 f hf, coverFaceB0 f hf)} : Set (Sym2 (ParafermionicCoverBoxVertex n)))
  simp only [List.mem_cons, List.not_mem_nil, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_false]

theorem parafermionicCoverFiniteFaceBoundaryGraph_actualEdgeSet {n : ℕ}
    (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    Sym2.map Subtype.val '' (parafermionicCoverFiniteFaceBoundaryGraph f hf).edgeSet =
      {parafermionicCoverFiniteFaceBottomEdge f,
       parafermionicCoverFiniteFaceRightEdge f,
       parafermionicCoverFiniteFaceTopEdge f,
       parafermionicCoverFiniteFaceLeftEdge f} := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  ext e
  simp [parafermionicCoverFiniteFaceBottomEdge,
    parafermionicCoverFiniteFaceRightEdge,
    parafermionicCoverFiniteFaceTopEdge,
    parafermionicCoverFiniteFaceLeftEdge,
    coverFaceB0, coverFaceB1, coverFaceB2, coverFaceB3,
    Sym2.map_mk]

def parafermionicCoverFiniteFaceTopEdgeBox {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    Sym2 (ParafermionicCoverBoxVertex n) :=
  s(⟨parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1⟩,
    ⟨parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2⟩)

theorem parafermionicCoverFiniteFaceTopEdgeBox_mem_boundaryGraph {n : ℕ}
    (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    parafermionicCoverFiniteFaceTopEdgeBox f hf ∈
      (parafermionicCoverFiniteFaceBoundaryGraph f hf).edgeSet := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  simp [parafermionicCoverFiniteFaceTopEdgeBox, coverFaceB2, coverFaceB3]

@[simp] theorem parafermionicCoverFiniteFaceTopEdgeBox_map {n : ℕ}
    (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    Sym2.map Subtype.val (parafermionicCoverFiniteFaceTopEdgeBox f hf) =
      parafermionicCoverFiniteFaceTopEdge f := by
  simp [parafermionicCoverFiniteFaceTopEdgeBox, parafermionicCoverFiniteFaceTopEdge,
    Sym2.map_mk]

@[irreducible] noncomputable def parafermionicCoverFiniteFaceBoundaryDegree {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (v : ParafermionicCoverBoxVertex n) : ℕ :=
  (parafermionicCoverFiniteFaceBoundaryGraph f hf).neighborSet v |>.ncard

private theorem eulerian_even_neighbor_ncard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u : V} (q : G.Walk u u)
    (hq : q.IsEulerian) (v : V) : Even (G.neighborSet v).ncard := by
  classical
  have hdegree : Even (G.degree v) :=
    (hq.even_degree_iff).2 (by intro huv; exact (huv rfl).elim)
  rw [← G.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] at hdegree
  exact hdegree

theorem parafermionicCoverFiniteFaceBoundaryGraph_even_degree {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    ∀ v : ParafermionicCoverBoxVertex n,
      Even (parafermionicCoverFiniteFaceBoundaryDegree f hf v) := by
  classical
  let : Fintype (ParafermionicCoverBoxVertex n) := inferInstance
  intro v
  unfold parafermionicCoverFiniteFaceBoundaryDegree
  let H := parafermionicCoverFiniteFaceBoundaryGraph f hf
  let w := coverFaceActualCycle f hf
  have hH : H = w.toSubgraph.spanningCoe := by
    change parafermionicCoverFiniteFaceBoundaryGraph f hf =
      (coverFaceActualCycle f hf).toSubgraph.spanningCoe
    unfold parafermionicCoverFiniteFaceBoundaryGraph
    rfl
  let : DecidableRel H.Adj := Classical.decRel _
  let q := w.transfer H (by
    intro e he
    rw [hH, SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.edgeSet_toSubgraph]
    exact he)
  have hqtrail : q.IsTrail := by
    simpa [q] using (coverFaceActualCycle_spec f hf).1.isTrail
  have hqedges : q.edgeSet = H.edgeSet := by
    change (w.transfer H _).edgeSet = H.edgeSet
    rw [SimpleGraph.Walk.edgeSet_transfer]
    rw [hH, SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.edgeSet_toSubgraph]
  have heuler : q.IsEulerian := hqtrail.isEulerian_iff.mpr hqedges
  let : DecidableRel H.Adj := Classical.decRel _
  exact eulerian_even_neighbor_ncard H q heuler v

end PottsDiscontinuity.TorusTopology.Planar.Medial
