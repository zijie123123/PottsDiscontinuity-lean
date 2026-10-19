/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.FiniteEvenEdgeCycle
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.FK

open SimpleGraph

/-- In a graph with finite edge set and even degree at every vertex, every edge
lies on an actual simple cycle, even when the vertex type is infinite. -/
theorem edge_mem_some_isCycle_of_even_degree_of_finite_edgeSet
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfinite : G.edgeSet.Finite)
    (heven : ∀ x : V, Even (G.neighborSet x).ncard)
    {u w : V} (huw : G.Adj u w) :
    ∃ (z : V) (p : G.Walk z z), p.IsCycle ∧ s(u,w) ∈ p.edges := by
  classical
  let U : Set V := {x | ∃ e ∈ G.edgeSet, x ∈ e.toFinset}
  have hUfinite : U.Finite := by
    rw [show U = ⋃ e ∈ G.edgeSet, (e.toFinset : Set V) by
      ext x
      simp [U]]
    exact hfinite.biUnion fun e he => Finset.finite_toSet _
  let : Finite ↑U := hUfinite
  let : Fintype U := Fintype.ofFinite U
  let H : SimpleGraph U := G.induce U
  have hu : u ∈ U := by
    refine ⟨s(u,w), G.mem_edgeSet.mpr huw, ?_⟩
    simp
  have hw : w ∈ U := by
    refine ⟨s(u,w), G.mem_edgeSet.mpr huw, ?_⟩
    simp
  have hneighbors (x : V) (hx : x ∈ U) : G.neighborSet x ⊆ U := by
    intro y hy
    refine ⟨s(x,y), G.mem_edgeSet.mpr ((G.mem_neighborSet x y).mp hy), ?_⟩
    simp
  have hevenH : ∀ x : U, Even (H.degree x) := by
    intro x
    have hnc : (H.neighborSet x).ncard = (G.neighborSet x.1).ncard := by
      refine Set.ncard_congr (s := H.neighborSet x) (t := G.neighborSet x.1)
        (fun y hy => (y : V)) ?_ ?_ ?_
      · intro y hy
        exact (G.mem_neighborSet x.1 y.1).mpr ((H.mem_neighborSet x y).mp hy)
      · intro y z hy hz heq
        exact Subtype.ext heq
      · intro y hy
        have hyU : y ∈ U := hneighbors x.1 x.2 hy
        exact ⟨⟨y,hyU⟩, (G.mem_neighborSet x.1 y).mpr hy, rfl⟩
    rw [← H.ncard_neighborSet, hnc]
    exact heven x.1
  have hAdj : H.Adj ⟨u,hu⟩ ⟨w,hw⟩ := huw
  obtain ⟨z,q,hq,he⟩ := edge_mem_some_isCycle_of_even_degree H hevenH hAdj
  let f : H →g G := { toFun := Subtype.val, map_rel' := by intro a b h; exact h }
  let p := q.map f
  have hp : p.IsCycle := (q.isCycle_map_iff_of_injective Subtype.val_injective).mpr hq
  have he' : s(u,w) ∈ p.edges := by
    have hmap : p.edges = q.edges.map (Sym2.map f) := by
      change (q.map f).edges = q.edges.map (Sym2.map f)
      rw [Walk.edges_map]
    rw [hmap]
    exact List.mem_map.mpr ⟨s(⟨u,hu⟩,⟨w,hw⟩), he, by
      change Sym2.map (fun a : U => (a : V)) (s(⟨u,hu⟩,⟨w,hw⟩)) = s(u,w)
      simp⟩
  exact ⟨f z, p, hp, he'⟩

end PottsDiscontinuity.FK
