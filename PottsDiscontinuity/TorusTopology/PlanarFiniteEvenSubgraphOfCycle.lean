/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph

/-- An even-degree subgraph of the spanning graph of a finite simple cycle is
empty or the whole cycle. -/
theorem evenSubgraphOfCycle_eq_bot_or_cycle
    {V : Type*} [Finite V] {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (hp : p.IsCycle) (H : SimpleGraph V)
    (hsub : H ≤ p.toSubgraph.spanningCoe)
    (heven : ∀ v : V, Even (H.neighborSet v).ncard) :
    H = ⊥ ∨ H = p.toSubgraph.spanningCoe := by
  classical
  let C := p.toSubgraph.spanningCoe
  have hneighborC (v : V) : C.neighborSet v = p.toSubgraph.neighborSet v := by
    ext w
    rfl
  have hfull_of_neighbor (v : V) (hv : v ∈ p.support)
      (hnon : (H.neighborSet v).Nonempty) :
      H.neighborSet v = C.neighborSet v := by
    have hsubN : H.neighborSet v ⊆ C.neighborSet v := SimpleGraph.neighborSet_mono hsub v
    have hCcard : (C.neighborSet v).ncard = 2 := by
      rw [hneighborC]
      exact hp.ncard_neighborSet_toSubgraph_eq_two hv
    have hle : (H.neighborSet v).ncard ≤ 2 := by
      calc
        (H.neighborSet v).ncard ≤ (C.neighborSet v).ncard := Set.ncard_le_ncard hsubN
        _ = 2 := hCcard
    have hpos : 0 < (H.neighborSet v).ncard := (Set.ncard_pos (Set.toFinite _)).mpr hnon
    have hHcard : (H.neighborSet v).ncard = 2 := by
      obtain ⟨k, hk⟩ := heven v
      omega
    apply Set.eq_of_subset_of_ncard_le hsubN
    rw [hCcard, hHcard]
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  · obtain ⟨a, b, hab⟩ := (SimpleGraph.ne_bot_iff_exists_adj).mp hbot
    have habC : C.Adj a b := hsub hab
    have haV : a ∈ p.toSubgraph.verts := p.toSubgraph.edge_vert habC
    have haSupport : a ∈ p.support := p.mem_verts_toSubgraph.mp haV
    have hstart : H.neighborSet a = C.neighborSet a :=
      hfull_of_neighbor a haSupport ⟨b, (H.mem_neighborSet a b).mpr hab⟩
    have hprop : ∀ {x y : p.toSubgraph.verts}
        (w : p.toSubgraph.coe.Walk x y),
        H.neighborSet x.1 = C.neighborSet x.1 →
          H.neighborSet y.1 = C.neighborSet y.1 := by
      intro x y w
      induction w with
      | nil => intro hx; exact hx
      | @cons x y z hadj tail ih =>
          intro hx
          have hadjC : C.Adj x.1 y.1 := hadj
          have hyC : y.1 ∈ C.neighborSet x.1 := (C.mem_neighborSet x.1 y.1).mpr hadjC
          have hyH : y.1 ∈ H.neighborSet x.1 := by simpa [hx] using hyC
          have hadjH : H.Adj x.1 y.1 := (H.mem_neighborSet x.1 y.1).mp hyH
          have hxH : x.1 ∈ H.neighborSet y.1 :=
            (H.mem_neighborSet y.1 x.1).mpr (hadjH.symm)
          have hySupport : y.1 ∈ p.support :=
            p.mem_verts_toSubgraph.mp y.2
          have hnext : H.neighborSet y.1 = C.neighborSet y.1 :=
            hfull_of_neighbor y.1 hySupport ⟨x.1, hxH⟩
          exact ih hnext
    have hfull : ∀ v : V, v ∈ p.support →
        H.neighborSet v = C.neighborSet v := by
      intro v hv
      let av : p.toSubgraph.verts := ⟨a, haV⟩
      let vv : p.toSubgraph.verts := ⟨v, p.mem_verts_toSubgraph.mpr hv⟩
      have hreach : p.toSubgraph.coe.Reachable av vv :=
        p.toSubgraph_connected av vv
      rcases hreach with ⟨w⟩
      exact hprop w hstart
    apply Or.inr
    apply le_antisymm hsub
    intro x y hxy
    have hxV : x ∈ p.toSubgraph.verts := p.toSubgraph.edge_vert hxy
    have hxSupport : x ∈ p.support := p.mem_verts_toSubgraph.mp hxV
    have hfullx := hfull x hxSupport
    have hyC : y ∈ C.neighborSet x := (C.mem_neighborSet x y).mpr hxy
    have hyH : y ∈ H.neighborSet x := by simpa [hfullx] using hyC
    exact (H.mem_neighborSet x y).mp hyH

end PottsDiscontinuity.TorusTopology.Planar.Medial
