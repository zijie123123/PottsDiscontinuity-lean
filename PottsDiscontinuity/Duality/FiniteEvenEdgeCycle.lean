/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.FiniteGraphBoundaryParity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.FK

open SimpleGraph

/-- Every edge of a finite even-degree graph lies on a genuine simple cycle. -/
theorem edge_mem_some_isCycle_of_even_degree
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (heven : ∀ x : V, Even (G.degree x)) {u w : V} (huw : G.Adj u w) :
    ∃ (z : V) (p : G.Walk z z), p.IsCycle ∧ s(u,w) ∈ p.edges := by
  classical
  have hne : u ≠ w := G.ne_of_adj huw
  let H := G.deleteEdges {s(u,w)}
  have hNFu : H.neighborFinset u = G.neighborFinset u \ {w} := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff, Finset.mem_singleton]
    rw [SimpleGraph.deleteEdges_adj]
    constructor
    · rintro ⟨hux, hnot⟩
      refine ⟨hux, ?_⟩
      intro hx
      apply hnot
      simp [hx]
    · rintro ⟨hux, hxw⟩
      refine ⟨hux, ?_⟩
      intro heq
      apply hxw
      have hpair := Sym2.eq_iff.mp heq
      rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact h2
      · exact (hne h1).elim
  have hNFw : H.neighborFinset w = G.neighborFinset w \ {u} := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff, Finset.mem_singleton]
    rw [SimpleGraph.deleteEdges_adj]
    constructor
    · rintro ⟨hwx, hnot⟩
      refine ⟨hwx, ?_⟩
      intro hx
      apply hnot
      simp [hx, Sym2.eq_swap]
    · rintro ⟨hwx, hxu⟩
      refine ⟨hwx, ?_⟩
      intro heq
      apply hxu
      have hpair := Sym2.eq_iff.mp heq
      rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact (hxu (h2.trans h1)).elim
      · exact (hxu h2).elim
  have hNFother (x : V) (hxU : x ≠ u) (hxW : x ≠ w) :
      H.neighborFinset x = G.neighborFinset x := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset]
    rw [SimpleGraph.deleteEdges_adj]
    constructor
    · rintro ⟨hxy, _⟩
      exact hxy
    · intro hxy
      refine ⟨hxy, ?_⟩
      intro heq
      have hpair := Sym2.eq_iff.mp heq
      rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact hxU h1
      · exact hxW h1
  have hdegU : H.degree u = G.degree u - 1 := by
    calc
      H.degree u = (H.neighborFinset u).card := by rw [SimpleGraph.card_neighborFinset_eq_degree]
      _ = (G.neighborFinset u \ {w}).card := by rw [hNFu]
      _ = (G.neighborFinset u).card - 1 := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem
          ((G.mem_neighborFinset u w).mpr huw)]
      _ = G.degree u - 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
  have hdegW : H.degree w = G.degree w - 1 := by
    calc
      H.degree w = (H.neighborFinset w).card := by rw [SimpleGraph.card_neighborFinset_eq_degree]
      _ = (G.neighborFinset w \ {u}).card := by rw [hNFw]
      _ = (G.neighborFinset w).card - 1 := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem
          ((G.mem_neighborFinset w u).mpr huw.symm)]
      _ = G.degree w - 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
  have hodd : Odd (∑ x ∈ ({u} : Finset V), H.degree x) := by
    simp only [Finset.sum_singleton]
    rw [hdegU]
    obtain ⟨k,hk⟩ := heven u
    have hv : w ∈ G.neighborFinset u := (G.mem_neighborFinset u w).mpr huw
    have hkpos : 0 < k := by
      have hpos : 0 < G.degree u := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨w,hv⟩
      omega
    refine ⟨k-1, ?_⟩
    omega
  have hevenOther : ∀ x, x ∉ ({u} ∪ {w} : Finset V) → Even (H.degree x) := by
    intro x hx
    have hx' : x ≠ u ∧ x ≠ w := by simpa using hx
    have hxU := hx'.1
    have hxW := hx'.2
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hNFother x hxU hxW,
      SimpleGraph.card_neighborFinset_eq_degree]
    exact heven x
  have hdisj : Disjoint ({u} : Finset V) {w} := by
    apply Finset.disjoint_left.mpr
    intro x hxU hxW
    have hxu : x = u := by simpa using hxU
    have hxw : x = w := by simpa using hxW
    exact hne (hxu.symm.trans hxw)
  have hreach := exists_reachable_between_of_odd_degree_sum H {u} {w}
    hdisj hevenOther hodd
  obtain ⟨x,hx,y,hy,hxy⟩ := hreach
  have hxu : x = u := by simpa using hx
  have hyw : y = w := by simpa using hy
  subst x
  subst y
  have hxy' : H.Reachable u w := hxy
  exact (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle).mp ⟨huw,hxy'⟩

end PottsDiscontinuity.FK
