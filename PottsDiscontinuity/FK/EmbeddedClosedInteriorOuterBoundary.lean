/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.FK.ComponentBoundarySupport
public import PottsDiscontinuity.FK.IsolatedBoundaryComponents
public import PottsDiscontinuity.FK.SubgraphComparison

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

private theorem removedEdge_endpoint_not_image_compl_general
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    (_hGH : G.map f ≤ H) (B : Set V)
    (hclosed : ∀ ⦃x : V⦄, x ∉ B → ∀ ⦃y : W⦄, H.Adj (f x) y →
      ∃ z : V, f z = y ∧ G.Adj x z)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
    ∀ ⦃e : H.edgeSet⦄, e ∈ K.val → ∀ ⦃w : W⦄, w ∈ e.1 →
      w ∉ f '' Bᶜ := by
  classical
  intro e he w hw himage
  rcases himage with ⟨x, hxB, hfx⟩
  have hnot : e.1 ∉ (G.map f).edgeSet :=
    (mem_subgraphRemovedEdges e).mp (K.property he)
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.1
  have heval : e.1 = Sym2.mk a b := by simpa using hab.symm
  have habAdj : H.Adj a b := by
    apply H.mem_edgeSet.mp
    rw [← heval]
    exact e.2
  have hwAB : w = a ∨ w = b := by
    rw [heval] at hw
    exact (Sym2.mem_iff').mp hw
  rcases hwAB with hwa | hwb
  · have hxa : f x = a := hfx.trans hwa
    obtain ⟨z, hzb, hxz⟩ := hclosed hxB (by simpa [hxa] using habAdj)
    have hmapAdj : (G.map f).Adj (f x) (f z) :=
      (SimpleGraph.map_adj _ _ _ _).mpr ⟨x, z, hxz, rfl, rfl⟩
    have he' : e.1 = Sym2.mk (f x) (f z) := by
      calc
        e.1 = Sym2.mk a b := heval
        _ = Sym2.mk (f x) (f z) := by rw [← hxa, ← hzb]
    apply hnot
    rw [he']
    exact (G.map f).mem_edgeSet.mpr hmapAdj
  · have hxb : f x = b := hfx.trans hwb
    obtain ⟨z, hza, hxz⟩ := hclosed hxB (by simpa [hxb] using habAdj.symm)
    have hmapAdj : (G.map f).Adj (f x) (f z) :=
      (SimpleGraph.map_adj _ _ _ _).mpr ⟨x, z, hxz, rfl, rfl⟩
    have he' : e.1 = Sym2.mk (f x) (f z) := by
      calc
        e.1 = Sym2.mk a b := heval
        _ = Sym2.mk (f x) (f z) := by
          apply Sym2.eq_iff.mpr
          exact Or.inr ⟨hza.symm, hxb.symm⟩
    apply hnot
    rw [he']
    exact (G.map f).mem_edgeSet.mpr hmapAdj

/-- Frozen configurations in an exterior region pull back to a partition
finer than the partition wiring `B`, for any outer boundary whose boundary
points avoid the embedded complement of `B`. Neighbor closure ensures frozen
removed edges cannot identify a point in that complement. -/
theorem isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    (hGH : G.map f ≤ H) (B : Set V)
    (hclosed : ∀ ⦃x : V⦄, x ∉ B → ∀ ⦃y : W⦄, H.Adj (f x) y →
      ∃ z : V, f z = y ∧ G.Adj x z)
    (ξ : BoundaryCondition W)
    (hξavoid : ∀ ⦃x : V⦄, x ∉ B → f x ∉ ξ.boundary)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤
      (BoundaryCondition.wired B).partition := by
  classical
  let D : Set W := (f '' Bᶜ)ᶜ
  have hcomp : componentSetoid H ξ K.val ≤
      (BoundaryCondition.wired (ξ.boundary ∪ D)).partition :=
    componentSetoid_le_wired_union_of_edge_endpoints ξ D K.val (by
      intro e he w hw
      exact removedEdge_endpoint_not_image_compl_general f hGH B hclosed K he hw)
  intro x y hxy
  have houter : (componentSetoid H ξ K.val).r (f x) (f y) :=
    (Setoid.comap_rel f (frozenBoundary ξ K.val).partition x y).mp hxy
  have hbig : (BoundaryCondition.wired (ξ.boundary ∪ D)).partition.r
      (f x) (f y) := hcomp houter
  rcases (BoundaryCondition.wired_rel (ξ.boundary ∪ D) (f x) (f y)).mp hbig with
    heq | ⟨hx, hy⟩
  · exact (BoundaryCondition.wired_rel B x y).mpr (Or.inl (f.injective heq))
  · have hxB : x ∈ B := by
      by_contra hxB
      rcases hx with hξ | hD
      · exact False.elim (hξavoid hxB hξ)
      · exact hD ⟨x, hxB, rfl⟩
    have hyB : y ∈ B := by
      by_contra hyB
      rcases hy with hξ | hD
      · exact False.elim (hξavoid hyB hξ)
      · exact hD ⟨y, hyB, rfl⟩
    exact (BoundaryCondition.wired_rel B x y).mpr (Or.inr ⟨hxB, hyB⟩)

end
end PottsDiscontinuity.FK
