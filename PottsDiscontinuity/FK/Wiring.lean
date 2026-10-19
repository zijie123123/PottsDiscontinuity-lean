/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.Graph

/-!
# Opening edges and boundary wiring

Opening additional edges can merge components but cannot split them. An edge
whose endpoints are already identified does not change the component relation
or the FK component count. In particular this applies to every edge with both
endpoints in one boundary block, as in the wired-edge convention on page 5.

These statements concern the component count. Actual paths still use only the
selected original graph edges, and can change when such an edge is inserted.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

variable {V : Type*} {G : SimpleGraph V}

theorem openGraph_mono {A B : Configuration G} (hAB : A ⊆ B) :
    openGraph G A ≤ openGraph G B := by
  intro u v h
  rw [openGraph_adj] at h ⊢
  rcases h with ⟨e, he, heuv⟩
  exact ⟨e, hAB he, heuv⟩

theorem actualConnected_mono {A B : Configuration G} (hAB : A ⊆ B) {u v : V}
    (h : ActualConnected G A u v) : ActualConnected G B u v :=
  h.mono (openGraph_mono hAB)

theorem componentSetoid_mono (ξ : BoundaryCondition V) {A B : Configuration G}
    (hAB : A ⊆ B) : componentSetoid G ξ A ≤ componentSetoid G ξ B := by
  apply componentSetoid_le
  · intro u v h
    exact actualConnected_component G ξ B (actualConnected_mono hAB h)
  · intro u v h
    exact boundary_component G ξ B h

/-- Adding open edges cannot increase the number of wired components. -/
theorem componentCount_antitone [Finite V] (ξ : BoundaryCondition V)
    {A B : Configuration G} (hAB : A ⊆ B) :
    componentCount G ξ B ≤ componentCount G ξ A := by
  let f : Quotient (componentSetoid G ξ A) → Quotient (componentSetoid G ξ B) :=
    Setoid.map_of_le (componentSetoid_mono ξ hAB)
  have hf : Function.Surjective f := by
    intro q
    refine Quotient.inductionOn q ?_
    intro v
    exact ⟨Quotient.mk _ v, rfl⟩
  exact Nat.card_le_card_of_surjective f hf

/-- A vertex equivalence containing every graph edge contains every open walk. -/
theorem reachableSetoid_le_of_adj (H : SimpleGraph V) (s : Setoid V)
    (hadj : ∀ {u v}, H.Adj u v → s.r u v) : H.reachableSetoid ≤ s := by
  intro u v h
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact s.refl _
  | cons h _ ih => exact s.trans (hadj h) ih

section Insertion

variable [DecidableEq G.edgeSet]

/-- Inserting an edge within an existing wired component changes no component. -/
theorem componentSetoid_insert_eq_of_related (ξ : BoundaryCondition V)
    (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (hrelated : (componentSetoid G ξ A).r u v) :
    componentSetoid G ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) =
      componentSetoid G ξ A := by
  apply le_antisymm
  · apply componentSetoid_le
    · apply reachableSetoid_le_of_adj
      intro x y hxy
      rw [openGraph_adj] at hxy
      rcases hxy with ⟨e, he, hexy⟩
      rcases Finset.mem_insert.mp he with he | he
      · subst e
        rcases Sym2.eq_iff.mp hexy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hrelated
        · exact (componentSetoid G ξ A).symm hrelated
      · apply actualConnected_component G ξ A
        apply actualConnected_of_adj
        rw [openGraph_adj]
        exact ⟨e, he, hexy⟩
    · intro x y hxy
      exact boundary_component G ξ A hxy
  · exact componentSetoid_mono ξ (Finset.subset_insert _ _)

theorem componentCount_insert_eq_of_related [Finite V] (ξ : BoundaryCondition V)
    (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (hrelated : (componentSetoid G ξ A).r u v) :
    componentCount G ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) =
      componentCount G ξ A := by
  rw [componentCount, componentCount, componentSetoid_insert_eq_of_related ξ A huv hrelated]

/-- Boundary identification alone suffices for insertion invariance. -/
theorem componentSetoid_insert_eq_of_boundary (ξ : BoundaryCondition V)
    (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (hboundary : ξ.partition.r u v) :
    componentSetoid G ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) =
      componentSetoid G ξ A :=
  componentSetoid_insert_eq_of_related ξ A huv (boundary_component G ξ A hboundary)

end Insertion

end PottsDiscontinuity.FK
