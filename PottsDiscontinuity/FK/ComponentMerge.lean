/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.Wiring
public import Mathlib.Data.Fintype.Card

/-!
# Opening an edge between distinct wired components

The new quotient is explicitly identified with the old component quotient with
one class removed. Thus opening a genuine edge between different components
merges exactly two classes, counting all original isolated vertices as before.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

variable {V : Type*} {G : SimpleGraph V}

 noncomputable def collapseComponent (s : Setoid V) (u v : V)
    (hne : ¬ s.r u v) (x : V) : {q : Quotient s // q ≠ Quotient.mk s v} := by
  classical
  exact if h : Quotient.mk s x = Quotient.mk s v then
    ⟨Quotient.mk s u, fun h => hne (Quotient.exact h)⟩ else ⟨Quotient.mk s x, h⟩

 theorem collapseComponent_respects (s : Setoid V) (u v : V)
    (hne : ¬ s.r u v) {x y : V} (hxy : s.r x y) :
    collapseComponent s u v hne x = collapseComponent s u v hne y := by
  classical
  apply Subtype.ext
  simp only [collapseComponent]
  simp only [Quotient.sound hxy]

 theorem collapseComponent_surjective (s : Setoid V) (u v : V)
    (hne : ¬ s.r u v) : Function.Surjective (collapseComponent s u v hne) := by
  classical
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
  refine ⟨x, ?_⟩
  apply Subtype.ext
  simp [collapseComponent, hq]

/-- The quotient after adding an edge between distinct components is the old
quotient with the second endpoint's class removed. This is a real equivalence. -/
noncomputable def componentQuotientInsertEquiv [DecidableEq G.edgeSet]
    (ξ : BoundaryCondition V) (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (hne : ¬ (componentSetoid G ξ A).r u v) :
    Quotient (componentSetoid G ξ (insert ⟨s(u,v), G.mem_edgeSet.mpr huv⟩ A)) ≃
      {q : Quotient (componentSetoid G ξ A) //
        q ≠ Quotient.mk (componentSetoid G ξ A) v} := by
  classical
  let s := componentSetoid G ξ A
  let t := componentSetoid G ξ (insert ⟨s(u,v), G.mem_edgeSet.mpr huv⟩ A)
  let f := collapseComponent s u v hne
  have hst : s ≤ t := componentSetoid_mono ξ (Finset.subset_insert _ _)
  have htuv : t.r u v := by
    apply actualConnected_component
    apply actualConnected_of_adj
    rw [openGraph_adj]
    exact ⟨⟨s(u,v), G.mem_edgeSet.mpr huv⟩, Finset.mem_insert_self _ _, rfl⟩
  have huvf : f u = f v := by
    apply Subtype.ext
    simp [f, collapseComponent, show Quotient.mk s u ≠ Quotient.mk s v from
      fun h => hne (Quotient.exact h)]
  have hle : t ≤ Setoid.ker f := by
    apply componentSetoid_le
    · apply reachableSetoid_le_of_adj
      intro x y hxy
      rw [openGraph_adj] at hxy
      rcases hxy with ⟨e, he, hexy⟩
      rcases Finset.mem_insert.mp he with he | he
      · subst e
        rcases Sym2.eq_iff.mp hexy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact huvf
        · exact huvf.symm
      · apply collapseComponent_respects
        apply actualConnected_component
        apply actualConnected_of_adj
        rw [openGraph_adj]
        exact ⟨e,he,hexy⟩
    · intro x y hxy
      exact collapseComponent_respects s u v hne (boundary_component G ξ A hxy)
  have hge : Setoid.ker f ≤ t := by
    intro x y hxy
    have he := congrArg Subtype.val hxy
    change (f x).val = (f y).val at he
    by_cases hx : Quotient.mk s x = Quotient.mk s v <;>
      by_cases hy : Quotient.mk s y = Quotient.mk s v
    · exact hst (Quotient.exact (hx.trans hy.symm))
    · have huy : s.r u y := by
        apply Quotient.exact
        simpa [f, collapseComponent, hx, hy] using he
      exact t.trans (hst (Quotient.exact hx)) (t.trans (t.symm htuv) (hst huy))
    · have hxu : s.r x u := by
        apply Quotient.exact
        simpa [f, collapseComponent, hx, hy] using he
      exact t.trans (hst hxu) (t.trans htuv (hst (Quotient.exact hy.symm)))
    · apply hst
      apply Quotient.exact
      simpa [f, collapseComponent, hx, hy] using he
  have ht : t = Setoid.ker f := le_antisymm hle hge
  exact (Quotient.congrRight (Setoid.ext_iff.mp ht)).trans
    (Setoid.quotientKerEquivOfSurjective f (collapseComponent_surjective s u v hne))

/-- Opening an edge between different wired components decreases their number
by exactly one. The edge need not be separately assumed absent: distinctness
already implies that fact. -/
theorem componentCount_insert_of_not_related [Finite V] [DecidableEq G.edgeSet]
    (ξ : BoundaryCondition V) (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (hne : ¬ (componentSetoid G ξ A).r u v) :
    componentCount G ξ (insert ⟨s(u,v), G.mem_edgeSet.mpr huv⟩ A) + 1 =
      componentCount G ξ A := by
  classical
  let s := componentSetoid G ξ A
  let : Fintype (Quotient s) := Fintype.ofFinite _
  have hcard := Nat.card_congr (componentQuotientInsertEquiv ξ A huv hne)
  have hpos : 0 < Nat.card (Quotient s) := by
    let : Nonempty (Quotient s) := ⟨Quotient.mk s u⟩
    exact Nat.card_pos
  change Nat.card (Quotient _) + 1 = Nat.card (Quotient s)
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (Quotient s) - 1 + 1 = Nat.card (Quotient s)
  omega

end PottsDiscontinuity.FK
