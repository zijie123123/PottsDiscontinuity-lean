module

public import PottsDiscontinuity.FK.FiniteEnergy

/-!
# Finite-energy lower bounds for closed edge sets

The FK single-edge finite-energy estimate iterates to a uniform lower bound
for every prescribed finite set of edges to be closed. In particular, four
specified edges have closed probability at least `(1 - p)^4`.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- Configurations in which every edge in `F` is closed. -/
def allClosedEdges (F : Finset G.edgeSet) : Set (FK.Configuration G) :=
  {A | Disjoint F A}

/-- In any finite FK measure, each prescribed finite set of edges is closed
with probability at least `(1-p)` to the power of its cardinality. -/
theorem measure_allClosedEdges_lower_bound (q : FK.Parameters)
    (ξ : FK.BoundaryCondition V) (F : Finset G.edgeSet) :
    (1 - FK.edgeParameter q) ^ F.card ≤
      (FK.measure G q ξ (allClosedEdges F)).toReal := by
  classical
  let : DecidableEq G.edgeSet := Classical.decEq _
  induction F using Finset.induction_on with
  | empty =>
      simp [allClosedEdges]
  | @insert e F he ih =>
      have hrepr (z : Sym2 V) : z ∈ G.edgeSet →
          ∃ u v, ∃ huv : G.Adj u v, z = s(u, v) := by
        refine Sym2.inductionOn z ?_
        intro u v hz
        exact ⟨u, v, G.mem_edgeSet.mp hz, rfl⟩
      obtain ⟨u, v, huv, hev⟩ := hrepr e.1 e.2
      have heq : e = ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ := by
        apply Subtype.ext
        exact hev
      subst e
      have hstable : ∀ A : FK.Configuration G,
          A ∈ allClosedEdges F ↔
            A.erase ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ ∈ allClosedEdges F := by
        intro A
        change Disjoint F A ↔ Disjoint F (A.erase ⟨s(u, v), G.mem_edgeSet.mpr huv⟩)
        constructor
        · intro h
          apply Finset.disjoint_left.mpr
          intro a haF haErase
          exact (Finset.disjoint_left.mp h) haF (Finset.mem_of_mem_erase haErase)
        · intro h
          apply Finset.disjoint_left.mpr
          intro a haF haA
          have hne : a ≠ (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) := by
            intro hEq
            subst a
            exact he haF
          exact (Finset.disjoint_left.mp h) haF (Finset.mem_erase.mpr ⟨hne, haA⟩)
      have hFE := FK.configurationProbability_edge_finite_energy_closed q ξ
        (allClosedEdges F) huv hstable
      have hEvent : allClosedEdges F ∩
          {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A} =
            allClosedEdges (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ F) := by
        ext A
        change (Disjoint F A ∧
          (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A) ↔
            Disjoint (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ F) A
        constructor
        · rintro ⟨hFA, heA⟩
          apply Finset.disjoint_left.mpr
          intro a ha aA
          rcases Finset.mem_insert.mp ha with hae | haF
          · exact heA (hae ▸ aA)
          · exact (Finset.disjoint_left.mp hFA) haF aA
        · intro h
          constructor
          · apply Finset.disjoint_left.mpr
            intro a haF aA
            exact (Finset.disjoint_left.mp h) (Finset.mem_insert_of_mem haF) aA
          · intro heA
            exact (Finset.disjoint_left.mp h) (Finset.mem_insert_self _ _) heA
      rw [hEvent] at hFE
      have hp : 0 ≤ 1 - FK.edgeParameter q :=
        (FK.one_sub_edgeParameter_pos q).le
      have hpow : (1 - FK.edgeParameter q) ^ (insert ⟨s(u, v),
          G.mem_edgeSet.mpr huv⟩ F).card =
            (1 - FK.edgeParameter q) * (1 - FK.edgeParameter q) ^ F.card := by
        rw [Finset.card_insert_of_notMem he, pow_succ]
        ring
      rw [hpow]
      exact (mul_le_mul_of_nonneg_left ih hp).trans hFE.1

end

end PottsDiscontinuity.Potts
