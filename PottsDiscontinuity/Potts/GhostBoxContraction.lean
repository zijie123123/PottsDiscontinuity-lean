module

public import PottsDiscontinuity.Potts.GhostBoxEdgeSplit
public import PottsDiscontinuity.Potts.GhostBoundary

/-! Contraction of the wired outer shell, including its exact component partition. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

def outerBoxWiring (n : ℕ) : FK.BoundaryCondition ↥(box (n + 1) : Set (ℤ × ℤ)) :=
  FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box (n + 1))}

/-- Restore a literal configuration and arbitrary shell bonds, with all four cuts closed. -/
def restoreGhostBonds (n : ℕ) (hn : 0 < n) (ω : LiteralBond (box n) → Bool)
    (η : OuterShellEdge n → Bool) : OuterBoxEdge n → Bool :=
  fun e => ((outerBoxEdgeEquiv n hn).symm e).elim ω
    (fun b => b.elim (fun _ => false) η)

theorem restoreGhostBonds_piece (n : ℕ) (hn : 0 < n) (ω : LiteralBond (box n) → Bool)
    (η : OuterShellEdge n → Bool) (b : OuterEdgePiece n) :
    restoreGhostBonds n hn ω η (outerEdgeFromPiece n b) =
      b.elim ω (fun c => c.elim (fun _ => false) η) := by
  change (((outerBoxEdgeEquiv n hn).symm ((outerBoxEdgeEquiv n hn) b)).elim ω
    (fun c => c.elim (fun _ => false) η)) = _
  rw [Equiv.symm_apply_apply]

theorem collapseOuterBox_surjective (n : ℕ) : Function.Surjective (collapseOuterBox n) := by
  intro x
  cases x with
  | some x => exact ⟨⟨x.val, box_subset_box_succ n x.property⟩, collapseOuterBox_inner n x⟩
  | none =>
      have hm : ((n : ℤ) + 1, 0) ∈ box (n + 1) := by rw [mem_box_iff]; dsimp; omega
      have hnot : ((n : ℤ) + 1, 0) ∉ box n := by rw [mem_box_iff]; dsimp; omega
      exact ⟨⟨((n : ℤ) + 1, 0), hm⟩, by simp [collapseOuterBox, hnot]⟩

theorem collapseOuterBox_ker (n : ℕ) :
    Setoid.ker (collapseOuterBox n) = (outerBoxWiring n).partition := by
  classical
  ext u v
  change collapseOuterBox n u = collapseOuterBox n v ↔
    u = v ∨ u.val ∈ vertexBoundary (box (n + 1)) ∧ v.val ∈ vertexBoundary (box (n + 1))
  rw [← outer_shell_iff_boundary n u.val u.property,
    ← outer_shell_iff_boundary n v.val v.property]
  by_cases hu : u.val ∈ box n
  · by_cases hv : v.val ∈ box n
    · constructor
      · intro h
        have hs : (some ⟨u.val, hu⟩ : Option ↥(box n : Set (ℤ × ℤ))) = some ⟨v.val, hv⟩ := by
          simpa only [collapseOuterBox, dite_eq_left hu, dite_eq_left hv] using h
        exact Or.inl (Subtype.ext (congrArg
          (fun z : ↥(box n : Set (ℤ × ℤ)) => z.val) (Option.some.inj hs)))
      · rintro (rfl | ⟨hnu, _⟩)
        · rfl
        · exact (hnu hu).elim
    · constructor
      · intro h
        have hs : (some ⟨u.val, hu⟩ : Option ↥(box n : Set (ℤ × ℤ))) = none := by
          simpa only [collapseOuterBox, dite_eq_left hu, dite_eq_right hv] using h
        cases hs
      · rintro (h | ⟨hnu, _⟩)
        · exact (hv (h ▸ hu)).elim
        · exact (hnu hu).elim
  · by_cases hv : v.val ∈ box n
    · constructor
      · intro h
        have hs : (none : Option ↥(box n : Set (ℤ × ℤ))) = some ⟨v.val, hv⟩ := by
          simpa only [collapseOuterBox, dite_eq_right hu, dite_eq_left hv] using h
        cases hs
      · rintro (h | ⟨_, hnv⟩)
        · exact (hu (h.symm ▸ hv)).elim
        · exact (hnv hv).elim
    · simp only [collapseOuterBox, dite_eq_right hu, dite_eq_right hv]
      exact iff_of_true trivial (Or.inr ⟨hu, hv⟩)

@[simp] theorem collapseOuterBox_embedding (n : ℕ) (x : ↥(box n : Set (ℤ × ℤ))) :
    collapseOuterBox n (innerBoxGraphEmbedding n x) = some x := by
  exact collapseOuterBox_inner n x

theorem openGraph_bool_adj_iff {V : Type*} [Finite V] (G : SimpleGraph V)
    (ω : G.edgeSet → Bool) (u v : V) :
    (FK.openGraph G (FK.boolConfigurationEquiv G ω)).Adj u v ↔
      ∃ h : G.Adj u v, ω ⟨s(u, v), G.mem_edgeSet.mpr h⟩ = true := by
  rw [FK.openGraph_adj, FK.openEdges_boolConfigurationEquiv]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨G.mem_edgeSet.mp h, hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨G.mem_edgeSet.mpr h, hh⟩

private theorem restored_edge_maps_reachable (n : ℕ) (hn : 0 < n)
    (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool)
    (e : OuterBoxEdge n) (he : restoreGhostBonds n hn ω η e = true)
    (u v : ↥(box (n + 1) : Set (ℤ × ℤ))) (huv : s(u, v) = e.val) :
    (ghostOpenGraph (box n) ω).Reachable (collapseOuterBox n u) (collapseOuterBox n v) := by
  obtain ⟨b, rfl⟩ := outerEdgeFromPiece_surjective n hn e
  rw [restoreGhostBonds_piece] at he
  cases b with
  | inl b =>
      cases b with
      | inl e =>
          rcases e with ⟨e, heG⟩
          induction e using Sym2.inductionOn with
          | _ a b =>
              have hab : (squareLattice.induce (box n : Set (ℤ × ℤ))).Adj a b :=
                (squareLattice.induce _).mem_edgeSet.mp heG
              have hadj : (ghostOpenGraph (box n) ω).Adj (some a) (some b) :=
                (openGraph_bool_adj_iff _ _ a b).mpr ⟨hab, he⟩
              change s(u, v) = s(innerBoxGraphEmbedding n a, innerBoxGraphEmbedding n b) at huv
              rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · simpa only [collapseOuterBox_embedding] using hadj.reachable
              · simpa only [collapseOuterBox_embedding] using hadj.symm.reachable
      | inr x =>
          have hadj : (ghostOpenGraph (box n) ω).Adj (some x.val) none := ⟨x.property, he⟩
          change s(u, v) = s(⟨x.val.val, _⟩, ⟨ghostOutwardNeighbor n x, _⟩) at huv
          rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simpa only [collapseOuterBox_inner, collapseOuterBox_outward] using hadj.reachable
          · simpa only [collapseOuterBox_inner, collapseOuterBox_outward] using hadj.symm.reachable
  | inr b =>
      cases b with
      | inl b => exact Bool.noConfusion he
      | inr e =>
          have hu : u.val ∉ box n := e.property u (huv ▸ Sym2.mem_mk_left u v)
          have hv : v.val ∉ box n := e.property v (huv ▸ Sym2.mem_mk_right u v)
          have hu' : collapseOuterBox n u = none := by simp [collapseOuterBox, hu]
          have hv' : collapseOuterBox n v = none := by simp [collapseOuterBox, hv]
          rw [hu', hv']

/-- The outer wired partition is exactly the pullback of the literal ghost
connection partition. Shell bonds have no effect on this partition. -/
theorem outer_componentSetoid_eq_ghost_comap (n : ℕ) (hn : 0 < n)
    (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
    FK.componentSetoid _ (outerBoxWiring n) (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η)) =
      (ghostOpenGraph (box n) ω).reachableSetoid.comap (collapseOuterBox n) := by
  let G := squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))
  let C := FK.boolConfigurationEquiv G (restoreGhostBonds n hn ω η)
  let R := FK.componentSetoid G (outerBoxWiring n) C
  let f := collapseOuterBox n
  have hker : Setoid.ker f ≤ R := by
    rw [show Setoid.ker f = (outerBoxWiring n).partition from collapseOuterBox_ker n]
    exact le_sup_right
  apply le_antisymm
  · apply sup_le
    · apply FK.reachableSetoid_le_of_adj
      intro u v h
      obtain ⟨huv, hh⟩ := (openGraph_bool_adj_iff G (restoreGhostBonds n hn ω η) u v).mp h
      exact restored_edge_maps_reachable n hn ω η ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ hh u v rfl
    · rw [← collapseOuterBox_ker n]
      intro u v h
      change f u = f v at h
      change (ghostOpenGraph (box n) ω).reachableSetoid (f u) (f v)
      rw [h]
  · have hmap : (ghostOpenGraph (box n) ω).reachableSetoid ≤ R.map f := by
      apply FK.reachableSetoid_le_of_adj
      intro u v h
      have hgen {a b : ↥(box (n + 1) : Set (ℤ × ℤ))} (hab : R a b) :
          (R.map f) (f a) (f b) :=
        Relation.EqvGen.rel _ _ ⟨a, b, hab, rfl, rfl⟩
      have hcross (x : ↥(box n : Set (ℤ × ℤ)))
          (hx : x.val ∈ vertexBoundary (box n)) (hh : ω (.inr ⟨x, hx⟩) = true) :
          (R.map f) (some x) none := by
        let a : ↥(box (n + 1) : Set (ℤ × ℤ)) := ⟨x.val, box_subset_box_succ n x.property⟩
        let b : ↥(box (n + 1) : Set (ℤ × ℤ)) :=
          ⟨ghostOutwardNeighbor n ⟨x, hx⟩, ghostOutwardNeighbor_mem_outer n ⟨x, hx⟩⟩
        have hb : restoreGhostBonds n hn ω η (ghostOutwardEdge n ⟨x, hx⟩) = true := by
          rw [show ghostOutwardEdge n ⟨x, hx⟩ = outerEdgeFromPiece n (.inl (.inr ⟨x, hx⟩)) from rfl,
            restoreGhostBonds_piece]
          exact hh
        have hadj : (FK.openGraph G C).Adj a b :=
          (openGraph_bool_adj_iff G _ a b).mpr ⟨ghostOutwardNeighbor_adj n ⟨x, hx⟩, hb⟩
        have hr : R a b := FK.actualConnected_component G (outerBoxWiring n) C hadj.reachable
        simpa only [f, a, b, collapseOuterBox_inner, collapseOuterBox_outward] using hgen hr
      cases u with
      | none =>
          cases v with
          | none => exact h.elim
          | some x => obtain ⟨hx, hh⟩ := h; exact (hcross x hx hh).symm
      | some x =>
          cases v with
          | none => obtain ⟨hx, hh⟩ := h; exact hcross x hx hh
          | some y =>
              obtain ⟨hxy, hh⟩ := (openGraph_bool_adj_iff _ (fun e => ω (.inl e)) x y).mp h
              let a := innerBoxGraphEmbedding n x
              let b := innerBoxGraphEmbedding n y
              have hb : restoreGhostBonds n hn ω η
                  (innerBoxEdgeEmbedding n ⟨s(x, y), (squareLattice.induce _).mem_edgeSet.mpr hxy⟩) = true := by
                rw [show innerBoxEdgeEmbedding n ⟨s(x, y), _⟩ =
                  outerEdgeFromPiece n (.inl (.inl ⟨s(x, y), _⟩)) from rfl, restoreGhostBonds_piece]
                exact hh
              have hadj : (FK.openGraph G C).Adj a b :=
                (openGraph_bool_adj_iff G _ a b).mpr ⟨hxy, hb⟩
              have hr : R a b := FK.actualConnected_component G (outerBoxWiring n) C hadj.reachable
              simpa only [f, a, b, collapseOuterBox_embedding] using hgen hr
    have hcomap := Setoid.comap_map_of_ker_le f R hker
    intro u v h
    exact (Setoid.ext_iff.mp hcomap u v).mp (hmap h)

theorem outer_componentCount_eq_ghost (n : ℕ) (hn : 0 < n)
    (ω : LiteralBond (box n) → Bool) (η : OuterShellEdge n → Bool) :
    FK.componentCount _ (outerBoxWiring n)
        (FK.boolConfigurationEquiv _ (restoreGhostBonds n hn ω η)) =
      ghostComponentCount (box n) ω := by
  rw [FK.componentCount, outer_componentSetoid_eq_ghost_comap, Setoid.comap_eq]
  exact Nat.card_congr (Setoid.quotientKerEquivOfSurjective _
    (Quotient.mk_surjective.comp (collapseOuterBox_surjective n)))

end
end PottsDiscontinuity.Potts
