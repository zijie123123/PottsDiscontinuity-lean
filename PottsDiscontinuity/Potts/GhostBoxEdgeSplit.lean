module

public import PottsDiscontinuity.Potts.GhostBoxCorners

/-! Classification of the outer-box edges into literal bonds, cuts, and shell edges. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

/-- Inclusion of the inner induced graph into the outer induced graph. -/
def innerBoxGraphEmbedding (n : ℕ) :
    squareLattice.induce (box n : Set (ℤ × ℤ)) ↪g
      squareLattice.induce (box (n + 1) : Set (ℤ × ℤ)) :=
  squareLattice.induceHomOfLE (fun _ hx => box_subset_box_succ n hx)

def innerBoxEdgeEmbedding (n : ℕ) :
    (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet ↪ OuterBoxEdge n :=
  (innerBoxGraphEmbedding n).mapEdgeSet

theorem innerBoxEdgeEmbedding_inside (n : ℕ)
    (e : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet)
    (x : ↥(box (n + 1) : Set (ℤ × ℤ))) (hx : x ∈ (innerBoxEdgeEmbedding n e).val) :
    x.val ∈ box n := by
  change x ∈ Sym2.map (innerBoxGraphEmbedding n) e.val at hx
  obtain ⟨a, _, ha⟩ := Sym2.mem_map.mp hx
  exact ha ▸ a.property

def literalBondOuterEdge (n : ℕ) : LiteralBond (box n) → OuterBoxEdge n
  | .inl e => innerBoxEdgeEmbedding n e
  | .inr x => ghostOutwardEdge n x

theorem literalBondOuterEdge_injective (n : ℕ) : Function.Injective (literalBondOuterEdge n) := by
  intro a b h
  cases a with
  | inl e =>
      cases b with
      | inl f => exact congrArg Sum.inl ((innerBoxEdgeEmbedding n).injective h)
      | inr x =>
          have hm : (⟨ghostOutwardNeighbor n x, ghostOutwardNeighbor_mem_outer n x⟩ :
              ↥(box (n + 1) : Set (ℤ × ℤ))) ∈ (innerBoxEdgeEmbedding n e).val := by
            rw [show innerBoxEdgeEmbedding n e = ghostOutwardEdge n x from h]
            exact Sym2.mem_mk_right _ _
          exact (ghostOutwardNeighbor_not_mem n x
            (innerBoxEdgeEmbedding_inside n e _ hm)).elim
  | inr x =>
      cases b with
      | inl e =>
          have hm : (⟨ghostOutwardNeighbor n x, ghostOutwardNeighbor_mem_outer n x⟩ :
              ↥(box (n + 1) : Set (ℤ × ℤ))) ∈ (innerBoxEdgeEmbedding n e).val := by
            rw [show innerBoxEdgeEmbedding n e = ghostOutwardEdge n x from h.symm]
            exact Sym2.mem_mk_right _ _
          exact (ghostOutwardNeighbor_not_mem n x
            (innerBoxEdgeEmbedding_inside n e _ hm)).elim
      | inr y => exact congrArg Sum.inr (ghostOutwardEdge_injective n h)

/-- A crossing edge is either the retained ghost edge or the omitted vertical
edge at a corner. The positive-radius hypothesis excludes the singleton box. -/
theorem crossingEdge_classification (n : ℕ) (hn : 0 < n)
    (x : BoundaryVertex (box n)) (y : ℤ × ℤ)
    (hxy : squareLattice.Adj x.val.val y) (hy : y ∉ box n) :
    y = ghostOutwardNeighbor n x ∨
      ∃ b : Bool × Bool, x.val.val = cornerPoint n b ∧ y = cornerOutwardPoint n b := by
  have hx := (mem_box_iff n x.val.val).mp x.val.property
  rw [mem_box_iff] at hy
  rw [FK.squareLattice_adj_iff] at hxy
  by_cases hx1 : x.val.val.1 = (n : ℤ)
  · by_cases hy1 : y.1 = (n : ℤ) + 1
    · left
      rw [ghostOutwardNeighbor, ite_eq_left hx1]
      ext <;> (try dsimp) <;> omega
    · right
      by_cases hx2 : x.val.val.2 = (n : ℤ)
      · refine ⟨(true, true), ?_, ?_⟩ <;> ext <;> dsimp [cornerPoint, cornerOutwardPoint] <;> omega
      · refine ⟨(true, false), ?_, ?_⟩ <;> ext <;> dsimp [cornerPoint, cornerOutwardPoint] <;> omega
  · by_cases hx1' : x.val.val.1 = -(n : ℤ)
    · by_cases hy1 : y.1 = -(n : ℤ) - 1
      · left
        rw [ghostOutwardNeighbor, ite_eq_right hx1, ite_eq_left hx1']
        ext <;> (try dsimp) <;> omega
      · right
        by_cases hx2 : x.val.val.2 = (n : ℤ)
        · refine ⟨(false, true), ?_, ?_⟩ <;> ext <;> dsimp [cornerPoint, cornerOutwardPoint] <;> omega
        · refine ⟨(false, false), ?_, ?_⟩ <;> ext <;> dsimp [cornerPoint, cornerOutwardPoint] <;> omega
    · left
      rw [ghostOutwardNeighbor, ite_eq_right hx1, ite_eq_right hx1']
      split_ifs <;> ext <;> (try dsimp) <;> omega

def outerEdgeCoordinates (n : ℕ) (e : OuterBoxEdge n) : Sym2 (ℤ × ℤ) :=
  Sym2.map Subtype.val e.val

theorem outerEdgeCoordinates_injective (n : ℕ) : Function.Injective (outerEdgeCoordinates n) := by
  intro e f h
  apply Subtype.ext
  exact Sym2.map.injective (f := fun x : ↥(box (n + 1) : Set (ℤ × ℤ)) => x.val)
    Subtype.val_injective h

@[simp] theorem outerEdgeCoordinates_ghost (n : ℕ) (x : BoundaryVertex (box n)) :
    outerEdgeCoordinates n (ghostOutwardEdge n x) = s(x.val.val, ghostOutwardNeighbor n x) := rfl

@[simp] theorem outerEdgeCoordinates_corner (n : ℕ) (b : Bool × Bool) :
    outerEdgeCoordinates n (cornerCutEdge n b) = s(cornerPoint n b, cornerOutwardPoint n b) := rfl

theorem literalBondOuterEdge_has_inner (n : ℕ) (b : LiteralBond (box n)) :
    ∃ x ∈ (literalBondOuterEdge n b).val, x.val ∈ box n := by
  cases b with
  | inl e =>
      refine ⟨innerBoxGraphEmbedding n e.val.out.1, ?_, e.val.out.1.property⟩
      change innerBoxGraphEmbedding n e.val.out.1 ∈ Sym2.map (innerBoxGraphEmbedding n) e.val
      exact Sym2.mem_map.mpr ⟨e.val.out.1, Sym2.out_fst_mem e.val, rfl⟩
  | inr x =>
      exact ⟨⟨x.val.val, box_subset_box_succ n x.val.property⟩,
        Sym2.mem_mk_left _ _, x.val.property⟩

theorem literalBondOuterEdge_ne_corner (n : ℕ) (b : LiteralBond (box n)) (c : Bool × Bool) :
    literalBondOuterEdge n b ≠ cornerCutEdge n c := by
  cases b with
  | inr x => exact (cornerCutEdge_ne_ghostOutwardEdge n c x).symm
  | inl e =>
      intro h
      have hm : (⟨cornerOutwardPoint n c, cornerOutwardPoint_mem n c⟩ :
          ↥(box (n + 1) : Set (ℤ × ℤ))) ∈ (innerBoxEdgeEmbedding n e).val := by
        rw [show innerBoxEdgeEmbedding n e = cornerCutEdge n c from h]
        exact Sym2.mem_mk_right _ _
      exact cornerOutwardPoint_not_mem n c (innerBoxEdgeEmbedding_inside n e _ hm)

abbrev OuterShellEdge (n : ℕ) :=
  {e : OuterBoxEdge n // ∀ x ∈ e.val, x.val ∉ box n}

abbrev OuterEdgePiece (n : ℕ) := LiteralBond (box n) ⊕ ((Bool × Bool) ⊕ OuterShellEdge n)

def outerEdgeFromPiece (n : ℕ) : OuterEdgePiece n → OuterBoxEdge n
  | .inl b => literalBondOuterEdge n b
  | .inr (.inl b) => cornerCutEdge n b
  | .inr (.inr e) => e.val

private theorem literal_ne_shell (n : ℕ) (b : LiteralBond (box n)) (e : OuterShellEdge n) :
    literalBondOuterEdge n b ≠ e.val := by
  intro h
  obtain ⟨x, hx, hi⟩ := literalBondOuterEdge_has_inner n b
  rw [h] at hx
  exact e.property x hx hi

private theorem corner_ne_shell (n : ℕ) (b : Bool × Bool) (e : OuterShellEdge n) :
    cornerCutEdge n b ≠ e.val := by
  intro h
  have hx : (⟨cornerPoint n b, box_subset_box_succ n (cornerPoint_mem n b)⟩ :
      ↥(box (n + 1) : Set (ℤ × ℤ))) ∈ e.val.val := by
    rw [← h]
    exact Sym2.mem_mk_left _ _
  exact e.property _ hx (cornerPoint_mem n b)

theorem outerEdgeFromPiece_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (outerEdgeFromPiece n) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (literalBondOuterEdge_injective n h)
      | inr b =>
          cases b with
          | inl c => exact (literalBondOuterEdge_ne_corner n a c h).elim
          | inr e => exact (literal_ne_shell n a e h).elim
  | inr a =>
      cases a with
      | inl c =>
          cases b with
          | inl a => exact (literalBondOuterEdge_ne_corner n a c h.symm).elim
          | inr b =>
              cases b with
              | inl d => exact congrArg (fun z => Sum.inr (Sum.inl z)) (cornerCutEdge_injective n hn h)
              | inr e => exact (corner_ne_shell n c e h).elim
      | inr e =>
          cases b with
          | inl a => exact (literal_ne_shell n a e h.symm).elim
          | inr b =>
              cases b with
              | inl c => exact (corner_ne_shell n c e h.symm).elim
              | inr f => exact congrArg (fun z => Sum.inr (Sum.inr z)) (Subtype.ext h)

private theorem crossingEdge_in_range (n : ℕ) (hn : 0 < n)
    (u v : ↥(box (n + 1) : Set (ℤ × ℤ)))
    (huv : squareLattice.Adj u.val v.val) (hu : u.val ∈ box n) (hv : v.val ∉ box n) :
    ∃ b : OuterEdgePiece n,
      outerEdgeFromPiece n b = ⟨s(u, v), (squareLattice.induce _).mem_edgeSet.mpr huv⟩ := by
  let x : BoundaryVertex (box n) := ⟨⟨u.val, hu⟩, hu, v.val, huv, hv⟩
  rcases crossingEdge_classification n hn x v.val huv hv with h | ⟨b, hb, hvb⟩
  · refine ⟨.inl (.inr x), ?_⟩
    apply outerEdgeCoordinates_injective n
    change s(u.val, ghostOutwardNeighbor n x) = s(u.val, v.val)
    rw [h]
  · refine ⟨.inr (.inl b), ?_⟩
    apply outerEdgeCoordinates_injective n
    change s(cornerPoint n b, cornerOutwardPoint n b) = s(u.val, v.val)
    exact congrArg₂ Sym2.mk hb.symm hvb.symm

theorem outerEdgeFromPiece_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (outerEdgeFromPiece n) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : squareLattice.Adj u.val v.val := (squareLattice.induce _).mem_edgeSet.mp he
      by_cases hu : u.val ∈ box n
      · by_cases hv : v.val ∈ box n
        · let a : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet :=
            ⟨s(⟨u.val, hu⟩, ⟨v.val, hv⟩), (squareLattice.induce _).mem_edgeSet.mpr huv⟩
          exact ⟨.inl (.inl a), rfl⟩
        · exact crossingEdge_in_range n hn u v huv hu hv
      · by_cases hv : v.val ∈ box n
        · obtain ⟨b, hb⟩ := crossingEdge_in_range n hn v u huv.symm hv hu
          refine ⟨b, hb.trans ?_⟩
          apply Subtype.ext
          exact Sym2.eq_swap
        · refine ⟨.inr (.inr ⟨⟨s(u, v), he⟩, ?_⟩), rfl⟩
          intro x hx
          rcases Sym2.mem_iff.mp hx with rfl | rfl
          · exact hu
          · exact hv

/-- The exact edge-index decomposition used to sum out the wired shell and to
condition the four omitted corner bonds closed. -/
def outerBoxEdgeEquiv (n : ℕ) (hn : 0 < n) : OuterEdgePiece n ≃ OuterBoxEdge n :=
  Equiv.ofBijective (outerEdgeFromPiece n)
    ⟨outerEdgeFromPiece_injective n hn, outerEdgeFromPiece_surjective n hn⟩

end
end PottsDiscontinuity.Potts
