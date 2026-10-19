module

public import PottsDiscontinuity.Potts.GhostBoxGeometry
public import PottsDiscontinuity.Potts.FiniteEnergyBounds

/-! The four corner edges omitted by the literal boundary term. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

def cornerPoint (n : ℕ) (b : Bool × Bool) : ℤ × ℤ :=
  (if b.1 then (n : ℤ) else -(n : ℤ), if b.2 then (n : ℤ) else -(n : ℤ))

def cornerOutwardPoint (n : ℕ) (b : Bool × Bool) : ℤ × ℤ :=
  ((cornerPoint n b).1, if b.2 then (n : ℤ) + 1 else -(n : ℤ) - 1)

theorem cornerPoint_mem (n : ℕ) (b : Bool × Bool) : cornerPoint n b ∈ box n := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> rw [mem_box_iff] <;> dsimp [cornerPoint] <;> omega

theorem cornerOutwardPoint_mem (n : ℕ) (b : Bool × Bool) :
    cornerOutwardPoint n b ∈ box (n + 1) := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> rw [mem_box_iff] <;>
    dsimp [cornerOutwardPoint, cornerPoint] <;> omega

theorem cornerOutwardPoint_not_mem (n : ℕ) (b : Bool × Bool) :
    cornerOutwardPoint n b ∉ box n := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> rw [mem_box_iff] <;>
    dsimp [cornerOutwardPoint, cornerPoint] <;> omega

theorem cornerPoint_adj_outward (n : ℕ) (b : Bool × Bool) :
    squareLattice.Adj (cornerPoint n b) (cornerOutwardPoint n b) := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> rw [FK.squareLattice_adj_iff] <;>
    dsimp [cornerOutwardPoint, cornerPoint] <;> omega

/-- The vertical outward edge at a corner; the horizontal one is retained. -/
def cornerCutEdge (n : ℕ) (b : Bool × Bool) : OuterBoxEdge n :=
  ⟨s(⟨cornerPoint n b, box_subset_box_succ n (cornerPoint_mem n b)⟩,
      ⟨cornerOutwardPoint n b, cornerOutwardPoint_mem n b⟩),
    (squareLattice.induce _).mem_edgeSet.mpr (cornerPoint_adj_outward n b)⟩

theorem cornerPoint_injective (n : ℕ) (hn : 0 < n) : Function.Injective (cornerPoint n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [cornerPoint]

theorem cornerCutEdge_injective (n : ℕ) (hn : 0 < n) : Function.Injective (cornerCutEdge n) := by
  intro b c h
  have he : s(cornerPoint n b, cornerOutwardPoint n b) =
      s(cornerPoint n c, cornerOutwardPoint n c) :=
    congrArg (fun e : OuterBoxEdge n => Sym2.map Subtype.val e.val) h
  rcases Sym2.eq_iff.mp he with ⟨hbc, _⟩ | ⟨hbc, _⟩
  · exact cornerPoint_injective n hn hbc
  · exact (cornerOutwardPoint_not_mem n c (hbc ▸ cornerPoint_mem n b)).elim

def cornerCutEdges (n : ℕ) : Finset (OuterBoxEdge n) := by
  classical
  exact Finset.univ.image (cornerCutEdge n)

theorem card_cornerCutEdges (n : ℕ) (hn : 0 < n) : (cornerCutEdges n).card = 4 := by
  classical
  rw [cornerCutEdges, Finset.card_image_of_injective _ (cornerCutEdge_injective n hn)]
  decide

theorem cornerCutEdge_ne_ghostOutwardEdge (n : ℕ) (b : Bool × Bool)
    (x : BoundaryVertex (box n)) : cornerCutEdge n b ≠ ghostOutwardEdge n x := by
  intro h
  have he : s(cornerPoint n b, cornerOutwardPoint n b) =
      s(x.val.val, ghostOutwardNeighbor n x) :=
    congrArg (fun e : OuterBoxEdge n => Sym2.map Subtype.val e.val) h
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, _⟩
  · have hfst := congrArg Prod.fst h2
    have hx := congrArg Prod.fst h1
    rcases b with ⟨b, c⟩
    cases b <;> cases c <;>
      dsimp [cornerOutwardPoint, cornerPoint] at hx hfst
    all_goals
      unfold ghostOutwardNeighbor at hfst
      split_ifs at hfst <;> dsimp at hfst <;> omega
  · exact (ghostOutwardNeighbor_not_mem n x (h1 ▸ cornerPoint_mem n b)).elim

/-- The event used in the outer wired conditioning, for positive inner radius. -/
def cornerClosureEvent (n : ℕ) : Set (FK.Configuration
    (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ)))) :=
  allClosedEdges (cornerCutEdges n)

/-- The exact four-corner event has the uniform finite-energy lower bound. -/
theorem cornerClosureEvent_probability_lower_bound (q : FK.Parameters) (n : ℕ) (hn : 0 < n) :
    (1 - FK.edgeParameter q) ^ 4 ≤
      (FK.measure (squareLattice.induce (box (n + 1) : Set (ℤ × ℤ))) q
        (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box (n + 1))})
        (cornerClosureEvent n)).toReal := by
  have h := measure_allClosedEdges_lower_bound q
    (FK.BoundaryCondition.wired {x | x.val ∈ vertexBoundary (box (n + 1))}) (cornerCutEdges n)
  rw [card_cornerCutEdges n hn] at h
  exact h

end
end PottsDiscontinuity.Potts
