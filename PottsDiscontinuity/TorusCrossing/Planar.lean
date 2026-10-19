module

public import PottsDiscontinuity.TorusCrossing.EndGraph

/-!
# Rectangular boards of the rotated lattice, with their primal and dual graphs

`Rect` is a block of cells `[x0, x0 + w] × [y0, y0 + h]`.  Its primal graph has the primal cells
as vertices and one edge for every medial vertex of the *inner* index set
`[x0+1, x0+w] × [y0+1, y0+h]` (the unit squares of the board).  The dual graph has the odd
cells as vertices and the crossing dual edges.  The boundary condition `sepBC` wires the
primal cells of the bottom row together and, separately, those of the top row; `dualBC` wires
the odd cells of the left and right columns into one class.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity

/-- A rectangular board of cells. -/
structure Rect where
  x0 : ℤ
  y0 : ℤ
  w : ℕ
  h : ℕ

namespace Rect

variable (R : Rect)

/-- All cells of the board. -/
def cells : Finset Cell := Finset.Icc R.x0 (R.x0 + R.w) ×ˢ Finset.Icc R.y0 (R.y0 + R.h)

/-- Medial vertices (unit squares) of the board. -/
def inner : Finset Cell := Finset.Icc (R.x0 + 1) (R.x0 + R.w) ×ˢ Finset.Icc (R.y0 + 1) (R.y0 + R.h)

/-- Primal cells of the board. -/
def pcells : Finset Cell := R.cells.filter (fun c => IsPrimal c)

/-- Odd (dual) cells of the board. -/
def dcells : Finset Cell := R.cells.filter (fun c => ¬ IsPrimal c)

variable {R}

theorem mem_cells {c : Cell} :
    c ∈ R.cells ↔ R.x0 ≤ c.1 ∧ c.1 ≤ R.x0 + R.w ∧ R.y0 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h := by
  unfold cells; simp only [Finset.mem_product, Finset.mem_Icc]; tauto

theorem mem_inner {m : Cell} :
    m ∈ R.inner ↔ R.x0 + 1 ≤ m.1 ∧ m.1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ m.2 ∧ m.2 ≤ R.y0 + R.h := by
  unfold inner; simp only [Finset.mem_product, Finset.mem_Icc]; tauto

theorem mem_pcells {c : Cell} : c ∈ R.pcells ↔ c ∈ R.cells ∧ IsPrimal c := by
  unfold pcells; simp [Finset.mem_filter]

theorem mem_dcells {c : Cell} : c ∈ R.dcells ↔ c ∈ R.cells ∧ ¬ IsPrimal c := by
  unfold dcells; simp [Finset.mem_filter]

theorem pData (R : Rect) : EndData primalEnds R.pcells R.inner where
  mem m hm := by
    rw [mem_inner] at hm
    refine ⟨mem_pcells.2 ⟨mem_cells.2 ?_, primalEnds_fst_primal m⟩,
      mem_pcells.2 ⟨mem_cells.2 ?_, primalEnds_snd_primal m⟩⟩ <;>
    · unfold primalEnds; split_ifs <;> dsimp only <;> omega
  ne := primalEnds_ne
  inj _ _ h := primalEnds_inj h

theorem dData (R : Rect) : EndData dualEnds R.dcells R.inner where
  mem m hm := by
    rw [mem_inner] at hm
    refine ⟨mem_dcells.2 ⟨mem_cells.2 ?_, dualEnds_fst_not_primal m⟩,
      mem_dcells.2 ⟨mem_cells.2 ?_, dualEnds_snd_not_primal m⟩⟩ <;>
    · unfold dualEnds; split_ifs <;> dsimp only <;> omega
  ne := dualEnds_ne
  inj _ _ h := dualEnds_inj h

variable (R)

/-- The primal board graph. -/
abbrev pG : SimpleGraph R.pcells := endGraph primalEnds R.pcells R.inner

/-- The dual board graph. -/
abbrev dG : SimpleGraph R.dcells := endGraph dualEnds R.dcells R.inner

/-- Wiring of the bottom row of primal cells and, separately, of the top row. -/
def sepRel (a b : R.pcells) : Prop :=
  a = b ∨ (a.1.2 = R.y0 ∧ b.1.2 = R.y0) ∨ (a.1.2 = R.y0 + R.h ∧ b.1.2 = R.y0 + R.h)

/-- Boundary condition with the bottom row and top row wired separately. -/
def sepBC : FK.BoundaryCondition R.pcells where
  boundary := {c | c.1.2 = R.y0 ∨ c.1.2 = R.y0 + R.h}
  partition :=
    { r := R.sepRel
      iseqv :=
        { refl := fun a => Or.inl rfl
          symm := by
            rintro a b (h | h | h)
            · exact Or.inl h.symm
            · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
            · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
          trans := by
            rintro a b c (h | h | h) (h' | h' | h')
            · exact Or.inl (h.trans h')
            · subst h; exact Or.inr (Or.inl h')
            · subst h; exact Or.inr (Or.inr h')
            · subst h'; exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inl ⟨h.1, h'.2⟩)
            · exact Or.inr (Or.inr ⟨by omega, h'.2⟩)
            · subst h'; exact Or.inr (Or.inr h)
            · exact Or.inr (Or.inl ⟨by omega, h'.2⟩)
            · exact Or.inr (Or.inr ⟨h.1, h'.2⟩) }}
  supported := by
    intro a b h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl h.1, Or.inl h.2⟩
    · exact Or.inr ⟨Or.inr h.1, Or.inr h.2⟩

end Rect

end PottsDiscontinuity.TorusCrossing
