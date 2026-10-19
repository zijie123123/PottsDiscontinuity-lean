/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Interval
public import PottsDiscontinuity.FK.Lattice

@[expose] public section

namespace PottsDiscontinuity.FK

/-- Closed axis-aligned lattice rectangle with lower-left corner `a` and
natural-number side lengths `w` and `h`. -/
def latticeRectangle (a : LatticeVertex) (w h : ℕ) : Finset LatticeVertex :=
  Finset.Icc a.1 (a.1 + (w : ℤ)) ×ˢ Finset.Icc a.2 (a.2 + (h : ℤ))

lemma mem_latticeRectangle (a v : LatticeVertex) (w h : ℕ) :
    v ∈ latticeRectangle a w h ↔
      (a.1 ≤ v.1 ∧ v.1 ≤ a.1 + (w : ℤ)) ∧
      (a.2 ≤ v.2 ∧ v.2 ≤ a.2 + (h : ℤ)) := by
  simp only [latticeRectangle, Finset.mem_product, Finset.mem_Icc]

lemma card_latticeRectangle (a : LatticeVertex) (w h : ℕ) :
    (latticeRectangle a w h).card = (w + 1) * (h + 1) := by
  rw [latticeRectangle, Finset.card_product, Int.card_Icc, Int.card_Icc]
  have hw : (a.1 + (w : ℤ) + 1 - a.1).toNat = w + 1 := by omega
  have hh : (a.2 + (h : ℤ) + 1 - a.2).toNat = h + 1 := by omega
  rw [hw, hh]

/-- All rectangle vertices, including isolated vertices. -/
abbrev RectangleVertex (a : LatticeVertex) (w h : ℕ) :=
  {v : LatticeVertex // v ∈ latticeRectangle a w h}

lemma card_rectangleVertex (a : LatticeVertex) (w h : ℕ) :
    Fintype.card (RectangleVertex a w h) = (w + 1) * (h + 1) := by
  rw [Fintype.card_coe, card_latticeRectangle]

/-- The induced square-lattice graph on the entire closed rectangle. -/
def rectangleGraph (a : LatticeVertex) (w h : ℕ) : SimpleGraph (RectangleVertex a w h) :=
  squareLattice.induce (latticeRectangle a w h : Set LatticeVertex)

instance rectangleGraph_decidableAdj (a : LatticeVertex) (w h : ℕ) :
    DecidableRel (rectangleGraph a w h).Adj := by
  unfold rectangleGraph
  infer_instance

lemma rectangleGraph_adj_iff (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) :
    (rectangleGraph a w h).Adj u v ↔ squareLattice.Adj u.val v.val := Iff.rfl

/-- Closed left side, with both corners included. -/
def rectangleLeftSide (a : LatticeVertex) (w h : ℕ) : Finset LatticeVertex :=
  (latticeRectangle a w h).filter (fun v => v.1 = a.1)

/-- Closed right side, with both corners included. -/
def rectangleRightSide (a : LatticeVertex) (w h : ℕ) : Finset LatticeVertex :=
  (latticeRectangle a w h).filter (fun v => v.1 = a.1 + (w : ℤ))

lemma latticeRectangle_box_eq (c : LatticeVertex) (r : ℕ) :
    latticeRectangle (c.1 - (r : ℤ), c.2 - (r : ℤ)) (2 * r) (2 * r) =
      latticeBox c r := by
  ext v
  rw [mem_latticeRectangle, mem_latticeBox]
  norm_num
  omega

end PottsDiscontinuity.FK
