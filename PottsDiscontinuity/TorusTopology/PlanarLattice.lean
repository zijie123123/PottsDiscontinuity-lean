/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Interval

/-! The square lattice and its finite closed boxes.

The vertex carrier of each induced graph is the entire box, including isolated
vertices. These boxes are lattice infrastructure, not a definition of the marked
Jordan-domain approximations in Theorem 1.1.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar

/-- Vertices of the unscaled square lattice. -/
abbrev LatticeVertex := ℤ × ℤ

/-- Horizontal or vertical unit-step adjacency on the square lattice. -/
def squareLattice : SimpleGraph LatticeVertex where
  Adj u v :=
    ((u.1 + 1 = v.1 ∨ v.1 + 1 = u.1) ∧ u.2 = v.2) ∨
    (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2))
  symm := ⟨by intro u v h; omega⟩
  loopless := ⟨by intro u; omega⟩

instance : DecidableRel squareLattice.Adj := by
  intro u v
  unfold squareLattice
  infer_instance

lemma squareLattice_adj_iff (u v : LatticeVertex) :
    squareLattice.Adj u v ↔
      ((u.1 + 1 = v.1 ∨ v.1 + 1 = u.1) ∧ u.2 = v.2) ∨
      (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)) := Iff.rfl

/-- Translation by an integer lattice vector. -/
def latticeTranslate (a v : LatticeVertex) : LatticeVertex :=
  (v.1 + a.1, v.2 + a.2)

lemma latticeTranslate_zero (v : LatticeVertex) : latticeTranslate 0 v = v := by
  simp only [latticeTranslate, Prod.fst_zero, Prod.snd_zero, add_zero]

lemma latticeTranslate_neg_cancel (a v : LatticeVertex) :
    latticeTranslate (-a) (latticeTranslate a v) = v := by
  ext <;> dsimp [latticeTranslate] <;> omega

lemma squareLattice_adj_translate_iff (a u v : LatticeVertex) :
    squareLattice.Adj (latticeTranslate a u) (latticeTranslate a v) ↔
      squareLattice.Adj u v := by
  simp only [squareLattice_adj_iff, latticeTranslate]
  omega

/-- Every integer translation is a graph automorphism of the square lattice. -/
def latticeTranslationIso (a : LatticeVertex) : squareLattice ≃g squareLattice where
  toFun := latticeTranslate a
  invFun := latticeTranslate (-a)
  left_inv := latticeTranslate_neg_cancel a
  right_inv v := by ext <;> dsimp [latticeTranslate] <;> omega
  map_rel_iff' := squareLattice_adj_translate_iff a _ _

/-- The closed integer box with center `c` and coordinate radius `r`. -/
def latticeBox (c : LatticeVertex) (r : ℕ) : Finset LatticeVertex :=
  (Finset.Icc (c.1 - (r : ℤ)) (c.1 + (r : ℤ))) ×ˢ
    (Finset.Icc (c.2 - (r : ℤ)) (c.2 + (r : ℤ)))

lemma mem_latticeBox (c v : LatticeVertex) (r : ℕ) :
    v ∈ latticeBox c r ↔
      (c.1 - (r : ℤ) ≤ v.1 ∧ v.1 ≤ c.1 + (r : ℤ)) ∧
      (c.2 - (r : ℤ) ≤ v.2 ∧ v.2 ≤ c.2 + (r : ℤ)) := by
  simp only [latticeBox, Finset.mem_product, Finset.mem_Icc]

lemma center_mem_latticeBox (c : LatticeVertex) (r : ℕ) : c ∈ latticeBox c r := by
  rw [mem_latticeBox]
  omega

lemma latticeBox_mono (c : LatticeVertex) {r s : ℕ} (hrs : r ≤ s) :
    latticeBox c r ⊆ latticeBox c s := by
  intro v hv
  rw [mem_latticeBox] at hv ⊢
  omega

lemma mem_latticeBox_translate_iff (a c v : LatticeVertex) (r : ℕ) :
    latticeTranslate a v ∈ latticeBox (latticeTranslate a c) r ↔
      v ∈ latticeBox c r := by
  simp only [mem_latticeBox, latticeTranslate]
  omega

lemma card_latticeBox (c : LatticeVertex) (r : ℕ) :
    (latticeBox c r).card = (2 * r + 1) ^ 2 := by
  rw [latticeBox, Finset.card_product, Int.card_Icc, Int.card_Icc]
  have hx : (c.1 + (r : ℤ) + 1 - (c.1 - (r : ℤ))).toNat = 2 * r + 1 := by omega
  have hy : (c.2 + (r : ℤ) + 1 - (c.2 - (r : ℤ))).toNat = 2 * r + 1 := by omega
  rw [hx, hy, pow_two]

/-- All vertices of a finite box, regardless of whether they meet an open edge. -/
abbrev BoxVertex (c : LatticeVertex) (r : ℕ) := {v : LatticeVertex // v ∈ latticeBox c r}

lemma card_boxVertex (c : LatticeVertex) (r : ℕ) :
    Fintype.card (BoxVertex c r) = (2 * r + 1) ^ 2 := by
  rw [Fintype.card_coe, card_latticeBox]

/-- The induced square-lattice graph on the full box carrier. -/
def boxGraph (c : LatticeVertex) (r : ℕ) : SimpleGraph (BoxVertex c r) :=
  squareLattice.induce (latticeBox c r : Set LatticeVertex)

instance (c : LatticeVertex) (r : ℕ) : DecidableRel (boxGraph c r).Adj := by
  unfold boxGraph
  infer_instance

lemma boxGraph_adj_iff (c : LatticeVertex) (r : ℕ) (u v : BoxVertex c r) :
    (boxGraph c r).Adj u v ↔ squareLattice.Adj u.val v.val := Iff.rfl

end PottsDiscontinuity.TorusTopology.Planar
