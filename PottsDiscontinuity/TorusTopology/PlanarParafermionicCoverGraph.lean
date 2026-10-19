/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarLattice
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar

/-- Vertices of the literal three-coordinate graph in DST17, p.46. -/
abbrev ParafermionicCoverVertex := LatticeVertex × ℤ

/-- The increment of the sheet coordinate when crossing the lower seam. -/
def parafermionicCoverSheetShift (p q : LatticeVertex) : ℤ :=
  if p.1 = 0 ∧ q.1 = 1 ∧ p.2 = q.2 ∧ p.2 < 0 then 1
  else if p.1 = 1 ∧ q.1 = 0 ∧ p.2 = q.2 ∧ p.2 < 0 then -1
  else 0

/-- The four actual edge types in the source, listed in both orientations:
vertical, ordinary horizontal, upper seam, and lower seam. -/
def parafermionicCoverAdjCases (u v : ParafermionicCoverVertex) : Prop :=
  (u.1.1 = v.1.1 ∧ u.1.2 + 1 = v.1.2 ∧ u.2 = v.2) ∨
  (u.1.1 = v.1.1 ∧ v.1.2 + 1 = u.1.2 ∧ u.2 = v.2) ∨
  (u.1.2 = v.1.2 ∧ u.2 = v.2 ∧ u.1.1 + 1 = v.1.1 ∧ u.1.1 ≠ 0) ∨
  (u.1.2 = v.1.2 ∧ u.2 = v.2 ∧ v.1.1 + 1 = u.1.1 ∧ v.1.1 ≠ 0) ∨
  (u.1.1 = 0 ∧ v.1.1 = 1 ∧ u.1.2 = v.1.2 ∧ 0 ≤ u.1.2 ∧ u.2 = v.2) ∨
  (u.1.1 = 1 ∧ v.1.1 = 0 ∧ u.1.2 = v.1.2 ∧ 0 ≤ u.1.2 ∧ u.2 = v.2) ∨
  (u.1.1 = 0 ∧ v.1.1 = 1 ∧ u.1.2 = v.1.2 ∧ u.1.2 < 0 ∧ u.2 + 1 = v.2) ∨
  (u.1.1 = 1 ∧ v.1.1 = 0 ∧ u.1.2 = v.1.2 ∧ u.1.2 < 0 ∧ v.2 + 1 = u.2)

theorem parafermionicCoverSheetShift_reverse (p q : LatticeVertex) :
    parafermionicCoverSheetShift q p = -parafermionicCoverSheetShift p q := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  unfold parafermionicCoverSheetShift
  dsimp only
  split_ifs <;> omega

def parafermionicCoverGraph : SimpleGraph ParafermionicCoverVertex where
  Adj u v := squareLattice.Adj u.1 v.1 ∧
    v.2 = u.2 + parafermionicCoverSheetShift u.1 v.1
  symm := ⟨by
    intro u v h
    rcases h with ⟨hbase, hsheet⟩
    refine ⟨?_, ?_⟩
    · rw [squareLattice_adj_iff] at hbase ⊢
      omega
    · rw [parafermionicCoverSheetShift_reverse]
      omega⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨ha, _⟩
    rw [squareLattice_adj_iff] at ha
    rcases ha with hh | hv
    · rcases hh.1 with hx | hx <;> omega
    · rcases hv.2 with hy | hy <;> omega⟩

instance : DecidableRel parafermionicCoverGraph.Adj := by
  intro u v
  unfold parafermionicCoverGraph
  infer_instance

theorem parafermionicCoverGraph_adj_iff_cases (u v : ParafermionicCoverVertex) :
    parafermionicCoverGraph.Adj u v ↔ parafermionicCoverAdjCases u v := by
  rcases u with ⟨⟨x, y⟩, k⟩
  rcases v with ⟨⟨x', y'⟩, k'⟩
  change (squareLattice.Adj (x, y) (x', y') ∧
      k' = k + parafermionicCoverSheetShift (x, y) (x', y')) ↔
    parafermionicCoverAdjCases ((x, y), k) ((x', y'), k')
  rw [squareLattice_adj_iff]
  unfold parafermionicCoverAdjCases parafermionicCoverSheetShift
  dsimp only
  constructor
  · rintro ⟨hbase, hsheet⟩
    rcases hbase with ⟨hx | hx, hy⟩ | ⟨hx, hy | hy⟩
    · split_ifs at hsheet <;> omega
    · split_ifs at hsheet <;> omega
    · have hk : k = k' := by simp_all; omega
      exact Or.inl ⟨hx, hy, hk⟩
    · have hk : k = k' := by simp_all; omega
      exact Or.inr (Or.inl ⟨hx, hy, hk⟩)
  · intro h
    rcases h with h | h | h | h | h | h | h | h
    · split_ifs <;> omega
    · split_ifs <;> omega
    · split_ifs <;> omega
    · split_ifs <;> omega
    · split_ifs <;> omega
    · split_ifs <;> omega
    · split_ifs <;> omega
    · split_ifs <;> omega

/-- The canonical height of the unique lift of a base neighbor from a given vertex. -/
def parafermionicCoverNeighborLift (u : ParafermionicCoverVertex) (v : LatticeVertex) :
    ParafermionicCoverVertex := (v, u.2 + parafermionicCoverSheetShift u.1 v)

theorem parafermionicCoverNeighborLift_adj (u : ParafermionicCoverVertex)
    (v : LatticeVertex) (h : squareLattice.Adj u.1 v) :
    parafermionicCoverGraph.Adj u (parafermionicCoverNeighborLift u v) := by
  refine ⟨h, ?_⟩
  rfl

theorem parafermionicCover_sheetShift_of_adj {u v : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v) :
    v.2 = u.2 + parafermionicCoverSheetShift u.1 v.1 := h.2

theorem parafermionicCoverNeighborLift_unique (u : ParafermionicCoverVertex)
    (v : LatticeVertex) (w : ParafermionicCoverVertex)
    (hw : w.1 = v) (hadj : parafermionicCoverGraph.Adj u w) :
    w = parafermionicCoverNeighborLift u v := by
  rcases w with ⟨p, k⟩
  simp only at hw
  subst p
  have hk := parafermionicCover_sheetShift_of_adj hadj
  exact Prod.ext rfl hk

/-- The finite vertex set `U_n` from the source, including every sheet in `[-n^5,n^5]`. -/
def parafermionicCoverBoxFinset (n : ℕ) : Finset ParafermionicCoverVertex :=
  latticeBox (0, 0) n ×ˢ Finset.Icc (-(n ^ 5 : ℕ) : ℤ) (n ^ 5 : ℤ)

abbrev parafermionicCoverBoxVertices (n : ℕ) : Set ParafermionicCoverVertex :=
  parafermionicCoverBoxFinset n

theorem parafermionicCoverBoxVertices_mem (n : ℕ) (v : ParafermionicCoverVertex) :
    v ∈ parafermionicCoverBoxVertices n ↔
      -(n : ℤ) ≤ v.1.1 ∧ v.1.1 ≤ (n : ℤ) ∧
      -(n : ℤ) ≤ v.1.2 ∧ v.1.2 ≤ (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ v.2 ∧ v.2 ≤ ((n ^ 5 : ℕ) : ℤ) := by
  change v ∈ (parafermionicCoverBoxFinset n : Set _) ↔ _
  simp [parafermionicCoverBoxFinset, mem_latticeBox, Nat.cast_pow]
  omega

theorem parafermionicCoverBoxFinset_card (n : ℕ) :
    (parafermionicCoverBoxFinset n).card = (2 * n + 1) ^ 2 * (2 * n ^ 5 + 1) := by
  rw [parafermionicCoverBoxFinset, Finset.card_product, card_latticeBox, Int.card_Icc]
  have hval : (n ^ 5 : ℤ) + 1 - (-(n ^ 5 : ℕ) : ℤ) = ((2 * n ^ 5 + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hval, Int.toNat_natCast]

abbrev ParafermionicCoverBoxVertex (n : ℕ) := ↥(parafermionicCoverBoxFinset n)

def parafermionicCoverBoxGraph (n : ℕ) : SimpleGraph (ParafermionicCoverBoxVertex n) :=
  parafermionicCoverGraph.induce (parafermionicCoverBoxVertices n)

instance parafermionicCoverBoxGraphDecidableRel (n : ℕ) :
    DecidableRel (parafermionicCoverBoxGraph n).Adj := by
  unfold parafermionicCoverBoxGraph
  infer_instance

theorem parafermionicCoverBoxVertex_card (n : ℕ) :
    Fintype.card (ParafermionicCoverBoxVertex n) = (2 * n + 1) ^ 2 * (2 * n ^ 5 + 1) := by
  simpa [ParafermionicCoverBoxVertex, parafermionicCoverBoxVertices,
    Fintype.card_coe] using parafermionicCoverBoxFinset_card n

end PottsDiscontinuity.TorusTopology.Planar
