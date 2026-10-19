module

public import Mathlib

/-!
# Cells, medial vertices and the local incidence of the rotated lattice

Planar bookkeeping for the diamond random-cluster lattice.  A *cell* is an integer
point `(x, y)`; it is *primal* when `x + y` is even and *dual* (odd) otherwise.  A
*medial vertex* `m = (a, b)` is the corner shared by the four cells
`NE = (a,b)`, `NW = (a-1,b)`, `SW = (a-1,b-1)`, `SE = (a,b-1)`.  Exactly one pair of
diagonal cells among them is primal (these are the endpoints of the primal edge at `m`)
and the other pair is odd (the endpoints of the crossing dual edge at `m`).  The same
conventions as `Torus.faceEndpointRaw` (`Torus/DiamondGraph.lean`) are used: when
`checker m` holds the primal edge joins `NE` and `SW`.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

/-- A cell of the rotated lattice. -/
abbrev Cell := ℤ × ℤ

/-- A cell is primal when its coordinate sum is even. -/
def IsPrimal (c : Cell) : Prop := (c.1 + c.2) % 2 = 0

instance (c : Cell) : Decidable (IsPrimal c) := by
  unfold IsPrimal; infer_instance

/-- Endpoints of the primal edge sitting at the medial vertex `m`. -/
def primalEnds (m : Cell) : Cell × Cell :=
  if (m.1 + m.2) % 2 = 0 then (m, (m.1 - 1, m.2 - 1))
  else ((m.1 - 1, m.2), (m.1, m.2 - 1))

/-- Endpoints of the dual edge sitting at the medial vertex `m`. -/
def dualEnds (m : Cell) : Cell × Cell :=
  if (m.1 + m.2) % 2 = 0 then ((m.1 - 1, m.2), (m.1, m.2 - 1))
  else (m, (m.1 - 1, m.2 - 1))

theorem primalEnds_fst_primal (m : Cell) : IsPrimal (primalEnds m).1 := by
  unfold primalEnds IsPrimal; split_ifs with h <;> dsimp only <;> omega

theorem primalEnds_snd_primal (m : Cell) : IsPrimal (primalEnds m).2 := by
  unfold primalEnds IsPrimal; split_ifs with h <;> dsimp only <;> omega

theorem dualEnds_fst_not_primal (m : Cell) : ¬ IsPrimal (dualEnds m).1 := by
  unfold dualEnds IsPrimal; split_ifs with h <;> dsimp only <;> omega

theorem dualEnds_snd_not_primal (m : Cell) : ¬ IsPrimal (dualEnds m).2 := by
  unfold dualEnds IsPrimal; split_ifs with h <;> dsimp only <;> omega

theorem primalEnds_ne (m : Cell) : (primalEnds m).1 ≠ (primalEnds m).2 := by
  unfold primalEnds; split_ifs with h <;> simp only [ne_eq, Prod.ext_iff] <;> omega

theorem dualEnds_ne (m : Cell) : (dualEnds m).1 ≠ (dualEnds m).2 := by
  unfold dualEnds; split_ifs with h <;> simp only [ne_eq, Prod.ext_iff] <;> omega

/-- The four corners (medial vertices) of the unit square attached to a cell. -/
def corners (c : Cell) : Finset Cell :=
  {c, (c.1 + 1, c.2), (c.1, c.2 + 1), (c.1 + 1, c.2 + 1)}

/-- The cell `c`, primal or odd, is an endpoint of the primal edge at `m` iff `m` is a
corner of `c` (for primal `c`). -/
theorem mem_primalEnds_iff (c m : Cell) (hc : IsPrimal c) :
    (c = (primalEnds m).1 ∨ c = (primalEnds m).2) ↔ m ∈ corners c := by
  unfold primalEnds corners IsPrimal at *
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
  split_ifs with h <;> dsimp only <;> omega

theorem mem_dualEnds_iff (z m : Cell) (hz : ¬ IsPrimal z) :
    (z = (dualEnds m).1 ∨ z = (dualEnds m).2) ↔ m ∈ corners z := by
  unfold dualEnds corners IsPrimal at *
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
  split_ifs with h <;> dsimp only <;> omega

/-- Distinct medial vertices carry distinct primal edges. -/
theorem primalEnds_inj {m m' : Cell}
    (h : primalEnds m = primalEnds m' ∨ primalEnds m = (primalEnds m').swap) : m = m' := by
  unfold primalEnds at h
  split_ifs at h <;> simp only [Prod.swap, Prod.ext_iff] at h <;> (rw [Prod.ext_iff]; omega)

theorem dualEnds_inj {m m' : Cell}
    (h : dualEnds m = dualEnds m' ∨ dualEnds m = (dualEnds m').swap) : m = m' := by
  unfold dualEnds at h
  split_ifs at h <;> simp only [Prod.swap, Prod.ext_iff] at h <;> (rw [Prod.ext_iff]; omega)

end PottsDiscontinuity.TorusCrossing
