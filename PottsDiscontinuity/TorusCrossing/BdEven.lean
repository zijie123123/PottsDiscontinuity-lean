module

public import PottsDiscontinuity.TorusCrossing.Cut

/-!
# Parity of boundary edges at primal cells

Around a primal cell `c` the four crossing dual edges form a 4-cycle through the odd cells
`W, S, E, N`.  Hence the number of edges separating two classes of odd cells is even at every
cell having all four edges inside the board; at a cell of the bottom (or top) row only two edges are
inside, and the parity is the difference of the classes of `W` and `E`.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

theorem dualEnds_corner1 (c : Cell) (hc : IsPrimal c) :
    dualEnds c = ((c.1 - 1, c.2), (c.1, c.2 - 1)) := by
  unfold dualEnds; unfold IsPrimal at hc
  rw [ite_eq_left (by omega)]

theorem dualEnds_corner2 (c : Cell) (hc : IsPrimal c) :
    dualEnds (c.1 + 1, c.2) = ((c.1 + 1, c.2), (c.1, c.2 - 1)) := by
  unfold dualEnds; unfold IsPrimal at hc
  rw [ite_eq_right (by dsimp only; omega)]
  simp

theorem dualEnds_corner3 (c : Cell) (hc : IsPrimal c) :
    dualEnds (c.1, c.2 + 1) = ((c.1, c.2 + 1), (c.1 - 1, c.2)) := by
  unfold dualEnds; unfold IsPrimal at hc
  rw [ite_eq_right (by dsimp only; omega)]
  simp

theorem dualEnds_corner4 (c : Cell) (hc : IsPrimal c) :
    dualEnds (c.1 + 1, c.2 + 1) = ((c.1, c.2 + 1), (c.1 + 1, c.2)) := by
  unfold dualEnds; unfold IsPrimal at hc
  rw [ite_eq_left (by dsimp only; omega)]
  simp

/-- Separation of odd cells by a label. -/
def IsSep (ℓ : Cell → Prop) (m : Cell) : Prop := ℓ (dualEnds m).1 ↔ ¬ ℓ (dualEnds m).2

open Rect in
/-- Parity of the number of separating edges around a primal cell strictly inside the side
columns, when the labels on the bottom and top rows are constant. -/
theorem sep_deg_even (R : Rect) (hh : 0 < R.h) (ℓ : Cell → Prop) (c : Cell) (hc : IsPrimal c)
    (hx1 : R.x0 < c.1) (hx2 : c.1 < R.x0 + R.w) (hcy1 : R.y0 ≤ c.2) (hcy2 : c.2 ≤ R.y0 + R.h)
    (hbot : c.2 = R.y0 → (ℓ (c.1 - 1, c.2) ↔ ℓ (c.1 + 1, c.2)))
    (htop : c.2 = R.y0 + R.h → (ℓ (c.1 - 1, c.2) ↔ ℓ (c.1 + 1, c.2))) :
    Even (((corners c).filter (fun m => m ∈ R.inner ∧ IsSep ℓ m)).card) := by
  have hh' : (0 : ℤ) < R.h := by exact_mod_cast hh
  rw [card_filter_corners]
  unfold IsSep
  rw [dualEnds_corner1 c hc, dualEnds_corner2 c hc, dualEnds_corner3 c hc, dualEnds_corner4 c hc]
  simp only [mem_inner]
  by_cases hb : c.2 = R.y0
  · have e1 : ¬ (R.x0 + 1 ≤ c.1 ∧ c.1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h) := by omega
    have e2 : ¬ (R.x0 + 1 ≤ c.1 + 1 ∧ c.1 + 1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h) := by omega
    have e3 : (R.x0 + 1 ≤ c.1 ∧ c.1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2 + 1 ∧ c.2 + 1 ≤ R.y0 + R.h) := by omega
    have e4 : (R.x0 + 1 ≤ c.1 + 1 ∧ c.1 + 1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2 + 1 ∧ c.2 + 1 ≤ R.y0 + R.h) := by omega
    simp only [e3, e4, true_and]
    have := hbot hb
    by_cases a : ℓ (c.1 - 1, c.2) <;> by_cases e : ℓ (c.1 + 1, c.2) <;> by_cases d : ℓ (c.1, c.2 + 1) <;>
      simp_all
  · by_cases ht : c.2 = R.y0 + R.h
    · have e1 : (R.x0 + 1 ≤ c.1 ∧ c.1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h) := by omega
      have e2 : (R.x0 + 1 ≤ c.1 + 1 ∧ c.1 + 1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h) := by omega
      have e3 : ¬ (R.x0 + 1 ≤ c.1 ∧ c.1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2 + 1 ∧ c.2 + 1 ≤ R.y0 + R.h) := by omega
      have e4 : ¬ (R.x0 + 1 ≤ c.1 + 1 ∧ c.1 + 1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2 + 1 ∧ c.2 + 1 ≤ R.y0 + R.h) := by omega
      simp only [e1, e2, true_and]
      have := htop ht
      by_cases a : ℓ (c.1 - 1, c.2) <;> by_cases s : ℓ (c.1, c.2 - 1) <;> by_cases e : ℓ (c.1 + 1, c.2) <;>
        simp_all
    · have e1 : (R.x0 + 1 ≤ c.1 ∧ c.1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h) := by omega
      have e2 : (R.x0 + 1 ≤ c.1 + 1 ∧ c.1 + 1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2 ∧ c.2 ≤ R.y0 + R.h) := by omega
      have e3 : (R.x0 + 1 ≤ c.1 ∧ c.1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2 + 1 ∧ c.2 + 1 ≤ R.y0 + R.h) := by omega
      have e4 : (R.x0 + 1 ≤ c.1 + 1 ∧ c.1 + 1 ≤ R.x0 + R.w ∧ R.y0 + 1 ≤ c.2 + 1 ∧ c.2 + 1 ≤ R.y0 + R.h) := by omega
      simp only [e1, e2, e3, true_and]
      by_cases a : ℓ (c.1 - 1, c.2) <;> by_cases b : ℓ (c.1, c.2 - 1) <;>
        by_cases e : ℓ (c.1 + 1, c.2) <;> by_cases d : ℓ (c.1, c.2 + 1) <;>
        simp [a, b, e, d] <;> decide

end PottsDiscontinuity.TorusCrossing
