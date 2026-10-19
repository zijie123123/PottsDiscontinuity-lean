module

public import PottsDiscontinuity.BetheAnsatz.OrderedPositions

/-!
# Coordinate conditions for the two transfer-action orientations

The inequalities here use the unique increasing integer coordinates of the actual states.
They supply the ordinary-coordinate side of the cyclic gap reindexing.
-/

@[expose] public section

open Finset Classical

namespace PottsDiscontinuity.BetheAnsatz

open SixVertex

theorem interlacedLE_positions_iff {N n : ℕ} (x y : State N n) :
    InterlacedLE x.1 y.1 ↔
      (∀ k, positions x k ≤ positions y k) ∧
      ∀ k l : Fin n, k.val + 1 = l.val → positions y k ≤ positions x l := by
  rcases x with ⟨s, hs⟩
  rcases y with ⟨t, ht⟩
  subst n
  change (∃ h : s.card = t.card,
    (∀ k : Fin s.card, s.orderEmbOfFin rfl k ≤ t.orderEmbOfFin h.symm k) ∧
    ∀ k l : Fin s.card, k.val + 1 = l.val → t.orderEmbOfFin h.symm k ≤ s.orderEmbOfFin rfl l) ↔ _
  simp only [positions]
  constructor
  · rintro ⟨h, h1, h2⟩
    refine ⟨fun k => ?_, fun k l hkl => ?_⟩
    · exact_mod_cast (show (s.orderEmbOfFin rfl k).val ≤ (t.orderEmbOfFin ht k).val from h1 k)
    · exact_mod_cast (show (t.orderEmbOfFin ht k).val ≤ (s.orderEmbOfFin rfl l).val from h2 k l hkl)
  · rintro ⟨h1, h2⟩
    refine ⟨ht.symm, fun k => ?_, fun k l hkl => ?_⟩
    · change (s.orderEmbOfFin rfl k).val ≤ (t.orderEmbOfFin ht k).val
      exact_mod_cast h1 k
    · change (t.orderEmbOfFin ht k).val ≤ (s.orderEmbOfFin rfl l).val
      exact_mod_cast h2 k l hkl

theorem interlacedLE_positions_succ_iff {N n : ℕ} (x y : State N (n + 1)) :
    InterlacedLE x.1 y.1 ↔
      (∀ k, positions x k ≤ positions y k) ∧
      ∀ k : Fin n, positions y k.castSucc ≤ positions x k.succ := by
  rw [interlacedLE_positions_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun k => h2 k.castSucc k.succ rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i j hij => ?_⟩
    have hi : i.val < n := by have hj := j.isLt; omega
    let k : Fin n := ⟨i.val, hi⟩
    have hik : k.castSucc = i := Fin.ext rfl
    have hjk : k.succ = j := Fin.ext hij
    simpa only [hik, hjk] using h2 k

/-- In the ordinary row, the lower interlacing orientation is exactly the gap inequalities. -/
theorem ordered_mem_gapTuples_iff {N n : ℕ} {x y : Fin (n + 1) → ℤ}
    (hx : x ∈ orderedTuples N (n + 1)) (hy : y ∈ orderedTuples N (n + 1)) :
    y ∈ gapTuples N x ↔ (∀ k, y k ≤ x k) ∧ ∀ k : Fin n, x k.castSucc ≤ y k.succ := by
  constructor
  · intro hg
    refine ⟨fun k => ((mem_gapTuples.mp hg) k).2, fun k => ?_⟩
    have h := ((mem_gapTuples.mp hg) k.succ).1
    simpa only [cyclicPredecessorPositions_succ] using h
  · rintro ⟨hu, hl⟩
    apply mem_gapTuples.mpr
    intro k
    refine ⟨?_, hu k⟩
    induction k using Fin.cases with
    | zero =>
      rw [cyclicPredecessorPositions_zero]
      have hxlast := ((mem_orderedTuples.mp hx).1 (Fin.last n)).2
      have hyzero := ((mem_orderedTuples.mp hy).1 0).1
      omega
    | succ k =>
      rw [cyclicPredecessorPositions_succ]
      exact hl k

theorem interlacedLE_iff_positions_mem_gapTuples {N n : ℕ} (x y : State N (n + 1)) :
    InterlacedLE y.1 x.1 ↔ positions y ∈ gapTuples N (positions x) := by
  rw [interlacedLE_positions_succ_iff,
    ordered_mem_gapTuples_iff (positions_mem_orderedTuples x) (positions_mem_orderedTuples y)]

/-- Applying the same predecessor shift to both tuples preserves pointwise order. -/
theorem cyclicPredecessorPositions_le_iff {N n : ℕ} (x y : Fin (n + 1) → ℤ) :
    (∀ k, cyclicPredecessorPositions N x k ≤ cyclicPredecessorPositions N y k) ↔
      ∀ k, x k ≤ y k := by
  constructor
  · intro h k
    have h' := h (finRotate (n + 1) k)
    simp only [cyclicPredecessorPositions, Equiv.symm_apply_apply] at h'
    omega
  · intro h k
    unfold cyclicPredecessorPositions
    exact sub_le_sub_right (h _) _

/-- The upper interlacing orientation becomes a gap tuple after moving the last point back N. -/
theorem ordered_shift_mem_gapTuples_iff {N n : ℕ} {x y : Fin (n + 1) → ℤ}
    (hx : x ∈ orderedTuples N (n + 1)) (hy : y ∈ orderedTuples N (n + 1)) :
    cyclicPredecessorPositions N y ∈ gapTuples N x ↔
      (∀ k, x k ≤ y k) ∧ ∀ k : Fin n, y k.castSucc ≤ x k.succ := by
  rw [mem_gapTuples]
  constructor
  · intro h
    refine ⟨cyclicPredecessorPositions_le_iff x y |>.mp (fun k => (h k).1), fun k => ?_⟩
    have h' := (h k.succ).2
    simpa only [cyclicPredecessorPositions_succ] using h'
  · rintro ⟨hl, hu⟩
    have hl' := (cyclicPredecessorPositions_le_iff (N := N) x y).mpr hl
    intro k
    refine ⟨hl' k, ?_⟩
    induction k using Fin.cases with
    | zero =>
      rw [cyclicPredecessorPositions_zero]
      have hylast := ((mem_orderedTuples.mp hy).1 (Fin.last n)).2
      have hxzero := ((mem_orderedTuples.mp hx).1 0).1
      omega
    | succ k =>
      rw [cyclicPredecessorPositions_succ]
      exact hu k

theorem interlacedLE_iff_shift_positions_mem_gapTuples {N n : ℕ} (x y : State N (n + 1)) :
    InterlacedLE x.1 y.1 ↔
      cyclicPredecessorPositions N (positions y) ∈ gapTuples N (positions x) := by
  rw [interlacedLE_positions_succ_iff,
    ordered_shift_mem_gapTuples_iff (positions_mem_orderedTuples x) (positions_mem_orderedTuples y)]

end PottsDiscontinuity.BetheAnsatz
