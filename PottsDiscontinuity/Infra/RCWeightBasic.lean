module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.RCWeight

/-!
# Basic facts about the finite-volume random-cluster weights

On the source parameter range `p ∈ [0, 1]`, `q > 0`, every weight is nonnegative and the partition
function is positive.

Provenance: proofs first written by an independent statement reviewer in a transient check file
(2026-10-18) and moved here unchanged apart from layout.
-/

@[expose] public section

namespace PottsDiscontinuity

theorem rcWeight_nonneg (V : Finset (ℤ × ℤ)) (p : Set.Icc (0:ℝ) 1) (q : Set.Ioi (0:ℝ)) (i : Fin 2)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    0 < q.1 → 0 ≤ rcWeight V p q i ω := by
  intro hq
  unfold rcWeight
  have h0 : (0:ℝ) ≤ p.1 := p.2.1
  have h1 : (0:ℝ) ≤ 1 - p.1 := by linarith [p.2.2]
  positivity

open Classical in
theorem rcWeight_denominator_pos (V : Finset (ℤ × ℤ)) (p : Set.Icc (0:ℝ) 1) (q : Set.Ioi (0:ℝ))
    (i : Fin 2) :
    0 < ∑ ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool, rcWeight V p q i ω := by
  have hq : (0:ℝ) < q.1 := q.2
  have h0 : (0:ℝ) ≤ p.1 := p.2.1
  have h1 : (0:ℝ) ≤ 1 - p.1 := by linarith [p.2.2]
  have hnn : ∀ ω, 0 ≤ rcWeight V p q i ω := fun ω => rcWeight_nonneg V p q i ω hq
  rcases lt_or_eq_of_le p.2.2 with hp | hp
  · -- p < 1 : all-closed configuration has positive weight
    have hpos : 0 < rcWeight V p q i (fun _ => false) := by
      unfold rcWeight
      have e1 : Nat.card {e : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet //
          (fun _ => false) e = true} = 0 := by
        rw [Nat.card_eq_zero]; left; exact ⟨fun ⟨_, h⟩ => by simp at h⟩
      rw [e1]
      have : 0 < 1 - p.1 := by linarith
      positivity
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun ω _ => hnn ω) (Finset.mem_univ _))
  · -- p = 1 : all-open configuration has positive weight
    have hpos : 0 < rcWeight V p q i (fun _ => true) := by
      unfold rcWeight
      have e1 : Nat.card {e : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet //
          (fun _ => true) e = false} = 0 := by
        rw [Nat.card_eq_zero]; left; exact ⟨fun ⟨_, h⟩ => by simp at h⟩
      rw [e1, hp]
      positivity
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun ω _ => hnn ω) (Finset.mem_univ _))

end PottsDiscontinuity
