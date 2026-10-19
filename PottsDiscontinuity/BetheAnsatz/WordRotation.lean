module

public import PottsDiscontinuity.BetheAnsatz.GapReindex
public import PottsDiscontinuity.BetheAnsatz.WordCancellation

/-!
# Moving a boundary ML edge to an ordinary edge

Rotate both the word and the lifted coordinates. The amplitude and plane-wave
boundary phases cancel by the exact toroidal identity already proved.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Coordinates selected by a word. -/
def wordPositions {n : ℕ} (N : ℕ) (x : Fin (n + 1) → ℤ) (w : Fin (n + 1) → Bool) :
    Fin (n + 1) → ℤ :=
  fun k => if w k then cyclicPredecessorPositions N x k else x k

/-- Rotating the word and coordinates rotates the selected endpoint tuple. -/
theorem wordPositions_rotate {n : ℕ} (N : ℕ) (x : Fin (n + 1) → ℤ)
    (w : Fin (n + 1) → Bool) :
    wordPositions N (cyclicSuccessorPositions N x) (fun k => w (finRotate (n + 1) k)) =
      cyclicSuccessorPositions N (wordPositions N x w) := by
  funext k
  simp only [wordPositions, cyclicPredecessor_successor, cyclicSuccessorPositions]
  by_cases hw : w (finRotate (n + 1) k) = true
  · simp only [hw, ↓reduceIte]
    exact (congrFun (cyclicSuccessor_predecessor N x) k).symm
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]

/-- The cyclic edge product is unchanged by a simultaneous cyclic reindexing. -/
theorem wordCoefficient_rotate {n : ℕ} (c : ℝ) (p : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) :
    wordCoefficient c p (σ * finRotate (n + 1)) (fun k => w (finRotate (n + 1) k)) =
      wordCoefficient c p σ w := by
  unfold wordCoefficient
  simpa only [Equiv.Perm.mul_apply, wordEdgeFactor] using Equiv.prod_comp (finRotate (n + 1))
    (fun k => wordEdgeFactor c p σ w k)

/-- The full word term obeys the toroidal rotation, including its boundary phase. -/
theorem wordTerm_rotate {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) :
    wordTerm (N := N) c (cyclicSuccessorPositions N x) p (σ * finRotate (n + 1))
      (fun k => w (finRotate (n + 1) k)) = wordTerm (N := N) c x p σ w := by
  have h := amplitude_planeWave_rotate (anisotropy_lt_neg_one hc) p hBE σ
    (wordPositions N (cyclicSuccessorPositions N x) (fun k => w (finRotate (n + 1) k)))
  rw [wordPositions_rotate, cyclicPredecessor_successor] at h
  unfold wordTerm
  rw [wordCoefficient_rotate]
  change _ * _ * planeWave p (σ * finRotate (n + 1))
      (wordPositions N (cyclicSuccessorPositions N x) (fun k => w (finRotate (n + 1) k))) =
    _ * _ * planeWave p σ (wordPositions N x w)
  rw [wordPositions_rotate]
  linear_combination wordCoefficient c p σ w * h

/-- The permutation sum of a word equals that of its cyclic rotation. -/
theorem sum_wordTerm_rotate {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hBE : BetheEquations N (anisotropy c) p) (w : Fin (n + 1) → Bool) :
    (∑ σ, wordTerm (N := N) c (cyclicSuccessorPositions N x) p σ
      (fun k => w (finRotate (n + 1) k))) = ∑ σ, wordTerm (N := N) c x p σ w := by
  calc
    _ = ∑ σ, wordTerm (N := N) c (cyclicSuccessorPositions N x) p
        (σ * finRotate (n + 1)) (fun k => w (finRotate (n + 1) k)) :=
      (Equiv.sum_comp (Equiv.mulRight (finRotate (n + 1))) _).symm
    _ = _ := Finset.sum_congr rfl fun σ _ => wordTerm_rotate hc x p hBE σ w

/-- The boundary ML edge cancels by moving it to the last ordinary edge. -/
theorem sum_wordTerm_eq_zero_of_boundaryML {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 2) → ℤ) (p : Fin (n + 2) → ℝ) (hp : ∀ j, z (p j) ≠ 1)
    (hBE : BetheEquations N (anisotropy c) p) (w : Fin (n + 2) → Bool)
    (ha : w (Fin.last (n + 1)) = false) (hb : w 0 = true) :
    (∑ σ, wordTerm (N := N) c x p σ w) = 0 := by
  rw [← sum_wordTerm_rotate hc x p hBE w]
  apply sum_wordTerm_eq_zero_of_adjacentML hc (cyclicSuccessorPositions N x) p hp
    (fun k => w (finRotate (n + 2) k)) (Fin.last n)
  · have hr : finRotate (n + 2) (Fin.last n).castSucc = (Fin.last n).succ :=
      finRotate_of_lt (Fin.last n).isLt
    simpa only [hr, Fin.succ_last] using ha
  · simpa only [Fin.succ_last, finRotate_last] using hb

end PottsDiscontinuity.BetheAnsatz
