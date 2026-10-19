module

public import PottsDiscontinuity.BetheAnsatz.Conventions
public import PottsDiscontinuity.BetheAnsatz.GapWeights
public import PottsDiscontinuity.BetheAnsatz.InterlacingCoordinates
public import PottsDiscontinuity.BetheAnsatz.TransferAction

/-!
# The actual transfer action as the cyclic gap sum

Companion paper, Corollary `cor:expressionRsi`. Both ordinary orientations are
reindexed with their actual weights; modulo-N distinctness is part of the finite sum.
-/

@[expose] public section

open Finset Complex Matrix Classical

namespace PottsDiscontinuity.BetheAnsatz

open SixVertex

/-- The finite gap reindexing, directly over the actual row states. -/
theorem sum_distinctGapTuples_eq_sum_states {N n : ℕ} (x : State N (n + 1))
    (F : (Fin (n + 1) → ℤ) → ℂ) :
    (∑ y ∈ distinctGapTuples N (positions x), F y) =
      (∑ y : State N (n + 1), if InterlacedLE y.1 x.1 then F (positions y) else 0) +
      ∑ y : State N (n + 1), if InterlacedLE x.1 y.1 then
        F (cyclicPredecessorPositions N (positions y)) else 0 := by
  rw [sum_distinctGapTuples_reindex (positions_mem_orderedTuples x)]
  congr 1
  · rw [Finset.sum_filter, ← sum_states_eq_sum_orderedTuples (N := N)]
    apply Finset.sum_congr rfl
    intro y _
    simp only [← interlacedLE_iff_positions_mem_gapTuples]
  · rw [Finset.sum_filter, ← sum_states_eq_sum_orderedTuples (N := N)]
    apply Finset.sum_congr rfl
    intro y _
    simp only [← interlacedLE_iff_shift_positions_mem_gapTuples]

/-- The coordinate wave is invariant under the lifted cyclic predecessor shift. -/
theorem coordinateWave_cyclicPredecessor {N n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N Δ p) (y : Fin (n + 1) → ℤ) :
    coordinateWave Δ p y = coordinateWave Δ p (cyclicPredecessorPositions N y) := by
  simpa only [coordinateWave, mul_one] using
    toroidal_change_of_variables hΔ p hBE y (fun _ => 1)

/-- Expanding the amplitude-weighted finite gap sums gives the coordinate wave summand. -/
theorem sum_amplitude_cyclicGapSum {N n : ℕ} (c Δ : ℝ) (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) :
    (∑ σ, amplitude Δ p σ * cyclicGapSum c N x p σ) =
      ∑ y ∈ distinctGapTuples N x, gapWeight c N x y * coordinateWave Δ p y := by
  simp only [cyclicGapSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [coordinateWave, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

/-- Corollary `cor:expressionRsi`: the gap sum is the action of the actual transfer matrix.
No relation between c and Δ is needed for this combinatorial/toroidal step. -/
theorem transfer_betheVector_eq_cyclicGapSum {N n : ℕ} (c : ℝ) {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N Δ p) (x : State N (n + 1)) :
    ((transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ betheVector Δ p) x.1 =
      ∑ σ, amplitude Δ p σ * cyclicGapSum c N (positions x) p σ := by
  rw [sum_amplitude_cyclicGapSum,
    sum_distinctGapTuples_eq_sum_states x (fun y => gapWeight c N (positions x) y * coordinateWave Δ p y)]
  change ((transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ extendByZero (blockWave Δ p)) x.1 = _
  rw [mulVec_extendByZero_apply, Matrix.mulVec, dotProduct, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  change (transferMatrix N c x.1 y.1 : ℂ) * coordinateWave Δ p (positions y) = _
  rw [transferMatrix_eq_two_orientations]
  by_cases hl : InterlacedLE y.1 x.1 <;> by_cases hu : InterlacedLE x.1 y.1
  · have hgl := (interlacedLE_iff_positions_mem_gapTuples x y).mp hl
    have hgu := (interlacedLE_iff_shift_positions_mem_gapTuples x y).mp hu
    rw [gapWeight_positions c x y hgl, gapWeight_shift_positions c x y hgu,
      ← coordinateWave_cyclicPredecessor hΔ p hBE (positions y)]
    simp [hl, hu, add_mul]
  · have hgl := (interlacedLE_iff_positions_mem_gapTuples x y).mp hl
    rw [ite_eq_left hl, ite_eq_right hu, gapWeight_positions c x y hgl]
    simp [hl, hu]
  · have hgu := (interlacedLE_iff_shift_positions_mem_gapTuples x y).mp hu
    rw [ite_eq_right hl, ite_eq_left hu, gapWeight_shift_positions c x y hgu,
      ← coordinateWave_cyclicPredecessor hΔ p hBE (positions y)]
    simp [hl, hu]
  · simp [hl, hu]

end PottsDiscontinuity.BetheAnsatz
