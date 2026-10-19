module

public import PottsDiscontinuity.Bethe.AsymptoticPartition
public import PottsDiscontinuity.Bethe.Theorem23Counting

/-! # Exact counting increments and cell mean values for Bethe solutions -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem betheCountingFunction_cell_increment {Δ : ℝ} {N k : ℕ} (hN : 0 < N)
    (p : Fin (k + 1) → ℝ) (hs : 2 * (k + 1) ≤ N)
    (hBE : DiscreteBetheEquation Δ N (k + 1) p) (j : Fin (k + 2)) :
    betheCountingFunction Δ N (k + 1) p (rootPartitionPoint (k + 1) p (by omega) j.succ) -
      betheCountingFunction Δ N (k + 1) p (rootPartitionPoint (k + 1) p (by omega) j.castSucc) =
        rootGapMultiplicity N (k + 1) hs j / (N : ℝ) := by
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  let f := betheCountingFunction Δ N (k + 1) p
  have hroot (i : Fin (k + 1)) : f (p i) = discreteBetheIndex (k + 1) i / (N : ℝ) :=
    betheCountingFunction_root_value hN p hBE i
  have hcast : ((N + 1 - 2 * (k + 1) : ℕ) : ℝ) = (N : ℝ) + 1 - 2 * ((k : ℝ) + 1) := by
    rw [Nat.cast_sub (by omega : 2 * (k + 1) ≤ N + 1)]
    push_cast
    ring
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    have ha : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).castSucc =
        p (Fin.last k) - 2 * Real.pi := by
      convert rootPartitionPoint_zero p (by omega) using 1 <;> congr 1
    have hb : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).succ = p 0 := by
      convert rootPartitionPoint_root p (by omega) (0 : Fin (k + 1)) using 1
      congr 1
    have hperiod := betheCountingFunction_period (Δ := Δ) hN p (p (Fin.last k) - 2 * Real.pi)
    rw [show p (Fin.last k) - 2 * Real.pi + 2 * Real.pi = p (Fin.last k) by ring] at hperiod
    have hminus : f (p (Fin.last k) - 2 * Real.pi) =
        f (p (Fin.last k)) - ((N : ℝ) - (k + 1 : ℕ)) / (N : ℝ) := by linarith only [hperiod]
    change f _ - f _ = _
    rw [ha, hb, hminus, hroot, hroot]
    simp only [rootGapMultiplicity, Fin.val_zero, true_or, ite_true, hcast,
      discreteBetheIndex, Fin.val_last, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
    field_simp [hNc]
    ring
  · by_cases hjlast : j.val = k + 1
    · have hj : j = Fin.last (k + 1) := Fin.ext hjlast
      subst j
      have ha : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).castSucc =
          p (Fin.last k) := by
        convert rootPartitionPoint_root p (by omega) (Fin.last k) using 1
        congr 1
      have hb : rootPartitionPoint (k + 1) p (by omega) (Fin.last (k + 1)).succ =
          p 0 + 2 * Real.pi := by
        convert rootPartitionPoint_end p (by omega) using 1 <;> congr 1
      have hperiod : f (p 0 + 2 * Real.pi) =
          f (p 0) + ((N : ℝ) - (k + 1 : ℕ)) / (N : ℝ) :=
        betheCountingFunction_period (Δ := Δ) hN p (p 0)
      change f _ - f _ = _
      rw [ha, hb, hperiod, hroot, hroot]
      simp only [rootGapMultiplicity, Fin.val_last, or_true, ite_true, hcast,
        discreteBetheIndex, Fin.val_zero, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
      field_simp [hNc]
      ring
    · let lo : Fin (k + 1) := ⟨j.val - 1, by omega⟩
      let hi : Fin (k + 1) := ⟨j.val, by omega⟩
      have ha : rootPartitionPoint (k + 1) p (by omega) j.castSucc = p lo := by
        convert rootPartitionPoint_root p (by omega) lo using 1
        congr 1
        apply Fin.ext
        dsimp [lo]
        omega
      have hb : rootPartitionPoint (k + 1) p (by omega) j.succ = p hi := by
        convert rootPartitionPoint_root p (by omega) hi using 1
        congr 1
      have hm : rootGapMultiplicity N (k + 1) hs j = 1 := by
        simp only [rootGapMultiplicity, ite_eq_right (not_or.mpr ⟨hj0, hjlast⟩)]
      have hindex : discreteBetheIndex (k + 1) hi - discreteBetheIndex (k + 1) lo = 1 := by
        dsimp [discreteBetheIndex, hi, lo]
        rw [Nat.cast_sub (by omega : 1 ≤ j.val)]
        push_cast
        ring
      change f _ - f _ = _
      rw [ha, hb, hroot, hroot, hm, ← sub_div, hindex]

theorem exists_betheCountingDerivative_cell_mean {Δ : ℝ} (hΔ : Δ < -1)
    {N k : ℕ} (hN : 0 < N) (p : Fin (k + 1) → ℝ) (hp : p ∈ S_n (k + 1))
    (hs : 2 * (k + 1) ≤ N) (hBE : DiscreteBetheEquation Δ N (k + 1) p)
    (j : Fin (k + 2)) :
    ∃ ξ ∈ Ioo (rootPartitionPoint (k + 1) p (by omega) j.castSucc)
        (rootPartitionPoint (k + 1) p (by omega) j.succ),
      betheCountingDerivative Δ N (k + 1) p ξ = rootGapMultiplicity N (k + 1) hs j /
        ((N : ℝ) * (rootPartitionPoint (k + 1) p (by omega) j.succ -
          rootPartitionPoint (k + 1) p (by omega) j.castSucc)) := by
  have hgap := rootPartition_gap_pos hp (by omega) j
  have hcont : Continuous (betheCountingFunction Δ N (k + 1) p) :=
    continuous_iff_continuousAt.2 (fun x => (hasDerivAt_betheCountingFunction hΔ N (k + 1) p x).continuousAt)
  obtain ⟨ξ, hξ, hmean⟩ := exists_hasDerivAt_eq_slope
    (betheCountingFunction Δ N (k + 1) p) (betheCountingDerivative Δ N (k + 1) p)
    (sub_pos.mp hgap) hcont.continuousOn
    (fun x _ => hasDerivAt_betheCountingFunction hΔ N (k + 1) p x)
  refine ⟨ξ, hξ, ?_⟩
  rw [betheCountingFunction_cell_increment hN p hs hBE j] at hmean
  simpa only [div_div] using hmean

end PottsDiscontinuity.Bethe
