module

public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# Geometric sums in an integer gap

Companion paper, equation `eq:EmptySetCalc`. Integer endpoints can be negative.
The only spectral restriction in this finite calculation is `z(p) ≠ 1`.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The exponential at one integer coordinate. -/
noncomputable def positionPhase (p : ℝ) (u : ℤ) : ℂ := Complex.exp (I * (p : ℂ) * (u : ℂ))

theorem positionPhase_add (p : ℝ) (a b : ℤ) :
    positionPhase p (a + b) = positionPhase p a * positionPhase p b := by
  unfold positionPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem positionPhase_one (p : ℝ) : positionPhase p 1 = z p := by
  simp only [positionPhase, Int.cast_one, mul_one, z]

theorem positionPhase_nat (p : ℝ) (d : ℕ) : positionPhase p d = z p ^ d := by
  rw [positionPhase, z, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- An open integer interval is a shifted natural geometric sum. -/
theorem sum_positionPhase_Ioo (p : ℝ) (a : ℤ) (d : ℕ) :
    (∑ u ∈ Ioo a (a + (d : ℤ) + 1), positionPhase p u) =
      positionPhase p (a + 1) * ∑ j ∈ range d, z p ^ j := by
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun (j : ℕ) _ => a + (j : ℤ) + 1)
  · intro j hj
    have hj' := mem_range.mp hj
    simp only [mem_Ioo]
    constructor <;> omega
  · intro i _ j _ he
    omega
  · intro u hu
    obtain ⟨hl, hr⟩ := mem_Ioo.mp hu
    refine ⟨(u - a - 1).toNat, ?_, ?_⟩
    · apply mem_range.mpr
      omega
    · omega
  · intro j _
    symm
    rw [show a + (j : ℤ) + 1 = (a + 1) + (j : ℤ) by ring,
      positionPhase_add, positionPhase_nat]

/-- Separate the two endpoints from the interior weighted sum. -/
theorem sum_gap_endpoint_weights (c p : ℝ) {a b : ℤ} (hab : a < b) :
    (∑ u ∈ Icc a b, (if u = a ∨ u = b then (1 : ℂ) else (c : ℂ) ^ 2) * positionPhase p u) =
      positionPhase p a + (c : ℂ) ^ 2 * (∑ u ∈ Ioo a b, positionPhase p u) + positionPhase p b := by
  have hs : Icc a b = insert a (insert b (Ioo a b)) := by
    ext u
    simp only [mem_Icc, mem_insert, mem_Ioo]
    omega
  have ha : a ∉ insert b (Ioo a b) := by simp [hab.ne]
  have hb : b ∉ Ioo a b := by simp
  rw [hs, Finset.sum_insert ha, Finset.sum_insert hb]
  have hi : (∑ u ∈ Ioo a b, (if u = a ∨ u = b then (1 : ℂ) else (c : ℂ) ^ 2) * positionPhase p u) =
      (c : ℂ) ^ 2 * ∑ u ∈ Ioo a b, positionPhase p u := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have h := mem_Ioo.mp hu
    simp only [h.1.ne', h.2.ne, or_self, ↓reduceIte]
  rw [hi]
  simp only [true_or, or_true, ↓reduceIte, one_mul]
  ring

/-- The single-gap geometric identity in the exact exponential convention of the wave. -/
theorem sum_gap_geometric (c p : ℝ) {a b : ℤ} (hab : a < b) (hp : z p ≠ 1) :
    (∑ u ∈ Icc a b, (if u = a ∨ u = b then (1 : ℂ) else (c : ℂ) ^ 2) * positionPhase p u) =
      L c (z p) * positionPhase p a + M c (z p) * positionPhase p b := by
  let d := (b - a - 1).toNat
  have hb : b = a + (d : ℤ) + 1 := by dsimp [d]; omega
  have hphase : positionPhase p b = positionPhase p a * (z p) ^ (d + 1) := by
    rw [hb, show a + (d : ℤ) + 1 = a + ((d + 1 : ℕ) : ℤ) by push_cast; ring,
      positionPhase_add, positionPhase_nat]
  rw [sum_gap_endpoint_weights c p hab, hb, sum_positionPhase_Ioo,
    geom_sum_eq hp, positionPhase_add, positionPhase_one]
  have hb' : positionPhase p (a + (d : ℤ) + 1) = positionPhase p a * (z p) ^ (d + 1) := by
    rw [← hb]
    exact hphase
  rw [hb', pow_succ]
  have hd : z p - 1 ≠ 0 := sub_ne_zero.mpr hp
  have hd' : 1 - z p ≠ 0 := sub_ne_zero.mpr hp.symm
  unfold L M
  field_simp
  ring

end PottsDiscontinuity.BetheAnsatz
