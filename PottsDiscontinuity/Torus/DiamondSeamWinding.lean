module

public import PottsDiscontinuity.Torus.DiamondDisplacement

/-!
# Primal winding as algebraic intersection with fixed torus cuts

The vertical reference cut lies between columns minus one and zero, and the
horizontal cut lies between rows minus one and zero. Endpoint coordinate potentials
show that these signed crossing sums equal lifted displacement divided by the period.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Signed primal-edge crossing of the fixed vertical reference cut. -/
def diamondSeamCrossX (v : Fin N × Fin M) : ℚ :=
  if v.1.val = 0 then (if checker v then -1 else 1) else 0

/-- Signed primal-edge crossing of the fixed horizontal reference cut. -/
def diamondSeamCrossY (v : Fin N × Fin M) : ℚ := if v.2.val = 0 then -1 else 0

/-- Algebraic intersection of an indexed primal chain with the vertical cut. -/
def diamondWindingX (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ) : ℚ :=
  ∑ e, diamondSeamCrossX e.val * f e

/-- Algebraic intersection of an indexed primal chain with the horizontal cut. -/
def diamondWindingY (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ) : ℚ :=
  ∑ e, diamondSeamCrossY e.val * f e

theorem prv_coordinate_step (i : Fin N) :
    (i.val : ℚ) - (prv i).val = 1 - (N : ℚ) * (if i.val = 0 then 1 else 0) := by
  by_cases hi : i.val = 0
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Fin.pos i).ne'
    have hz : i = 0 := Fin.ext hi
    subst i
    rw [prv_zero]
    simp only [Fin.val_zero, Fin.val_last, ite_true, mul_one, Nat.cast_succ]
    ring
  · have hp := prv_val_of_pos i (by omega)
    have hn : (prv i).val + 1 = i.val := by omega
    have hq : ((prv i).val : ℚ) + 1 = i.val := by exact_mod_cast hn
    simp only [hi, ite_false, mul_zero, sub_zero]
    linarith

theorem diamondCoordinateX_coboundary (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (e : OpenDiamondEdge A) :
    diamondCoboundary hN hM A (fun u => (u.val.1.val : ℚ)) e =
      (if checker e.val then -1 else 1) - (N : ℚ) * diamondSeamCrossX e.val := by
  have he := prv_coordinate_step e.val.1
  cases hc : checker e.val <;> by_cases hx : e.val.1.val = 0 <;>
    simp only [diamondCoboundary_apply, faceEndpoint, faceEndpointRaw, hc,
      Bool.false_eq_true, ite_true, ite_false, diamondSeamCrossX, hx] at * <;> linarith

theorem diamondCoordinateY_coboundary (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (e : OpenDiamondEdge A) :
    diamondCoboundary hN hM A (fun u => (u.val.2.val : ℚ)) e =
      -1 - (M : ℚ) * diamondSeamCrossY e.val := by
  have he := prv_coordinate_step e.val.2
  cases hc : checker e.val <;> by_cases hy : e.val.2.val = 0 <;>
    simp only [diamondCoboundary_apply, faceEndpoint, faceEndpointRaw, hc,
      Bool.false_eq_true, ite_true, ite_false, diamondSeamCrossY, hy] at * <;> linarith

theorem diamondWindingX_mul_period (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) :
    (N : ℚ) * diamondWindingX A f.val = diamondHorizontalDisplacement A f.val := by
  have he := diamondBoundary_pairing hN hM A (fun u => (u.val.1.val : ℚ)) f.val
  have hf : diamondBoundary hN hM A f.val = 0 := f.property
  rw [hf] at he
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at he
  simp_rw [diamondCoordinateX_coboundary, sub_mul, mul_assoc] at he
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at he
  exact (sub_eq_zero.mp he.symm).symm

theorem diamondWindingY_mul_period (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) :
    (M : ℚ) * diamondWindingY A f.val = diamondVerticalDisplacement A f.val := by
  have he := diamondBoundary_pairing hN hM A (fun u => (u.val.2.val : ℚ)) f.val
  have hf : diamondBoundary hN hM A f.val = 0 := f.property
  rw [hf] at he
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at he
  simp_rw [diamondCoordinateY_coboundary, sub_mul, mul_assoc, neg_one_mul] at he
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib] at he
  exact (sub_eq_zero.mp he.symm).symm

end PottsDiscontinuity.Torus
