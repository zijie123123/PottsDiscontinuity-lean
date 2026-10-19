module

public import Mathlib
public import PottsDiscontinuity.Bethe.DiscreteCore
public import PottsDiscontinuity.BetheAnsatz.Defs

/-! # Corollary 3.4: transfer the discrete Bethe data to Theorem 3.1 -/

@[expose] public section

open Complex

namespace PottsDiscontinuity.SixVertex

/-- The centered quantum number in (BE_Δ) contributes the phase `(-1)^(n-1)` in (BE). -/
theorem cor34_discreteBethe_phase (n : ℕ) (j : Fin n) :
    Complex.exp (I * ((2 * Real.pi *
      Bethe.discreteBetheIndex n j : ℝ) : ℂ)) = (-1 : ℂ) ^ (n - 1) := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hindex :
      2 * Real.pi * Bethe.discreteBetheIndex n j =
        (2 * (j.val : ℝ) - ((n : ℝ) - 1)) * Real.pi := by
    unfold Bethe.discreteBetheIndex
    ring
  have harg : I * ((2 * Real.pi * Bethe.discreteBetheIndex n j : ℝ) : ℂ) =
      (j.val : ℂ) * (2 * Real.pi * I) +
        ((n - 1 : ℕ) : ℂ) * (-(Real.pi * I)) := by
    rw [hindex]
    push_cast [Nat.cast_sub hn]
    ring
  have hperiod : Complex.exp ((j.val : ℂ) * (2 * Real.pi * I)) = 1 := by
    have hj : (j.val : ℂ) = (j.val : ℤ) := by norm_cast
    rw [hj]
    convert Complex.exp_int_mul_two_pi_mul_I (j.val : ℤ) using 1
  have hsign : Complex.exp (((n - 1 : ℕ) : ℂ) * (-(Real.pi * I))) =
      (-1 : ℂ) ^ (n - 1) := by
    rw [Complex.exp_nat_mul]
    simp [Complex.exp_neg, Complex.exp_pi_mul_I]
  rw [harg, Complex.exp_add, hperiod, hsign, one_mul]

/-- Every solution of the discrete equations with centered indices satisfies the Bethe
equations used by Theorem 3.1. -/
theorem cor34_discreteBetheEquation_to_betheEquations
    {Δ : ℝ} {N n : ℕ} (p : Fin n → ℝ)
    (hBE : Bethe.DiscreteBetheEquation Δ N n p) :
    BetheAnsatz.BetheEquations N Δ p := by
  intro j
  have hphase := cor34_discreteBethe_phase n j
  calc
    Complex.exp (I * (N : ℂ) * (p j : ℂ)) =
        Complex.exp (I * (((N : ℝ) * p j : ℝ) : ℂ)) := by
          congr 1
          push_cast
          ring
    _ = Complex.exp (I *
        ((2 * Real.pi * Bethe.discreteBetheIndex n j -
          ∑ k : Fin n, Bethe.theta Δ (p j) (p k) : ℝ) : ℂ)) := by
          rw [hBE j]
    _ = Complex.exp (I * ((2 * Real.pi * Bethe.discreteBetheIndex n j : ℝ) : ℂ)) *
        Complex.exp (- (I * ((∑ k : Fin n, Bethe.theta Δ (p j) (p k) : ℝ) : ℂ))) := by
          rw [show I *
              ((2 * Real.pi * Bethe.discreteBetheIndex n j -
                ∑ k : Fin n, Bethe.theta Δ (p j) (p k) : ℝ) : ℂ) =
                I * ((2 * Real.pi * Bethe.discreteBetheIndex n j : ℝ) : ℂ) +
                  - (I * ((∑ k : Fin n, Bethe.theta Δ (p j) (p k) : ℝ) : ℂ)) by
                    push_cast
                    ring,
            Complex.exp_add]
    _ = (-1 : ℂ) ^ (n - 1) *
        Complex.exp (- (I * ((∑ k : Fin n, Bethe.theta Δ (p j) (p k) : ℝ) : ℂ))) := by
          rw [hphase]

/-- The strict ordering in `S_n` makes all momenta distinct. -/
theorem cor34_S_n_injective {n : ℕ} {p : Fin n → ℝ} (hp : p ∈ Bethe.S_n n) :
    Function.Injective p :=
  hp.2.1.injective

/-- For even particle number, symmetry and strict ordering exclude a zero momentum. -/
theorem cor34_even_S_n_roots_nonzero {n : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ Bethe.S_n n) (hn : Even n) (j : Fin n) : p j ≠ 0 := by
  intro hj
  have hrev : Fin.rev j = j := hp.2.1.injective (by rw [hp.2.2 j, hj, neg_zero])
  have hv := congrArg Fin.val hrev
  simp only [Fin.val_rev] at hv
  rcases hn with ⟨k, hk⟩
  omega

/-- For odd particle number, the fixed middle index is the unique zero momentum. -/
theorem cor34_odd_S_n_center_zero {n q : ℕ} {p : Fin n → ℝ}
    (hp : p ∈ Bethe.S_n n) (hnq : n + 1 = 2 * q) :
    p (⟨q - 1, by omega⟩ : Fin n) = 0 := by
  let l : Fin n := ⟨q - 1, by omega⟩
  have hrev : Fin.rev l = l := by
    apply Fin.ext
    simp [l, Fin.val_rev]
    omega
  have hs := hp.2.2 l
  rw [hrev] at hs
  linarith

end PottsDiscontinuity.SixVertex
