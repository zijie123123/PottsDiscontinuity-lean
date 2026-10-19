module

public import PottsDiscontinuity.BetheAnsatz.Amplitude
public import PottsDiscontinuity.BetheAnsatz.WordSwap

/-!
# Cancellation at ordinary ML edges

The product form of the coefficient identity avoids dividing by word coefficients.
Only the nonzero two-body scattering denominator is divided out.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- One term in the amplitude-weighted word expansion. -/
noncomputable def wordTerm {N n : ℕ} (c : ℝ) (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  amplitude (anisotropy c) p σ * wordCoefficient c p σ w * wordPhase (N := N) x p σ w

/-- The two terms paired at an ordinary ML edge are negatives of each other. -/
theorem wordTerm_adjacent_swap {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (hp : ∀ j, z (p j) ≠ 1)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (a : Fin n)
    (ha : w a.castSucc = false) (hb : w a.succ = true) :
    wordTerm (N := N) c x p (σ * Equiv.swap a.castSucc a.succ) w =
      -wordTerm (N := N) c x p σ w := by
  have hrot : finRotate (n + 1) a.castSucc = a.succ := finRotate_of_lt a.isLt
  have hcross := wordCoefficient_swap_cross c p σ w ha (hrot.symm ▸ hb)
  rw [hrot] at hcross
  have hden := M_mul_L_sub_one_ne_zero hc (hp (σ a.succ)) (hp (σ a.castSucc))
  unfold wordTerm
  rw [wordPhase_adjacent_swap x p σ w a ha hb,
    amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p σ (by simp),
    exp_I_theta_eq_M_L_ratio hc (hp (σ a.castSucc)) (hp (σ a.succ))]
  apply mul_right_cancel₀ hden
  field_simp
  linear_combination -amplitude (anisotropy c) p σ * wordPhase (N := N) x p σ w * hcross

/-- Every word with an ordinary ML edge contributes zero after the permutation sum. -/
theorem sum_wordTerm_eq_zero_of_adjacentML {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (hp : ∀ j, z (p j) ≠ 1)
    (w : Fin (n + 1) → Bool) (a : Fin n)
    (ha : w a.castSucc = false) (hb : w a.succ = true) :
    (∑ σ, wordTerm (N := N) c x p σ w) = 0 := by
  have h : (∑ σ, wordTerm (N := N) c x p σ w) =
      ∑ σ, wordTerm (N := N) c x p (σ * Equiv.swap a.castSucc a.succ) w :=
    (Equiv.sum_comp (Equiv.mulRight (Equiv.swap a.castSucc a.succ)) _).symm
  simp_rw [wordTerm_adjacent_swap hc x p hp _ w a ha hb] at h
  rw [Finset.sum_neg_distrib] at h
  linear_combination (1 / 2 : ℂ) * h

end PottsDiscontinuity.BetheAnsatz
