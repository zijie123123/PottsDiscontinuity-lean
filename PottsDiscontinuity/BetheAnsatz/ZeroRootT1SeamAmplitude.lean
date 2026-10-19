module

public import PottsDiscontinuity.BetheAnsatz.Amplitude
public import PottsDiscontinuity.BetheAnsatz.Cyclic

/-!
# The seam amplitude transposition

Conjugating the seam swap by the cyclic rotation turns it into the ordinary
swap of slots 0 and 1. The cyclic Bethe relation then gives its boundary factor.
-/

@[expose] public section

open Complex

namespace PottsDiscontinuity.BetheAnsatz

/-- The amplitude ratio for swapping the last and first slots, with the first
slot carrying a zero root. -/
theorem amplitude_seam_swap {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (hn : 0 < n)
    (hzero : p (σ 0) = 0) :
    amplitude (anisotropy c) p (σ * Equiv.swap (Fin.last n) 0) =
      -(z (p (σ (Fin.last n))) ^ N) *
        Complex.exp (I * (Bethe.theta (anisotropy c)
          (p (σ (Fin.last n))) 0 : ℂ)) * amplitude (anisotropy c) p σ := by
  let τ := finRotate (n + 1)
  let ρ := σ * τ.symm
  have hlast : τ (Fin.last n) = 0 := finRotate_last
  let j : Fin n := ⟨0, hn⟩
  have hjcast : j.castSucc = (0 : Fin (n + 1)) := by ext; simp [j]
  have hjsucc : j.succ = (1 : Fin (n + 1)) := by
    apply Fin.ext
    simp [j, Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
  have hzeroRotate : τ 0 = 1 := by
    change finRotate (n + 1) j.castSucc = (1 : Fin (n + 1))
    calc
      finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
      _ = 1 := hjsucc
  have hinvzero : τ.symm 0 = Fin.last n :=
    (Equiv.symm_apply_eq _).mpr hlast.symm
  have hinvone : τ.symm 1 = 0 :=
    (Equiv.symm_apply_eq _).mpr hzeroRotate.symm
  have hEq : (τ.trans (Equiv.swap (0 : Fin (n + 1)) 1)).trans τ.symm =
      Equiv.swap (Fin.last n) 0 := by
    rw [Equiv.trans_swap_trans_symm, hinvzero, hinvone]
  have hconj : τ.symm * Equiv.swap (0 : Fin (n + 1)) 1 * τ =
      Equiv.swap (Fin.last n) 0 := by
    ext k
    simp only [Equiv.Perm.mul_apply]
    have hpoint : τ.symm (Equiv.swap (0 : Fin (n + 1)) 1 (τ k)) =
        Equiv.swap (Fin.last n) 0 k := by
      simpa only [Equiv.trans_apply] using
        congrArg (fun e : Fin (n + 1) ≃ Fin (n + 1) => e k) hEq
    exact congrArg Fin.val hpoint
  have hperm : σ * Equiv.swap (Fin.last n) 0 = (ρ * Equiv.swap 0 1) * τ := by
    rw [← hconj]
    simp [ρ, mul_assoc]
  have hρzero : ρ 0 = σ (Fin.last n) := by
    simp [ρ, Equiv.Perm.mul_apply, hinvzero]
  have hρone : ρ 1 = σ 0 := by
    simp [ρ, Equiv.Perm.mul_apply, hinvone]
  have hρswapzero : (ρ * Equiv.swap (0 : Fin (n + 1)) 1) 0 = σ 0 := by
    simp [Equiv.Perm.mul_apply, hρone]
  have hrot : amplitude (anisotropy c) p (ρ * τ) =
      (z (p (ρ 0)) ^ N)⁻¹ * amplitude (anisotropy c) p ρ :=
    amplitude_rotate (anisotropy_lt_neg_one hc) p hBE ρ
  have hτinv : τ.symm * τ = 1 := by
    ext k
    simp
  have hρτ : ρ * τ = σ := by
    calc
      ρ * τ = (σ * τ.symm) * τ := rfl
      _ = σ * (τ.symm * τ) := by rw [mul_assoc]
      _ = σ * 1 := by rw [hτinv]
      _ = σ := by rw [mul_one]
  have hρamp : amplitude (anisotropy c) p ρ =
      z (p (σ (Fin.last n))) ^ N * amplitude (anisotropy c) p σ := by
    have hz : z (p (σ (Fin.last n))) ^ N ≠ 0 :=
      pow_ne_zero N (z_ne_zero _)
    rw [hρτ] at hrot
    rw [hρzero] at hrot
    calc
      amplitude (anisotropy c) p ρ =
          z (p (σ (Fin.last n))) ^ N *
            ((z (p (σ (Fin.last n))) ^ N)⁻¹ * amplitude (anisotropy c) p ρ) := by
        field_simp [hz]
      _ = z (p (σ (Fin.last n))) ^ N * amplitude (anisotropy c) p σ := by
        rw [hrot]
  have hrotSwap : amplitude (anisotropy c) p
      ((ρ * Equiv.swap (0 : Fin (n + 1)) 1) * τ) =
        amplitude (anisotropy c) p (ρ * Equiv.swap 0 1) := by
    rw [amplitude_rotate (anisotropy_lt_neg_one hc) p hBE]
    rw [hρswapzero, hzero]
    simp [z]
  
  have hAdj := amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p ρ
    (a := j.castSucc) (b := j.succ) (by simp)
  rw [hjcast, hjsucc, hρzero, hρone, hzero] at hAdj
  calc
    amplitude (anisotropy c) p (σ * Equiv.swap (Fin.last n) 0) =
        amplitude (anisotropy c) p
          ((ρ * Equiv.swap (0 : Fin (n + 1)) 1) * τ) := by rw [hperm]
    _ = amplitude (anisotropy c) p (ρ * Equiv.swap 0 1) := hrotSwap
    _ = -Complex.exp (I * (Bethe.theta (anisotropy c)
          (p (σ (Fin.last n))) 0 : ℂ)) * amplitude (anisotropy c) p ρ := hAdj
    _ = -(z (p (σ (Fin.last n))) ^ N) *
          Complex.exp (I * (Bethe.theta (anisotropy c)
            (p (σ (Fin.last n))) 0 : ℂ)) * amplitude (anisotropy c) p σ := by
      rw [hρamp]
      ring

end PottsDiscontinuity.BetheAnsatz
