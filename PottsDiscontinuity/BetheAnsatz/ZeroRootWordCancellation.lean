module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamPhase

/-!
# Cancellation away from the perturbed zero root

The amplitudes remain at the original Bethe roots while word coefficients and
phases use the perturbed tuple. A cyclic ML edge still cancels whenever neither
endpoint carries the root label being perturbed.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- A word term with amplitudes fixed at `p` and local weights evaluated at `q`. -/
noncomputable def fixedAmplitudeWordTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p q : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  amplitude (anisotropy c) p σ * wordCoefficient c q σ w *
    wordPhase (N := N) x q σ w

/-- The boundary amplitude ratio follows from the cyclic Bethe relation and
the ordinary adjacent amplitude relation. The zero-root specialization is
`amplitude_seam_swap`. -/
theorem amplitude_seam_swap_general {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (hn : 0 < n) :
    amplitude (anisotropy c) p (σ * Equiv.swap (Fin.last n) 0) =
      -(z (p (σ (Fin.last n))) ^ N) *
        (z (p (σ 0)) ^ N)⁻¹ *
        Complex.exp (I * (Bethe.theta (anisotropy c)
          (p (σ (Fin.last n))) (p (σ 0)) : ℂ)) *
        amplitude (anisotropy c) p σ := by
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
  have hperm : σ * Equiv.swap (Fin.last n) 0 =
      (ρ * Equiv.swap 0 1) * τ := by
    rw [← hconj]
    simp [ρ, mul_assoc]
  have hρzero : ρ 0 = σ (Fin.last n) := by
    simp [ρ, Equiv.Perm.mul_apply, hinvzero]
  have hρone : ρ 1 = σ 0 := by
    simp [ρ, Equiv.Perm.mul_apply, hinvone]
  have hρswapzero : (ρ * Equiv.swap (0 : Fin (n + 1)) 1) 0 = ρ 1 := by
    simp [Equiv.Perm.mul_apply]
  have hτinv : τ.symm * τ = 1 := by ext k; simp
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
    have hrot := amplitude_rotate (anisotropy_lt_neg_one hc) p hBE ρ
    rw [hρτ, hρzero] at hrot
    calc
      amplitude (anisotropy c) p ρ =
          z (p (σ (Fin.last n))) ^ N *
            ((z (p (σ (Fin.last n))) ^ N)⁻¹ * amplitude (anisotropy c) p ρ) := by
        field_simp [hz]
      _ = z (p (σ (Fin.last n))) ^ N * amplitude (anisotropy c) p σ := by
        rw [hrot]
  have hρswapAmp := amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p ρ
      (a := j.castSucc) (b := j.succ) (by simp)
  rw [hjcast, hjsucc, hρzero, hρone] at hρswapAmp
  have hrotSwap := amplitude_rotate (anisotropy_lt_neg_one hc) p hBE
    (ρ * Equiv.swap (0 : Fin (n + 1)) 1)
  have hrotSwap' :
      amplitude (anisotropy c) p ((ρ * Equiv.swap (0 : Fin (n + 1)) 1) * τ) =
        (z (p (ρ 1)) ^ N)⁻¹ *
          amplitude (anisotropy c) p (ρ * Equiv.swap (0 : Fin (n + 1)) 1) := by
    simpa only [Equiv.Perm.mul_apply, hρswapzero] using hrotSwap
  calc
    amplitude (anisotropy c) p (σ * Equiv.swap (Fin.last n) 0) =
        amplitude (anisotropy c) p
          ((ρ * Equiv.swap (0 : Fin (n + 1)) 1) * τ) := by rw [hperm]
    _ = (z (p (σ 0)) ^ N)⁻¹ *
          amplitude (anisotropy c) p (ρ * Equiv.swap (0 : Fin (n + 1)) 1) := by
      rw [hrotSwap', hρone]
    _ = -(z (p (σ 0)) ^ N)⁻¹ *
          Complex.exp (I * (Bethe.theta (anisotropy c)
            (p (σ (Fin.last n))) (p (σ 0)) : ℂ)) *
          amplitude (anisotropy c) p ρ := by
      rw [hρswapAmp]
      ring
    _ = -(z (p (σ (Fin.last n))) ^ N) *
          (z (p (σ 0)) ^ N)⁻¹ *
          Complex.exp (I * (Bethe.theta (anisotropy c)
            (p (σ (Fin.last n))) (p (σ 0)) : ℂ)) *
          amplitude (anisotropy c) p σ := by rw [hρamp]; ring

/-- At an ordinary ML edge away from the perturbed label, the two
fixed-amplitude terms cancel. -/
theorem fixedAmplitudeWordTerm_adjacent_swap {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p q : Fin (n + 1) → ℝ) (x : Fin (n + 1) → ℤ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (a : Fin n)
    (ha : w a.castSucc = false) (hb : w a.succ = true)
    (hqa : q (σ a.castSucc) = p (σ a.castSucc))
    (hqb : q (σ a.succ) = p (σ a.succ))
    (hza : z (p (σ a.castSucc)) ≠ 1) (hzb : z (p (σ a.succ)) ≠ 1) :
    fixedAmplitudeWordTerm (N := N) c x p q
        (σ * Equiv.swap a.castSucc a.succ) w =
      -fixedAmplitudeWordTerm (N := N) c x p q σ w := by
  have hr : finRotate (n + 1) a.castSucc = a.succ := finRotate_of_lt a.isLt
  have hcross := wordCoefficient_swap_cross c q σ w ha (by
    simpa only [hr] using hb)
  rw [hr] at hcross
  rw [hqa, hqb] at hcross
  have hd := M_mul_L_sub_one_ne_zero hc hza hzb
  have he := M_mul_L_sub_one_ne_zero hc hzb hza
  have hphase := wordPhase_adjacent_swap (N := N) x q σ w a ha hb
  have hab : (a.castSucc).val + 1 = (a.succ).val := rfl
  have hamp := amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p σ hab
  have hfactor :
      Complex.exp (I * (Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) (p (σ a.succ)) : ℂ)) *
        wordCoefficient c q (σ * Equiv.swap a.castSucc a.succ) w =
      wordCoefficient c q σ w := by
    rw [exp_I_theta_eq_M_L_ratio hc hza hzb]
    field_simp [hd, he]
    linear_combination hcross
  unfold fixedAmplitudeWordTerm
  rw [hphase, hamp]
  calc
    (-Complex.exp (I * (Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) (p (σ a.succ)) : ℂ)) * amplitude (anisotropy c) p σ) *
        wordCoefficient c q (σ * Equiv.swap a.castSucc a.succ) w *
        wordPhase (N := N) x q σ w =
      -(amplitude (anisotropy c) p σ *
        (Complex.exp (I * (Bethe.theta (anisotropy c)
          (p (σ a.castSucc)) (p (σ a.succ)) : ℂ)) *
          wordCoefficient c q (σ * Equiv.swap a.castSucc a.succ) w) *
        wordPhase (N := N) x q σ w) := by ring
    _ = -(amplitude (anisotropy c) p σ * wordCoefficient c q σ w *
        wordPhase (N := N) x q σ w) := by rw [hfactor]

/-- At the cyclic seam, the Bethe and position phases cancel whenever the
perturbed root is not at either endpoint. -/
theorem fixedAmplitudeWordTerm_seam_swap {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p q : Fin (n + 1) → ℝ) (x : Fin (n + 1) → ℤ)
    (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (hn : 0 < n)
    (hLast : w (Fin.last n) = false) (hZero : w 0 = true)
    (hqLast : q (σ (Fin.last n)) = p (σ (Fin.last n)))
    (hqZero : q (σ 0) = p (σ 0))
    (hzLast : z (p (σ (Fin.last n))) ≠ 1) (hzZero : z (p (σ 0)) ≠ 1) :
    fixedAmplitudeWordTerm (N := N) c x p q
        (σ * Equiv.swap (Fin.last n) 0) w =
      -fixedAmplitudeWordTerm (N := N) c x p q σ w := by
  have hcross := wordCoefficient_swap_cross c q σ w
      (a := Fin.last n) hLast (by simpa only [finRotate_last] using hZero)
  rw [finRotate_last] at hcross
  rw [hqLast, hqZero] at hcross
  have hd := M_mul_L_sub_one_ne_zero hc hzLast hzZero
  have he := M_mul_L_sub_one_ne_zero hc hzZero hzLast
  have hphase := wordPhase_seam_swap (N := N) x q σ w hn hLast hZero
  have hamp := amplitude_seam_swap_general hc p hBE σ hn
  have hfactor :
      Complex.exp (I * (Bethe.theta (anisotropy c)
        (p (σ (Fin.last n))) (p (σ 0)) : ℂ)) *
        wordCoefficient c q (σ * Equiv.swap (Fin.last n) 0) w =
      wordCoefficient c q σ w := by
    rw [exp_I_theta_eq_M_L_ratio hc hzLast hzZero]
    field_simp [hd, he]
    linear_combination hcross
  unfold fixedAmplitudeWordTerm
  rw [hphase, hamp]
  have hz0 : z (p (σ 0)) ^ N ≠ 0 := pow_ne_zero N (z_ne_zero _)
  have hzu : z (p (σ (Fin.last n))) ^ N ≠ 0 :=
    pow_ne_zero N (z_ne_zero _)
  calc
    (-(z (p (σ (Fin.last n))) ^ N) * (z (p (σ 0)) ^ N)⁻¹ *
        Complex.exp (I * (Bethe.theta (anisotropy c)
          (p (σ (Fin.last n))) (p (σ 0)) : ℂ)) * amplitude (anisotropy c) p σ) *
        wordCoefficient c q (σ * Equiv.swap (Fin.last n) 0) w *
        (z (q (σ 0)) ^ N * (z (q (σ (Fin.last n))) ^ N)⁻¹ *
          wordPhase (N := N) x q σ w) =
      -(amplitude (anisotropy c) p σ *
        (Complex.exp (I * (Bethe.theta (anisotropy c)
          (p (σ (Fin.last n))) (p (σ 0)) : ℂ)) *
          wordCoefficient c q (σ * Equiv.swap (Fin.last n) 0) w) *
        wordPhase (N := N) x q σ w) := by
      rw [hqLast, hqZero]
      field_simp [hz0, hzu]
    _ = -(amplitude (anisotropy c) p σ * wordCoefficient c q σ w *
        wordPhase (N := N) x q σ w) := by rw [hfactor]

end PottsDiscontinuity.BetheAnsatz
