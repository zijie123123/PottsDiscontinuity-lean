module

public import PottsDiscontinuity.BetheAnsatz.Amplitude
public import PottsDiscontinuity.BetheAnsatz.Perturbation
public import PottsDiscontinuity.BetheAnsatz.WordSwap

/-!
# Ordinary-edge pairing in the zero-root perturbation

With the amplitudes held at the original Bethe roots, an ordinary ML edge
still has a pair relation. The moved root contributes its phase explicitly;
this is the corrected Claim 1 ratio from the source audit.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- One amplitude-weighted word term with only the word momentum perturbed. -/
noncomputable def perturbedWordTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (t : ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  amplitude (anisotropy c) p σ *
    wordCoefficient c (perturbedMomenta p l t) σ w *
      wordPhase (N := N) x (perturbedMomenta p l t) σ w

/-- At an ordinary ML edge whose L slot carries the moved root, swapping the
two slots multiplies the perturbed word term by the corrected scattering phase. -/
theorem perturbedWordTerm_adjacent_pair {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (t : ℝ) (ht : z t ≠ 1)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (a : Fin n)
    (hsig : σ a.succ = l) (ha : w a.castSucc = false) (hb : w a.succ = true) :
    perturbedWordTerm (N := N) c x p l t (σ * Equiv.swap a.castSucc a.succ) w =
      -Complex.exp (I * (Bethe.theta (anisotropy c) t (p (σ a.castSucc)) -
        Bethe.theta (anisotropy c) 0 (p (σ a.castSucc)) : ℂ)) *
        perturbedWordTerm (N := N) c x p l t σ w := by
  let q := perturbedMomenta p l t
  have hslots : a.castSucc ≠ a.succ := Fin.castSucc_lt_succ.ne
  have hσa : σ a.castSucc ≠ l := by
    intro h
    exact hslots (σ.injective (h.trans hsig.symm))
  have hrootne (j : Fin (n + 1)) (hj : j ≠ l) : p j ≠ 0 := by
    intro hz
    apply hj
    exact hinj (hz.trans hpl.symm)
  have hqa : q (σ a.castSucc) = p (σ a.castSucc) :=
    perturbedMomenta_of_ne p l (σ a.castSucc) t hσa
  have hqb : q (σ a.succ) = t := by
    simp [q, hsig, perturbedMomenta, hpl]
  have hqa_ne : z (q (σ a.castSucc)) ≠ 1 := by
    rw [hqa]
    exact z_ne_one (hp (σ a.castSucc)) (hrootne _ hσa)
  have hqb_ne : z (q (σ a.succ)) ≠ 1 := by rw [hqb]; exact ht
  have hrot : finRotate (n + 1) a.castSucc = a.succ := finRotate_of_lt a.isLt
  have hcross := wordCoefficient_swap_cross c q σ w ha (hrot.symm ▸ hb)
  rw [hrot] at hcross
  let num := M c (z (q (σ a.succ))) * L c (z (q (σ a.castSucc))) - 1
  let den := M c (z (q (σ a.castSucc))) * L c (z (q (σ a.succ))) - 1
  have hden : den ≠ 0 := by
    dsimp [den]
    exact M_mul_L_sub_one_ne_zero hc hqa_ne hqb_ne
  have hcross' :
      wordCoefficient c q (σ * Equiv.swap a.castSucc a.succ) w * den =
        wordCoefficient c q σ w * num := by
    simpa [den, num] using hcross
  have htheta : Complex.exp (I * (Bethe.theta (anisotropy c)
        (q (σ a.succ)) (q (σ a.castSucc)) : ℂ)) = num / den := by
    simpa [num, den] using exp_I_theta_eq_M_L_ratio hc hqb_ne hqa_ne
  have hnum : num = Complex.exp (I * (Bethe.theta (anisotropy c)
        (q (σ a.succ)) (q (σ a.castSucc)) : ℂ)) * den := by
    calc
      num = (num / den) * den := by field_simp [hden]
      _ = Complex.exp (I * (Bethe.theta (anisotropy c)
          (q (σ a.succ)) (q (σ a.castSucc)) : ℂ)) * den := by rw [← htheta]
  have hnum' : num = Complex.exp (I * (Bethe.theta (anisotropy c)
        t (p (σ a.castSucc)) : ℂ)) * den := by
    simpa [hqb, hqa] using hnum
  have hamp : amplitude (anisotropy c) p (σ * Equiv.swap a.castSucc a.succ) =
      -Complex.exp (I * (Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) 0 : ℂ)) * amplitude (anisotropy c) p σ := by
    rw [amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p σ (by simp), hsig, hpl]
  have hphase : wordPhase (N := N) x q (σ * Equiv.swap a.castSucc a.succ) w =
      wordPhase (N := N) x q σ w :=
    wordPhase_adjacent_swap x q σ w a ha hb
  have hword :
      wordCoefficient c q (σ * Equiv.swap a.castSucc a.succ) w *
          wordPhase (N := N) x q σ w =
        Complex.exp (I * (Bethe.theta (anisotropy c)
          t (p (σ a.castSucc)) : ℂ)) *
          (wordCoefficient c q σ w * wordPhase (N := N) x q σ w) := by
    apply mul_right_cancel₀ hden
    calc
      wordCoefficient c q (σ * Equiv.swap a.castSucc a.succ) w *
            wordPhase (N := N) x q σ w * den =
          (wordCoefficient c q (σ * Equiv.swap a.castSucc a.succ) w * den) *
            wordPhase (N := N) x q σ w := by ring
      _ = (wordCoefficient c q σ w * num) *
            wordPhase (N := N) x q σ w := by rw [hcross']
      _ = (wordCoefficient c q σ w *
            (Complex.exp (I * (Bethe.theta (anisotropy c)
              t (p (σ a.castSucc)) : ℂ)) * den)) *
            wordPhase (N := N) x q σ w := by rw [hnum']
      _ = Complex.exp (I * (Bethe.theta (anisotropy c)
            t (p (σ a.castSucc)) : ℂ)) *
            (wordCoefficient c q σ w * wordPhase (N := N) x q σ w) * den := by ring
  have hword' :
      wordCoefficient c (perturbedMomenta p l t)
          (σ * Equiv.swap a.castSucc a.succ) w *
          wordPhase (N := N) x q σ w =
        Complex.exp (I * (Bethe.theta (anisotropy c)
          t (p (σ a.castSucc)) : ℂ)) *
          (wordCoefficient c (perturbedMomenta p l t) σ w *
            wordPhase (N := N) x q σ w) := by
    simpa [q] using hword
  have hfactor : Complex.exp (I * (Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) 0 : ℂ)) *
      Complex.exp (I * (Bethe.theta (anisotropy c) t (p (σ a.castSucc)) : ℂ)) =
      Complex.exp (I * (Bethe.theta (anisotropy c) t (p (σ a.castSucc)) -
        Bethe.theta (anisotropy c) 0 (p (σ a.castSucc)) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [Bethe.theta_swap, Complex.ofReal_neg]
    ring
  unfold perturbedWordTerm
  rw [hamp, hphase]
  calc
    (-Complex.exp (I * (Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) 0 : ℂ)) * amplitude (anisotropy c) p σ) *
        wordCoefficient c (perturbedMomenta p l t)
          (σ * Equiv.swap a.castSucc a.succ) w *
          wordPhase (N := N) x q σ w =
      (-Complex.exp (I * (Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) 0 : ℂ)) * amplitude (anisotropy c) p σ) *
        (wordCoefficient c (perturbedMomenta p l t)
          (σ * Equiv.swap a.castSucc a.succ) w *
          wordPhase (N := N) x q σ w) := by ring
    _ = (-Complex.exp (I * (Bethe.theta (anisotropy c)
        (p (σ a.castSucc)) 0 : ℂ)) * amplitude (anisotropy c) p σ) *
        (Complex.exp (I * (Bethe.theta (anisotropy c)
          t (p (σ a.castSucc)) : ℂ)) *
          (wordCoefficient c (perturbedMomenta p l t) σ w *
            wordPhase (N := N) x q σ w)) := by rw [hword']
    _ = -(Complex.exp (I * (Bethe.theta (anisotropy c)
          (p (σ a.castSucc)) 0 : ℂ)) *
        Complex.exp (I * (Bethe.theta (anisotropy c)
          t (p (σ a.castSucc)) : ℂ))) *
        (amplitude (anisotropy c) p σ *
          wordCoefficient c (perturbedMomenta p l t) σ w *
          wordPhase (N := N) x q σ w) := by ring
    _ = -Complex.exp (I * (Bethe.theta (anisotropy c)
          t (p (σ a.castSucc)) - Bethe.theta (anisotropy c) 0
            (p (σ a.castSucc)) : ℂ)) *
        (amplitude (anisotropy c) p σ *
          wordCoefficient c (perturbedMomenta p l t) σ w *
          wordPhase (N := N) x q σ w) := by
      rw [hfactor]

end PottsDiscontinuity.BetheAnsatz
