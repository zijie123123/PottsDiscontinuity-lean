module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamAmplitude
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamPhase
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1ZipperFinalStep

/-!
# The cyclic seam zipper move

The ordinary zipper identity also holds across the last-to-first edge. The
Bethe boundary relation and the `N`-shift in the position phase cancel exactly.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Move a zero root across two consecutive L letters at the cyclic seam. -/
theorem zeroRootRegularizedWordTerm_zipper_seam {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (hn : 0 < n)
    (hσ : σ (Fin.last n) = l)
    (hZero : w 0 = true) :
    zeroRootRegularizedWordTerm (N := N) c x p l
      (σ * Equiv.swap (Fin.last n) 0) (Function.update w (Fin.last n) false) =
    zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
  let u := Fin.last n
  let σ' := σ * Equiv.swap u 0
  let w' := Function.update w u false
  have hu0 : u ≠ (0 : Fin (n + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    simp [u] at hv
    omega
  have hσ0 : σ' 0 = l := by
    change σ (Equiv.swap u 0 0) = l
    rw [Equiv.swap_apply_right]
    exact hσ
  have hσ'u : σ' u = σ 0 := by
    change σ (Equiv.swap u 0 u) = σ 0
    rw [Equiv.swap_apply_left]
  have hσswap : σ' * Equiv.swap u 0 = σ := by
    ext k
    simp [σ', u]
  have hzero' : p (σ' 0) = 0 := by rw [hσ0, hpl]
  have hσ0ne : σ 0 ≠ l := by
    intro h
    exact hu0 (σ.injective (h.trans hσ.symm)).symm
  have hpσ0 : p (σ 0) ≠ 0 := by
    intro h
    exact hσ0ne (hinj (h.trans hpl.symm))
  have hz : z (p (σ 0)) ≠ 1 := z_ne_one (hp (σ 0)) hpσ0
  have hL : L c (z (p (σ 0))) ≠ 0 := L_ne_zero hc hz
  have hM : M c (z (p (σ 0))) ≠ 0 := M_ne_zero hc hz
  have hphaseFlip : wordPhase (N := N) x p σ w' =
      wordPhase (N := N) x p σ w := by
    unfold wordPhase
    apply Finset.prod_congr rfl
    intro k _
    by_cases hku : k = u
    · subst k
      have hpσu : p (σ u) = 0 := by rw [hσ, hpl]
      simp [w', hpσu, positionPhase]
    · simp [w', Function.update_of_ne hku]
  have hphaseSwap := wordPhase_seam_swap (N := N) x p σ w' hn
    (by simp [w', u]) (by simpa [w', Function.update_of_ne hu0.symm] using hZero)
  have hphase : wordPhase (N := N) x p σ' w' =
      z (p (σ 0)) ^ N * wordPhase (N := N) x p σ w := by
    simpa [σ', w', u, hσ, hpl, z_zero, hphaseFlip] using hphaseSwap
  have hAmpSwap := amplitude_seam_swap hc p hBE σ' hn hzero'
  have hAmp : amplitude (anisotropy c) p σ =
      -(z (p (σ 0)) ^ N) *
        Complex.exp (I * (Bethe.theta (anisotropy c) (p (σ 0)) 0 : ℂ)) *
        amplitude (anisotropy c) p σ' := by
    have hAmp' := hAmpSwap
    rw [hσswap] at hAmp'
    simpa [u, hσ'u] using hAmp'
  have hθ0 := exp_I_theta_zero_eq_neg_L_div_M hc hz
  have hθswap : Bethe.theta (anisotropy c) (p (σ 0)) 0 =
      -Bethe.theta (anisotropy c) 0 (p (σ 0)) := by
    exact Bethe.theta_swap (anisotropy c) 0 (p (σ 0))
  have hθ : Complex.exp (I * (Bethe.theta (anisotropy c)
      (p (σ 0)) 0 : ℂ)) = -M c (z (p (σ 0))) / L c (z (p (σ 0))) := by
    rw [hθswap, Complex.ofReal_neg, mul_neg, Complex.exp_neg, hθ0]
    field_simp [hL, hM]
  have hAmpCross : amplitude (anisotropy c) p σ' * z (p (σ 0)) ^ N *
      M c (z (p (σ 0))) = amplitude (anisotropy c) p σ * L c (z (p (σ 0))) := by
    rw [hAmp, hθ]
    field_simp [hL]
  let S : Finset (Fin (n + 1)) := (univ.erase u).erase 0
  have hcommon :
      (∏ k ∈ S, zeroRootLetterWeight c p σ' w' k) =
        ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
    apply Finset.prod_congr rfl
    intro k hk
    have hku : k ≠ u := (mem_erase.mp (mem_erase.mp hk).2).1
    have hk0 : k ≠ (0 : Fin (n + 1)) := (mem_erase.mp hk).1
    have hswap : Equiv.swap u 0 k = k := Equiv.swap_apply_of_ne_of_ne hku hk0
    have hσk : σ' k = σ k := by simp [σ', Equiv.Perm.mul_apply, hswap]
    simp [σ', w', zeroRootLetterWeight, Function.update_of_ne hku, hσk]
  have hroot : σ.symm l = u := by
    apply σ.injective
    simpa using hσ.symm
  have hroot' : σ'.symm l = 0 := by
    apply σ'.injective
    simpa using hσ0.symm
  have hletter : zeroRootLetterWeight c p σ w 0 = L c (z (p (σ 0))) := by
    simp [zeroRootLetterWeight, hZero]
  have hletter' : zeroRootLetterWeight c p σ' w' u =
      M c (z (p (σ 0))) := by
    simp [zeroRootLetterWeight, w', hσ'u]
  have hOld : zeroRootRegularizedProduct c p l σ w =
      L c (z (p (σ 0))) * ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
    unfold zeroRootRegularizedProduct
    rw [hroot]
    calc
      (∏ k ∈ univ.erase u, zeroRootLetterWeight c p σ w k) =
          zeroRootLetterWeight c p σ w 0 *
            ∏ k ∈ (univ.erase u).erase 0, zeroRootLetterWeight c p σ w k :=
        (Finset.mul_prod_erase (univ.erase u)
          (fun k => zeroRootLetterWeight c p σ w k)
          (Finset.mem_erase.mpr ⟨hu0.symm, mem_univ 0⟩)).symm
      _ = L c (z (p (σ 0))) *
            ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by rw [hletter]
  have hNew : zeroRootRegularizedProduct c p l σ' w' =
      M c (z (p (σ 0))) * ∏ k ∈ S, zeroRootLetterWeight c p σ' w' k := by
    unfold zeroRootRegularizedProduct
    rw [hroot']
    have hset : (univ.erase 0).erase u = S := by
      ext k
      simp only [S, Finset.mem_erase, Finset.mem_univ]
      constructor <;> rintro ⟨h1, h2, _⟩ <;> exact ⟨h2, h1, trivial⟩
    calc
      (∏ k ∈ univ.erase 0, zeroRootLetterWeight c p σ' w' k) =
          zeroRootLetterWeight c p σ' w' u *
            ∏ k ∈ (univ.erase 0).erase u, zeroRootLetterWeight c p σ' w' k :=
        (Finset.mul_prod_erase (univ.erase 0)
          (fun k => zeroRootLetterWeight c p σ' w' k)
          (Finset.mem_erase.mpr ⟨hu0, mem_univ u⟩)).symm
      _ = M c (z (p (σ 0))) *
            ∏ k ∈ S, zeroRootLetterWeight c p σ' w' k := by rw [hletter', hset]
  unfold zeroRootRegularizedWordTerm
  rw [hOld, hNew, hcommon, hphase]
  calc
    _ = (amplitude (anisotropy c) p σ' * z (p (σ 0)) ^ N *
          M c (z (p (σ 0)))) * ((c : ℂ)^2 *
          (∏ k ∈ S, zeroRootLetterWeight c p σ w k) *
          wordPhase (N := N) x p σ w) := by ring
    _ = (amplitude (anisotropy c) p σ * L c (z (p (σ 0)))) *
          ((c : ℂ)^2 * (∏ k ∈ S, zeroRootLetterWeight c p σ w k) *
          wordPhase (N := N) x p σ w) := by rw [hAmpCross]
    _ = _ := by ring

/-- The zero-root zipper move at an arbitrary cyclic edge. -/
theorem zeroRootRegularizedWordTerm_zipper_cyclic {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool)
    (a : Fin (n + 1)) (hσ : σ a = l) (hw : w a = true)
    (hnext : w (finRotate (n + 1) a) = true) :
    zeroRootRegularizedWordTerm (N := N) c x p l
      (σ * Equiv.swap a (finRotate (n + 1) a)) (Function.update w a false) =
    zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
  by_cases hlast : a = Fin.last n
  · subst a
    by_cases hn : 0 < n
    · simpa only [finRotate_last] using
        (zeroRootRegularizedWordTerm_zipper_seam hc x p hp hinj l hpl hBE
          σ w hn hσ (by simpa [finRotate_last] using hnext))
    · have hn0 : n = 0 := by omega
      subst n
      have hflip := zeroRootRegularizedWordTerm_flipRoot (N := N) (n := 0) (c := c) x p l σ w
        0 hσ hpl
      have hperm : σ * Equiv.swap (Fin.last 0) (finRotate 1 (Fin.last 0)) = σ := by
        ext k
        simp
      rw [hperm]
      exact hflip
  · let b : Fin n := ⟨a.val, by
      have ha := a.isLt
      have hne : a.val ≠ n := by
        intro h
        apply hlast
        exact Fin.ext h
      omega⟩
    have hbc : b.castSucc = a := by
      apply Fin.ext
      rfl
    have hbs : b.succ = finRotate (n + 1) a := by
      rw [← hbc]
      exact (finRotate_of_lt b.isLt).symm
    have hstep := zeroRootRegularizedWordTerm_zipper_ordinary (N := N) hc x p hp hinj
      l hpl σ w b (by rw [hbc]; exact hσ)
      (by rw [hbs]; exact hnext)
    simpa [hbc, hbs] using hstep

end PottsDiscontinuity.BetheAnsatz
