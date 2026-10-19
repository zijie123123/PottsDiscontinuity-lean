module

public import PottsDiscontinuity.BetheAnsatz.WordRotation

/-!
# Regularized zero-root word terms and an ordinary zipper move

The corrected move takes an `L` at the zero-root slot across the next `L`,
changing that letter to `M` and transposing the two momentum slots. -/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The letter weight at a nonzero-root slot. -/
noncomputable def zeroRootLetterWeight {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (k : Fin (n + 1)) : ℂ :=
  if w k then L c (z (p (σ k))) else M c (z (p (σ k)))

/-- The regularized product omits the slot occupied by the zero root. -/
noncomputable def zeroRootRegularizedProduct {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  ∏ k ∈ (univ : Finset (Fin (n + 1))).erase (σ.symm l),
    zeroRootLetterWeight c p σ w k

/-- The source's `ĝσ(w)`, with a zero momentum label `l` and zero-based positions. -/
noncomputable def zeroRootRegularizedWordTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  amplitude (anisotropy c) p σ * (c : ℂ)^2 *
    zeroRootRegularizedProduct c p l σ w * wordPhase (N := N) x p σ w

/-- Updating an ordinary zipper letter leaves its position phase at the
transposed root slots unchanged, since the moved root has momentum zero. -/
theorem wordPhase_zipper_ordinary {N n : ℕ} (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin n)
    (hb : p (σ a.castSucc) = 0) (hc : w a.succ = true) :
    wordPhase (N := N) x p (σ * Equiv.swap a.castSucc a.succ)
        (Function.update w a.castSucc false) =
      wordPhase (N := N) x p σ w := by
  change planeWave p (σ * Equiv.swap a.castSucc a.succ)
      (wordPositions N x (Function.update w a.castSucc false)) =
    planeWave p σ (wordPositions N x w)
  rw [planeWave_swap]
  unfold planeWave
  apply Finset.prod_congr rfl
  intro k hk
  by_cases hkb : k = a.castSucc
  · subst k
    simp [wordPositions, hb]
  · by_cases hkc : k = a.succ
    · subst k
      have hpred := cyclicPredecessorPositions_succ N x a
      simp [wordPositions, hc, hpred]
    · have hswap := Equiv.swap_apply_of_ne_of_ne hkb hkc
      simp [wordPositions, hkb, hswap]

/-- One ordinary zipper step preserves the regularized word term. -/
theorem zeroRootRegularizedWordTerm_zipper_ordinary {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (a : Fin n)
    (hsig : σ a.castSucc = l) (hcw : w a.succ = true) :
    zeroRootRegularizedWordTerm (N := N) c x p l
        (σ * Equiv.swap a.castSucc a.succ) (Function.update w a.castSucc false) =
      zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
  let b := a.castSucc
  let d := a.succ
  have hbd : b ≠ d := by dsimp [b, d]; exact Fin.castSucc_lt_succ.ne
  have hσb : σ b = l := by simpa [b] using hsig
  have hσd : σ d ≠ l := by
    intro h
    exact hbd (σ.injective (h.trans hσb.symm)).symm
  have hpd : p (σ d) ≠ 0 := by
    intro h
    apply hσd
    exact hinj (h.trans hpl.symm)
  have hzd : z (p (σ d)) ≠ 1 := z_ne_one (hp (σ d)) hpd
  have hM : M c (z (p (σ d))) ≠ 0 := M_ne_zero hc hzd
  have hL : L c (z (p (σ d))) ≠ 0 := L_ne_zero hc hzd
  have hRoot' : (σ * Equiv.swap b d).symm l = d := by
    apply (σ * Equiv.swap b d).injective
    simp [Equiv.Perm.mul_apply, hσb]
  have hσ'b : (σ * Equiv.swap b d) b = σ d := by
    simp [Equiv.Perm.mul_apply, b, d]
  have hw'b : Function.update w b false b = false := by simp
  have hcw' : w d = true := by simpa [d] using hcw
  have hw'c : Function.update w b false d = true := by
    simp [Function.update_of_ne hbd.symm, hcw']
  let S : Finset (Fin (n + 1)) := ((univ.erase b).erase d)
  have hcommon :
      (∏ k ∈ S, zeroRootLetterWeight c p (σ * Equiv.swap b d)
          (Function.update w b false) k) =
        ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkb : k ≠ b := by
      intro he
      subst k
      exact (mem_erase.mp (mem_erase.mp hk).2).1 rfl
    have hkd : k ≠ d := (mem_erase.mp hk).1
    have hσk : (σ * Equiv.swap b d) k = σ k := by
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hkb hkd]
    simp [zeroRootLetterWeight, Function.update_of_ne hkb, hσk]
  have hOld : zeroRootRegularizedProduct c p l σ w =
      L c (z (p (σ d))) * ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
    have hSymm : σ.symm l = b := by
      apply σ.injective
      simpa using hσb.symm
    have hletter : zeroRootLetterWeight c p σ w d =
        L c (z (p (σ d))) := by
      simp [zeroRootLetterWeight, hcw']
    unfold zeroRootRegularizedProduct
    rw [hSymm]
    calc
      (∏ k ∈ univ.erase b, zeroRootLetterWeight c p σ w k) =
          zeroRootLetterWeight c p σ w d *
            ∏ k ∈ (univ.erase b).erase d, zeroRootLetterWeight c p σ w k :=
        (Finset.mul_prod_erase (univ.erase b)
          (fun k => zeroRootLetterWeight c p σ w k)
          (Finset.mem_erase.mpr ⟨hbd.symm, mem_univ d⟩)).symm
      _ = L c (z (p (σ d))) * ∏ k ∈ S, zeroRootLetterWeight c p σ w k := by
        rw [hletter]
  have hNew : zeroRootRegularizedProduct c p l
      (σ * Equiv.swap b d) (Function.update w b false) =
      M c (z (p (σ d))) * ∏ k ∈ S,
        zeroRootLetterWeight c p (σ * Equiv.swap b d)
          (Function.update w b false) k := by
    have hletter : zeroRootLetterWeight c p (σ * Equiv.swap b d)
        (Function.update w b false) b = M c (z (p (σ d))) := by
      simp [zeroRootLetterWeight, hσ'b]
    have hset : (univ.erase d).erase b = S := by
      ext k
      simp only [S, Finset.mem_erase, Finset.mem_univ]
      constructor <;> rintro ⟨h1, h2, _⟩ <;> exact ⟨h2, h1, trivial⟩
    unfold zeroRootRegularizedProduct
    rw [hRoot']
    calc
      (∏ k ∈ univ.erase d,
          zeroRootLetterWeight c p (σ * Equiv.swap b d)
            (Function.update w b false) k) =
          zeroRootLetterWeight c p (σ * Equiv.swap b d)
              (Function.update w b false) b *
            ∏ k ∈ (univ.erase d).erase b,
              zeroRootLetterWeight c p (σ * Equiv.swap b d)
                (Function.update w b false) k :=
        (Finset.mul_prod_erase (univ.erase d)
          (fun k => zeroRootLetterWeight c p (σ * Equiv.swap b d)
            (Function.update w b false) k)
          (Finset.mem_erase.mpr ⟨hbd, mem_univ b⟩)).symm
      _ = M c (z (p (σ d))) * ∏ k ∈ S,
            zeroRootLetterWeight c p (σ * Equiv.swap b d)
              (Function.update w b false) k := by
        rw [hletter, hset]
  have hprodCross :
      zeroRootRegularizedProduct c p l (σ * Equiv.swap b d)
          (Function.update w b false) * L c (z (p (σ d))) =
        zeroRootRegularizedProduct c p l σ w * M c (z (p (σ d))) := by
    rw [hNew, hOld, hcommon]
    ring
  have hbzero : p (σ a.castSucc) = 0 := by rw [hsig]; exact hpl
  have hphase := wordPhase_zipper_ordinary (N := N) x p σ w a hbzero hcw
  have hAmp : amplitude (anisotropy c) p (σ * Equiv.swap b d) *
      M c (z (p (σ d))) =
    amplitude (anisotropy c) p σ * L c (z (p (σ d))) := by
    have hθ := exp_I_theta_zero_eq_neg_L_div_M hc hzd
    have hadj : b.val + 1 = d.val := by simp [b, d]
    have hswap := amplitude_adjacent_swap (anisotropy_lt_neg_one hc) p σ
      (a := b) (b := d) hadj
    rw [hσb, hpl] at hswap
    calc
      _ = (-Complex.exp (I * (Bethe.theta (anisotropy c) 0
          (p (σ d)) : ℂ)) * amplitude (anisotropy c) p σ) *
            M c (z (p (σ d))) := by rw [hswap]
      _ = amplitude (anisotropy c) p σ * L c (z (p (σ d))) := by
        rw [hθ]
        field_simp [hM]
  have hAP : amplitude (anisotropy c) p (σ * Equiv.swap b d) *
      zeroRootRegularizedProduct c p l (σ * Equiv.swap b d)
        (Function.update w b false) =
    amplitude (anisotropy c) p σ * zeroRootRegularizedProduct c p l σ w := by
    apply mul_right_cancel₀ hL
    calc
      (amplitude (anisotropy c) p (σ * Equiv.swap b d) *
          zeroRootRegularizedProduct c p l (σ * Equiv.swap b d)
            (Function.update w b false)) * L c (z (p (σ d))) =
        amplitude (anisotropy c) p (σ * Equiv.swap b d) *
          (zeroRootRegularizedProduct c p l σ w * M c (z (p (σ d)))) := by
            calc
              _ = amplitude (anisotropy c) p (σ * Equiv.swap b d) *
                    (zeroRootRegularizedProduct c p l
                      (σ * Equiv.swap b d) (Function.update w b false) *
                      L c (z (p (σ d)))) := by ring
              _ = _ := by rw [hprodCross]
      _ = amplitude (anisotropy c) p σ *
          (zeroRootRegularizedProduct c p l σ w * L c (z (p (σ d)))) := by
            calc
              _ = (amplitude (anisotropy c) p (σ * Equiv.swap b d) *
                    M c (z (p (σ d)))) * zeroRootRegularizedProduct c p l σ w := by ring
              _ = (amplitude (anisotropy c) p σ *
                    L c (z (p (σ d)))) * zeroRootRegularizedProduct c p l σ w := by
                    rw [hAmp]
              _ = _ := by ring
      _ = (amplitude (anisotropy c) p σ *
          zeroRootRegularizedProduct c p l σ w) * L c (z (p (σ d))) := by ring
  unfold zeroRootRegularizedWordTerm
  rw [hphase]
  change amplitude (anisotropy c) p (σ * Equiv.swap b d) * (c : ℂ)^2 *
      zeroRootRegularizedProduct c p l (σ * Equiv.swap b d)
        (Function.update w b false) * wordPhase (N := N) x p σ w =
    amplitude (anisotropy c) p σ * (c : ℂ)^2 *
      zeroRootRegularizedProduct c p l σ w * wordPhase (N := N) x p σ w
  calc
    _ = ((amplitude (anisotropy c) p (σ * Equiv.swap b d) *
          zeroRootRegularizedProduct c p l (σ * Equiv.swap b d)
            (Function.update w b false)) * (c : ℂ)^2) *
          wordPhase (N := N) x p σ w := by ring_nf
    _ = ((amplitude (anisotropy c) p σ *
          zeroRootRegularizedProduct c p l σ w) * (c : ℂ)^2) *
          wordPhase (N := N) x p σ w := by rw [hAP]
    _ = amplitude (anisotropy c) p σ * (c : ℂ)^2 *
        zeroRootRegularizedProduct c p l σ w * wordPhase (N := N) x p σ w := by ring

end PottsDiscontinuity.BetheAnsatz
