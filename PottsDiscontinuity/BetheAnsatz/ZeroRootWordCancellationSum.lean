module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordCancellation

/-!
# Cancellation on a fixed zero-root slot

For a fixed word and a fixed slot occupied by the perturbed root, every ML edge
disjoint from that slot pairs the constrained permutation sum with its negative.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Permutations which place the distinguished label at a fixed slot. -/
abbrev RootSlotPerm {n : ℕ} (l r : Fin (n + 1)) :=
  {σ : Equiv.Perm (Fin (n + 1)) // σ r = l}

/-- A transposition away from the root slot preserves the constrained
permutation fiber and is an involution on it. -/
theorem sum_fixedAmplitudeWordTerm_eq_zero_of_ML_away {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (hn : 0 < n)
    (p : Fin (n + 1) → ℝ) (q : Fin (n + 1) → ℝ)
    (x : Fin (n + 1) → ℤ) (l r a : Fin (n + 1))
    (w : Fin (n + 1) → Bool)
    (hBE : BetheEquations N (anisotropy c) p)
    (hAgree : ∀ k, k ≠ l → q k = p k)
    (hNotOne : ∀ k, k ≠ l → z (p k) ≠ 1)
    (ha : w a = false) (hb : w (finRotate (n + 1) a) = true)
    (hra : r ≠ a) (hrb : r ≠ finRotate (n + 1) a) :
    (∑ σ : RootSlotPerm l r,
      fixedAmplitudeWordTerm (N := N) c x p q σ.1 w) = 0 := by
  classical
  let b := finRotate (n + 1) a
  have hswapRoot (σ : RootSlotPerm l r) : (σ.1 * Equiv.swap a b) r = l := by
    change σ.1 (Equiv.swap a b r) = l
    rw [Equiv.swap_apply_of_ne_of_ne hra hrb]
    exact σ.2
  let e : RootSlotPerm l r ≃ RootSlotPerm l r := {
    toFun := fun σ => ⟨σ.1 * Equiv.swap a b, hswapRoot σ⟩
    invFun := fun σ => ⟨σ.1 * Equiv.swap a b, hswapRoot σ⟩
    left_inv := by
      intro σ
      apply Subtype.ext
      ext k
      simp
    right_inv := by
      intro σ
      apply Subtype.ext
      ext k
      simp }
  have hslot (σ : RootSlotPerm l r) (k : Fin (n + 1)) (hk : k ≠ r) :
      σ.1 k ≠ l := by
    intro h
    apply hk
    exact σ.1.injective (h.trans σ.2.symm)
  have hcancel (σ : RootSlotPerm l r) :
      fixedAmplitudeWordTerm (N := N) c x p q (e σ).1 w =
        -fixedAmplitudeWordTerm (N := N) c x p q σ.1 w := by
    have hσa := hslot σ a hra.symm
    have hσb := hslot σ b hrb.symm
    have hqa : q (σ.1 a) = p (σ.1 a) := hAgree _ hσa
    have hqb : q (σ.1 b) = p (σ.1 b) := hAgree _ hσb
    by_cases hseam : a = Fin.last n
    · subst a
      have hlast : b = 0 := by simp [b]
      have hha : w (Fin.last n) = false := ha
      have hhb : w 0 = true := by simpa [finRotate_last] using hb
      have hσ0 : σ.1 0 ≠ l := hslot σ 0 (by
        simpa [finRotate_last] using hrb.symm)
      have hq0 : q (σ.1 0) = p (σ.1 0) := hAgree _ hσ0
      have hleft := fixedAmplitudeWordTerm_seam_swap hc p q x hBE σ.1 w hn
        hha hhb hqa hq0 (hNotOne _ hσa) (hNotOne _ hσ0)
      simpa [e, hlast] using hleft
    · obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hseam
      have hrj : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
      have hb' : b = j.succ := by
        dsimp [b]
        rw [← hj, hrj]
      have hqa' : q (σ.1 j.castSucc) = p (σ.1 j.castSucc) := by
        simpa [hj] using hqa
      have hqb' : q (σ.1 j.succ) = p (σ.1 j.succ) := by
        simpa [hb'] using hqb
      have hza' : z (p (σ.1 j.castSucc)) ≠ 1 := by
        simpa [hj] using hNotOne _ hσa
      have hzb' : z (p (σ.1 j.succ)) ≠ 1 := by
        simpa [hb'] using hNotOne _ hσb
      have hha : w j.castSucc = false := by simpa [hj] using ha
      have hhb : w j.succ = true := by
        rw [← hb']
        exact hb
      have hleft := fixedAmplitudeWordTerm_adjacent_swap (N := N) hc p q x σ.1 w j
        hha hhb hqa' hqb' hza' hzb'
      change fixedAmplitudeWordTerm (N := N) c x p q
        (σ.1 * Equiv.swap a b) w = _
      rw [← hj, hb']
      exact hleft
  let f : RootSlotPerm l r → ℂ := fun σ =>
    fixedAmplitudeWordTerm (N := N) c x p q σ.1 w
  have hEq : (∑ σ : RootSlotPerm l r, f σ) =
      ∑ σ : RootSlotPerm l r, f (e σ) := (Equiv.sum_comp e f).symm
  dsimp only [f] at hEq
  simp_rw [hcancel] at hEq
  rw [Finset.sum_neg_distrib] at hEq
  linear_combination (1 / 2 : ℂ) * hEq

end PottsDiscontinuity.BetheAnsatz
