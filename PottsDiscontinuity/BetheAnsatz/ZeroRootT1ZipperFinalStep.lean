module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1ZipperStep

/-!
# Removing the last zero-root letter in the T₁ zipper

When the unique zero momentum has reached an `L` slot, the remaining letter can
be changed to `M` without a transposition: its singular factor is omitted from
the regularized product, and its plane-wave factor is one.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Flipping the letter at the zero-root slot preserves the regularized word
term. No permutation is needed for this final zipper move. -/
theorem zeroRootRegularizedWordTerm_flipRoot {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool)
    (a : Fin (n + 1)) (hσ : σ a = l) (hpl : p l = 0) :
    zeroRootRegularizedWordTerm (N := N) c x p l σ
      (Function.update w a false) =
    zeroRootRegularizedWordTerm (N := N) c x p l σ w := by
  have hroot : σ.symm l = a := by
    apply σ.injective
    simpa using hσ.symm
  have hprod : zeroRootRegularizedProduct c p l σ (Function.update w a false) =
      zeroRootRegularizedProduct c p l σ w := by
    unfold zeroRootRegularizedProduct
    rw [hroot]
    apply Finset.prod_congr rfl
    intro k hk
    have hka : k ≠ a := (mem_erase.mp hk).1
    simp [zeroRootLetterWeight, Function.update_of_ne hka]
  have hpzero : p (σ a) = 0 := by rw [hσ, hpl]
  have hphase : wordPhase (N := N) x p σ (Function.update w a false) =
      wordPhase (N := N) x p σ w := by
    unfold wordPhase
    apply Finset.prod_congr rfl
    intro k _
    by_cases hka : k = a
    · subst k
      simp [hpzero, positionPhase]
    · simp [Function.update_of_ne hka]
  unfold zeroRootRegularizedWordTerm
  rw [hprod, hphase]

end PottsDiscontinuity.BetheAnsatz
