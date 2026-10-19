module

public import PottsDiscontinuity.BetheAnsatz.GapRestricted

/-!
# Words in the restricted gap expansion

A true letter denotes L and a false letter denotes M. We first keep the collision
set visible in each coefficient. Summing these coefficients by inclusion-exclusion
is an exact word expansion before the coefficient is collected into ML factors.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Endpoint phase of a word, in the integer predecessor convention. -/
noncomputable def wordPhase {N n : ℕ} (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  ∏ k, positionPhase (p (σ k)) (if w k then cyclicPredecessorPositions N x k else x k)

/-- Local coefficient with the two endpoint constraints recorded explicitly. -/
noncomputable def restrictedLetterCoefficient {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (k : Fin (n + 1)) (b : Bool) : ℂ :=
  if b then (if k ∈ S then 0 else
    if (finRotate (n + 1)).symm k ∈ S then 1 else L c (z (p (σ k))))
  else (if (finRotate (n + 1)).symm k ∈ S then 0 else
    if k ∈ S then 1 else M c (z (p (σ k))))

/-- Coefficient of a word before the sum over collision sets. -/
noncomputable def restrictedWordCoefficient {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  ∏ k, restrictedLetterCoefficient c p σ S k (w k)

/-- The restricted geometric product expanded over all words. -/
theorem restrictedGapSum_eq_sum_words {N n : ℕ} (c : ℝ) (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (hx : StrictMono x)
    (hspan : x (Fin.last n) - x 0 < (N : ℤ)) (hp : ∀ j, z (p j) ≠ 1) :
    restrictedGapSum (N := N) c x p σ S =
      ∑ w : Fin (n + 1) → Bool,
        restrictedWordCoefficient c p σ S w * wordPhase (N := N) x p σ w := by
  rw [restrictedGapSum_eq_product c x p σ S hx hspan hp]
  unfold restrictedWordCoefficient wordPhase
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k (b : Bool) => restrictedLetterCoefficient c p σ S k b *
    positionPhase (p (σ k)) (if b then cyclicPredecessorPositions N x k else x k))]
  apply Finset.prod_congr rfl
  intro k _
  simp only [Fintype.sum_bool, restrictedLetterCoefficient, Bool.false_eq_true,
    ↓reduceIte]
  by_cases hk : k ∈ S <;> by_cases hl : (finRotate (n + 1)).symm k ∈ S <;>
    simp only [hk, hl, ↓reduceIte, zero_mul, one_mul, zero_add, add_zero]

/-- Exact inclusion-exclusion coefficient, prior to collecting the ML factors. -/
noncomputable def inclusionWordCoefficient {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  ∑ S ∈ (univ : Finset (Fin (n + 1))).powerset,
    (-1 : ℂ) ^ S.card * restrictedWordCoefficient c p σ S w

/-- The finite gap sum expanded in words, with the exact uncollected coefficients. -/
theorem cyclicGapSum_eq_sum_words_uncollected {N n : ℕ} (c : ℝ) (x : Fin (n + 2) → ℤ)
    (p : Fin (n + 2) → ℝ) (σ : Equiv.Perm (Fin (n + 2))) (hx : StrictMono x)
    (hspan : x (Fin.last (n + 1)) - x 0 < (N : ℤ)) (hp : ∀ j, z (p j) ≠ 1) :
    cyclicGapSum c N x p σ =
      ∑ w : Fin (n + 2) → Bool,
        inclusionWordCoefficient c p σ w * wordPhase (N := N) x p σ w := by
  rw [cyclicGapSum_inclusion_exclusion c x p σ hx hspan]
  simp_rw [restrictedGapSum_eq_sum_words c x p σ _ hx hspan hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  unfold inclusionWordCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _
  ring

end PottsDiscontinuity.BetheAnsatz
