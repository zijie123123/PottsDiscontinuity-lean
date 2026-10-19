module

public import PottsDiscontinuity.BetheAnsatz.WordCoefficients

/-!
# Swapping the two momenta at an ML edge

Only one edge coefficient changes: the two momenta occur nowhere else in rσ(w).
This algebraic identity does not require Bethe equations or division by coefficients.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The factor at one cyclic edge in the explicit word coefficient. -/
noncomputable def wordEdgeFactor {n : ℕ} (c : ℝ) (p : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (k : Fin (n + 1)) : ℂ :=
  if w k then
    (if w (finRotate (n + 1) k) then L c (z (p (σ (finRotate (n + 1) k)))) else 1)
  else (if w (finRotate (n + 1) k) then
    M c (z (p (σ k))) * L c (z (p (σ (finRotate (n + 1) k)))) - 1
    else M c (z (p (σ k))))

/-- Every edge other than the chosen ML edge ignores the two swapped momenta. -/
theorem wordEdgeFactor_swap_of_ne {n : ℕ} (c : ℝ) (p : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool)
    {a k : Fin (n + 1)} (ha : w a = false) (hb : w (finRotate (n + 1) a) = true)
    (hk : k ≠ a) :
    wordEdgeFactor c p (σ * Equiv.swap a (finRotate (n + 1) a)) w k =
      wordEdgeFactor c p σ w k := by
  let b := finRotate (n + 1) a
  have hnext : finRotate (n + 1) k ≠ b := fun he => hk ((finRotate _).injective he)
  unfold wordEdgeFactor
  simp only [Equiv.Perm.mul_apply]
  by_cases hkb : k = b
  · subst k
    simp only [show w b = true from hb, ↓reduceIte]
    by_cases hna : finRotate (n + 1) b = a
    · simp only [hna, ha, Bool.false_eq_true, ↓reduceIte]
    · rw [Equiv.swap_apply_of_ne_of_ne hna hnext]
  · have hswap : Equiv.swap a b k = k := Equiv.swap_apply_of_ne_of_ne hk hkb
    rw [hswap]
    by_cases hna : finRotate (n + 1) k = a
    · simp only [hna, ha, Bool.false_eq_true, ↓reduceIte]
    · rw [Equiv.swap_apply_of_ne_of_ne hna hnext]

/-- Cross-multiplication form of the coefficient ratio at any cyclic ML edge. -/
theorem wordCoefficient_swap_cross {n : ℕ} (c : ℝ) (p : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool)
    {a : Fin (n + 1)} (ha : w a = false) (hb : w (finRotate (n + 1) a) = true) :
    wordCoefficient c p (σ * Equiv.swap a (finRotate (n + 1) a)) w *
        (M c (z (p (σ a))) * L c (z (p (σ (finRotate (n + 1) a)))) - 1) =
      wordCoefficient c p σ w *
        (M c (z (p (σ (finRotate (n + 1) a)))) * L c (z (p (σ a))) - 1) := by
  have hab : a ≠ finRotate (n + 1) a := by intro he; rw [← he, ha] at hb; contradiction
  change (∏ k, wordEdgeFactor c p (σ * Equiv.swap a (finRotate (n + 1) a)) w k) * _ =
    (∏ k, wordEdgeFactor c p σ w k) * _
  rw [← Finset.mul_prod_erase univ _ (mem_univ a),
    ← Finset.mul_prod_erase univ (wordEdgeFactor c p σ w) (mem_univ a)]
  have hr : (∏ k ∈ univ.erase a,
      wordEdgeFactor c p (σ * Equiv.swap a (finRotate (n + 1) a)) w k) =
      ∏ k ∈ univ.erase a, wordEdgeFactor c p σ w k := by
    apply Finset.prod_congr rfl
    intro k hk
    exact wordEdgeFactor_swap_of_ne c p σ w ha hb (mem_erase.mp hk).1
  rw [hr]
  simp only [wordEdgeFactor, ha, hb, Bool.false_eq_true, ↓reduceIte,
    Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

/-- Swapping momenta is equivalent to swapping their two coordinates. -/
theorem planeWave_swap {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℤ) (a b : Fin n) :
    planeWave p (σ * Equiv.swap a b) x = planeWave p σ (fun k => x (Equiv.swap a b k)) := by
  unfold planeWave
  simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_self] using
    Equiv.prod_comp (Equiv.swap a b) (fun k =>
      Complex.exp (I * (p (σ k) : ℂ) * (x (Equiv.swap a b k) : ℂ)))

/-- At an ordinary ML edge both selected coordinates are the same integer. -/
theorem wordPhase_adjacent_swap {N n : ℕ} (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin n)
    (ha : w a.castSucc = false) (hb : w a.succ = true) :
    wordPhase (N := N) x p (σ * Equiv.swap a.castSucc a.succ) w =
      wordPhase (N := N) x p σ w := by
  change planeWave p (σ * Equiv.swap a.castSucc a.succ)
    (fun k => if w k then cyclicPredecessorPositions N x k else x k) =
    planeWave p σ (fun k => if w k then cyclicPredecessorPositions N x k else x k)
  rw [planeWave_swap]
  congr 1
  funext k
  by_cases hk : k = a.castSucc
  · subst k
    simp only [Equiv.swap_apply_left, ha, hb, Bool.false_eq_true, ↓reduceIte,
      cyclicPredecessorPositions_succ]
  · by_cases hk' : k = a.succ
    · subst k
      simp only [Equiv.swap_apply_right, ha, hb, Bool.false_eq_true, ↓reduceIte,
        cyclicPredecessorPositions_succ]
    · rw [Equiv.swap_apply_of_ne_of_ne hk hk']

end PottsDiscontinuity.BetheAnsatz
