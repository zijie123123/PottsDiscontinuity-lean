module

public import PottsDiscontinuity.Bethe.DiscreteJacobian

/-! # Explicit coordinates on the symmetric root subspace -/

@[expose] public section

open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- Linear extension of the first-half coordinates in the source basis. -/
noncomputable def discreteSymLift (n : ℕ) : (Fin (n / 2) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun q := ∑ j, q j • discreteSymBasis n j
  map_add' q r := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c q := by simp [mul_smul, Finset.smul_sum]

@[simp]
theorem discreteSymLift_half (n : ℕ) (q : Fin (n / 2) → ℝ) (i : Fin (n / 2)) :
    discreteSymLift n q (discreteHalfIndex n i) = q i := by
  classical
  simp [discreteSymLift, Finset.sum_apply, discreteSymBasis_at_half]

@[simp]
theorem discreteSymLift_single (n : ℕ) (i : Fin (n / 2)) :
    discreteSymLift n (Pi.single i 1) = discreteSymBasis n i := by
  classical
  simp [discreteSymLift, Pi.single_apply, ite_smul, Finset.sum_ite_eq']

theorem discreteSymLift_mem (n : ℕ) (q : Fin (n / 2) → ℝ) :
    discreteSymLift n q ∈ R_n_sym n := by
  change (∑ j, q j • discreteSymBasis n j) ∈ R_n_sym n
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (discreteSymBasis_mem_R_n_sym j)

/-- First-half coordinates determine a symmetric vector, including its middle
coordinate when the number of roots is odd. -/
theorem discreteSym_ext {n : ℕ} {p q : Fin n → ℝ}
    (hp : p ∈ R_n_sym n) (hq : q ∈ R_n_sym n)
    (h : ∀ i : Fin (n / 2), p (discreteHalfIndex n i) = q (discreteHalfIndex n i)) :
    p = q := by
  funext j
  by_cases hj : j.val < n / 2
  · exact h ⟨j.val, hj⟩
  · by_cases hr : (Fin.rev j).val < n / 2
    · have he := h ⟨(Fin.rev j).val, hr⟩
      change p (Fin.rev j) = q (Fin.rev j) at he
      rw [hp j, hq j] at he
      linarith
    · have hfix : Fin.rev j = j := by
        apply Fin.ext
        simp only [Fin.val_rev] at hr ⊢
        omega
      have hpj := hp j
      have hqj := hq j
      rw [hfix] at hpj hqj
      linarith

@[simp]
theorem discreteSymLift_coordinates {n : ℕ} (p : Fin n → ℝ) (hp : p ∈ R_n_sym n) :
    discreteSymLift n (fun i => p (discreteHalfIndex n i)) = p := by
  apply discreteSym_ext (discreteSymLift_mem _ _) hp
  intro i
  exact discreteSymLift_half _ _ _

end PottsDiscontinuity.Bethe
