module

public import PottsDiscontinuity.BetheAnsatz.Scattering

/-!
# Cyclic permutation of the coordinate Bethe amplitudes

Companion paper, Lemma `lem:ratios`, equation (11). The cyclic permutation is
`finRotate`: it sends the last index to zero and each other index to its successor.
-/

@[expose] public section

open Finset Complex

namespace PottsDiscontinuity.BetheAnsatz

private theorem pair_product_succ (n : ℕ) (f : Fin (n + 1) → Fin (n + 1) → ℂ) :
    (∏ i, ∏ j ∈ Ioi i, f i j) =
      (∏ j : Fin n, f 0 j.succ) * (∏ i : Fin n, ∏ j ∈ Ioi i, f i.succ j.succ) := by
  rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
  congr 1
  exact Finset.prod_congr rfl fun i _ => Fin.prod_Ioi_succ (f i.succ) i

private theorem pair_product_last (n : ℕ) (f : Fin (n + 1) → Fin (n + 1) → ℂ) :
    (∏ i, ∏ j ∈ Ioi i, f i j) =
      (∏ i : Fin n, ∏ j ∈ Ioi i, f i.castSucc j.castSucc) *
        (∏ i : Fin n, f i.castSucc (Fin.last n)) := by
  have hi : ∀ i : Fin n, (∏ j ∈ Ioi i.castSucc, f i.castSucc j) =
      (∏ j ∈ Ioi i, f i.castSucc j.castSucc) * f i.castSucc (Fin.last n) := by
    intro i
    rw [← Finset.filter_lt_eq_Ioi, Finset.prod_filter, Fin.prod_univ_castSucc]
    simp only [Fin.castSucc_lt_last, ↓reduceIte, Fin.castSucc_lt_castSucc_iff]
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
  have hl : Ioi (Fin.last n) = ∅ := by
    ext j
    simp only [mem_Ioi, notMem_empty, iff_false]
    exact not_lt_of_ge (Fin.le_last j)
  rw [Fin.prod_univ_castSucc]
  simp only [hl, Finset.prod_empty, mul_one]
  simp_rw [hi]
  rw [Finset.prod_mul_distrib]

/-- Moving the first index to the end reverses exactly its pair factors. -/
theorem pair_product_rotate (n : ℕ) (f : Fin (n + 1) → Fin (n + 1) → ℂ) :
    (∏ i, ∏ j ∈ Ioi i, f (finRotate (n + 1) i) (finRotate (n + 1) j)) *
      (∏ j : Fin n, f 0 j.succ) =
      (∏ i, ∏ j ∈ Ioi i, f i j) * (∏ j : Fin n, f j.succ 0) := by
  have hr : ∀ i : Fin n, finRotate (n + 1) i.castSucc = i.succ := fun i =>
    finRotate_of_lt i.isLt
  rw [pair_product_last, pair_product_succ]
  simp_rw [hr, finRotate_last]
  ring

/-- Cyclic amplitude relation before imposing BE. The phase sum is over all root labels. -/
theorem amplitude_rotate_phase {n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1))) :
    amplitude Δ p (σ * finRotate (n + 1)) =
      (-1 : ℂ) ^ n * Complex.exp (I * ((∑ k, Bethe.theta Δ (p (σ 0)) (p k) : ℝ) : ℂ)) *
        amplitude Δ p σ := by
  let f : Fin (n + 1) → Fin (n + 1) → ℂ := fun i j =>
    z (p (σ i)) * scattering Δ (p (σ i)) (p (σ j))
  let U := ∏ j : Fin n, f 0 j.succ
  let V := ∏ j : Fin n, f j.succ 0
  have hU : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ =>
    mul_ne_zero (z_ne_zero _) (scattering_ne_zero hΔ _ _)
  have hs : (∑ j : Fin n, Bethe.theta Δ (p (σ 0)) (p (σ j.succ))) =
      ∑ k, Bethe.theta Δ (p (σ 0)) (p k) := by
    calc
      _ = ∑ j : Fin (n + 1), Bethe.theta Δ (p (σ 0)) (p (σ j)) := by
        rw [Fin.sum_univ_succ, Bethe.theta_self, zero_add]
      _ = _ := Equiv.sum_comp σ (fun k => Bethe.theta Δ (p (σ 0)) (p k))
  have he : Complex.exp (I * ((∑ k, Bethe.theta Δ (p (σ 0)) (p k) : ℝ) : ℂ)) = V / U := by
    rw [← hs]
    push_cast
    rw [Finset.mul_sum, Complex.exp_sum]
    simp_rw [exp_I_theta_eq_scattering hΔ]
    rw [Finset.prod_div_distrib]
  have hsign : (((Equiv.Perm.sign (σ * finRotate (n + 1)) : ℤ) : ℂ)) =
      (((Equiv.Perm.sign σ : ℤ) : ℂ)) * (-1 : ℂ) ^ n := by
    simp [Equiv.Perm.sign_mul]
  have hcross : amplitude Δ p (σ * finRotate (n + 1)) * U =
      (-1 : ℂ) ^ n * amplitude Δ p σ * V := by
    have hp := pair_product_rotate n f
    unfold amplitude
    rw [hsign]
    change (((((Equiv.Perm.sign σ : ℤ) : ℂ)) * (-1 : ℂ) ^ n) *
      (∏ i, ∏ j ∈ Ioi i, f (finRotate (n + 1) i) (finRotate (n + 1) j))) * U =
      (-1 : ℂ) ^ n * ((((Equiv.Perm.sign σ : ℤ) : ℂ)) * (∏ i, ∏ j ∈ Ioi i, f i j)) * V
    dsimp [U, V]
    linear_combination ((((Equiv.Perm.sign σ : ℤ) : ℂ)) * (-1 : ℂ) ^ n) * hp
  apply mul_right_cancel₀ hU
  rw [he]
  calc
    amplitude Δ p (σ * finRotate (n + 1)) * U = (-1 : ℂ) ^ n * amplitude Δ p σ * V := hcross
    _ = ((-1 : ℂ) ^ n * (V / U) * amplitude Δ p σ) * U := by field_simp

/-- The cyclic amplitude relation from BE, valid also for one particle. -/
theorem amplitude_rotate {N n : ℕ} {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N Δ p)
    (σ : Equiv.Perm (Fin (n + 1))) :
    amplitude Δ p (σ * finRotate (n + 1)) =
      (z (p (σ 0)) ^ N)⁻¹ * amplitude Δ p σ := by
  have hp : z (p (σ 0)) ^ N = (-1 : ℂ) ^ n *
      Complex.exp (-(I * ((∑ k, Bethe.theta Δ (p (σ 0)) (p k) : ℝ) : ℂ))) := by
    calc
      _ = Complex.exp (I * (N : ℂ) * (p (σ 0) : ℂ)) := by
        rw [z, ← Complex.exp_nat_mul]
        congr 1
        ring
      _ = _ := by simpa only [Nat.add_sub_cancel] using hBE (σ 0)
  have hi := congrArg (fun w : ℂ => w⁻¹) hp
  simp only [mul_inv_rev, Complex.exp_neg, inv_inv] at hi
  have hsign_inv : ((-1 : ℂ) ^ n)⁻¹ = (-1 : ℂ) ^ n := by
    rw [← inv_pow]
    norm_num
  rw [hsign_inv] at hi
  have he : (-1 : ℂ) ^ n *
      Complex.exp (I * ((∑ k, Bethe.theta Δ (p (σ 0)) (p k) : ℝ) : ℂ)) =
      (z (p (σ 0)) ^ N)⁻¹ := by simpa only [mul_comm] using hi.symm
  rw [amplitude_rotate_phase hΔ p σ, he]

end PottsDiscontinuity.BetheAnsatz
