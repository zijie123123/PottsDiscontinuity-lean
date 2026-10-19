module

public import PottsDiscontinuity.BetheAnsatz.Scattering

/-!
# Bethe products with one zero root

The zero-root Bethe equation and equation (19) imply equality of the products
of L and M over the remaining roots. This is the cancellation in the T₀ terms.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The L and M products over all nonzero roots agree at a zero-root Bethe solution. -/
theorem prod_L_eq_prod_M_of_zero {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (n + 1) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    (∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, L c (z (p j))) =
      ∏ j ∈ (univ : Finset (Fin (n + 1))).erase l, M c (z (p j)) := by
  let s : Finset (Fin (n + 1)) := univ.erase l
  let θ : Fin (n + 1) → ℝ := fun j => Bethe.theta (anisotropy c) 0 (p j)
  have hsum : (∑ j ∈ s, θ j) = ∑ j, θ j := by
    rw [← Finset.sum_erase_add (s := (univ : Finset (Fin (n + 1))))
      (f := θ) (a := l) (mem_univ l)]
    simp [s, θ, hpl, Bethe.theta_self]
  have heq : (1 : ℂ) = (-1 : ℂ) ^ n *
      Complex.exp (-(I * ((∑ j ∈ s, θ j : ℝ) : ℂ))) := by
    have hh := hBE l
    rw [hpl] at hh
    simpa [θ, ← hsum, Nat.add_sub_cancel] using hh
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    calc
      (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = (-1 : ℂ) ^ (n + n) := by rw [pow_add]
      _ = (-1 : ℂ) ^ (2 * n) := by congr 1; omega
      _ = ((-1 : ℂ) ^ 2) ^ n := by rw [pow_mul]
      _ = 1 := by norm_num
  have hsignne : (-1 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hneg : Complex.exp (-(I * ((∑ j ∈ s, θ j : ℝ) : ℂ))) = (-1 : ℂ) ^ n := by
    apply mul_left_cancel₀ hsignne
    exact heq.symm.trans hsign.symm
  have hpos : Complex.exp (I * ((∑ j ∈ s, θ j : ℝ) : ℂ)) = (-1 : ℂ) ^ n := by
    calc
      _ = (Complex.exp (-(I * ((∑ j ∈ s, θ j : ℝ) : ℂ))) : ℂ)⁻¹ := by
        rw [Complex.exp_neg]
        simp
      _ = (-1 : ℂ) ^ n := by
        rw [hneg]
        have hinv : ((-1 : ℂ) ^ n)⁻¹ = (-1 : ℂ) ^ n := by
          rw [← inv_pow]
          norm_num
        exact hinv
  have hphaseprod : (∏ j ∈ s, Complex.exp (I * (θ j : ℂ))) = (-1 : ℂ) ^ n := by
    rw [← Complex.exp_sum]
    have hcast : (∑ j ∈ s, I * (θ j : ℂ)) = I * ((∑ j ∈ s, θ j : ℝ) : ℂ) := by
      push_cast
      rw [← Finset.mul_sum]
    rw [hcast]
    exact hpos
  have hlocal : ∀ j ∈ s, Complex.exp (I * (θ j : ℂ)) =
      -L c (z (p j)) / M c (z (p j)) := by
    intro j hj
    have hjl : j ≠ l := (mem_erase.mp hj).1
    have hpj0 : p j ≠ 0 := by
      intro hzero
      apply hjl
      apply hinj
      rw [hzero, hpl]
    exact exp_I_theta_zero_eq_neg_L_div_M_of_mem hc (hp j) hpj0
  have hMne : ∏ j ∈ s, M c (z (p j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hjl : j ≠ l := (mem_erase.mp hj).1
    have hpj0 : p j ≠ 0 := by
      intro hzero
      apply hjl
      apply hinj
      rw [hzero, hpl]
    exact M_ne_zero hc (z_ne_one (hp j) hpj0)
  have hratio : (∏ j ∈ s, L c (z (p j))) / (∏ j ∈ s, M c (z (p j))) = 1 := by
    have hcalc : (∏ j ∈ s, Complex.exp (I * (θ j : ℂ))) =
        (-1 : ℂ) ^ n *
          ((∏ j ∈ s, L c (z (p j))) / (∏ j ∈ s, M c (z (p j)))) := by
      calc
        _ = ∏ j ∈ s, (-L c (z (p j)) / M c (z (p j))) := by
          apply Finset.prod_congr rfl
          intro j hj
          exact hlocal j hj
        _ = ∏ j ∈ s, ((-1 : ℂ) * (L c (z (p j)) / M c (z (p j)))) := by
          apply Finset.prod_congr rfl
          intro j hj
          ring
        _ = (∏ j ∈ s, (-1 : ℂ)) * (∏ j ∈ s, (L c (z (p j)) / M c (z (p j)))) :=
          Finset.prod_mul_distrib
        _ = _ := by
          rw [Finset.prod_div_distrib]
          simp [s, Finset.card_erase_of_mem (mem_univ l)]
    have hs : (-1 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hcancel := hcalc.symm.trans hphaseprod
    exact (mul_left_cancel₀ hs) (by simpa using hcancel)
  exact (div_eq_one_iff_eq hMne).mp hratio

end PottsDiscontinuity.BetheAnsatz
