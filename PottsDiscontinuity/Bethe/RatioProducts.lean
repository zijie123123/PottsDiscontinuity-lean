module

public import PottsDiscontinuity.BetheAnsatz.Scattering
public import PottsDiscontinuity.Bethe.DiscreteCore

/-!
# Symmetric products in the two Bethe eigenvalue formulas

Source: L1500–1504 and L1531–1535. These are scalar identities; no claim
identifying a scalar with a transfer-matrix eigenvalue is needed here.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

theorem ratio_z_neg (x : ℝ) : z (-x) = conj (z x) := by
  rw [z, z, ← Complex.exp_conj]
  congr 1
  simp

theorem ratio_M_neg (c x : ℝ) : M c (z (-x)) = conj (M c (z x)) := by
  simp [M, ratio_z_neg]

theorem ratio_L_eq_M_neg (c x : ℝ) : L c (z x) = M c (z (-x)) := by
  have hz := z_ne_zero x
  have hneg : z (-x) = (z x)⁻¹ := by
    simp only [z, Complex.ofReal_neg, mul_neg, Complex.exp_neg]
  rw [hneg]
  by_cases hx : z x = 1
  · simp [L, M, hx]
  · have hd : 1 - z x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hi : 1 - (z x)⁻¹ ≠ 0 := by
      intro h
      have he : (z x)⁻¹ = 1 := (sub_eq_zero.mp h).symm
      exact hx (inv_eq_one.mp he)
    unfold L M
    field_simp
    ring

theorem ratio_M_ne_zero {c : ℝ} (hc : 2 < c) (x : ℝ) : M c (z x) ≠ 0 := by
  by_cases hx : z x = 1
  · simp [M, hx]
  · exact M_ne_zero hc hx

/-- Pairing complex conjugates yields a positive real product; fixed points
are allowed exactly when their factor is already its nonnegative modulus. -/
theorem ratio_prod_eq_prod_norm {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ) (g : ι → ι)
    (hmem : ∀ i ∈ s, g i ∈ s) (hinv : ∀ i ∈ s, g (g i) = i)
    (hconj : ∀ i ∈ s, f (g i) = conj (f i))
    (hne : ∀ i ∈ s, f i ≠ 0)
    (hfix : ∀ i ∈ s, g i = i → f i = (‖f i‖ : ℂ)) :
    (∏ i ∈ s, f i) = ((∏ i ∈ s, ‖f i‖ : ℝ) : ℂ) := by
  have hnorm (i : ι) (hi : i ∈ s) : (‖f i‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr (hne i hi))
  have hprod : ∏ i ∈ s, f i / (‖f i‖ : ℂ) = 1 := by
    apply Finset.prod_involution (fun i _ => g i)
    · intro i hi
      rw [hconj i hi, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj', pow_two]
      exact div_self (mul_ne_zero (hnorm i hi) (hnorm i hi))
    · intro i hi hnot hgi
      apply hnot
      exact (div_eq_one_iff_eq (hnorm i hi)).mpr (hfix i hi hgi)
    · exact hmem
    · exact hinv
  rw [Finset.prod_div_distrib] at hprod
  have hpne : (∏ i ∈ s, (‖f i‖ : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hnorm
  rw [div_eq_one_iff_eq hpne] at hprod
  simpa only [Complex.ofReal_prod] using hprod

/-- The product of `M` factors for a symmetric ordered configuration is
positive real, including when the total definition is evaluated at zero. -/
theorem ratio_symmetric_M_product {n : ℕ} {p : Fin n → ℝ}
    {c : ℝ} (hc : 2 < c) (hp : p ∈ S_n n) :
    (∏ j, M c (z (p j))) = ((∏ j, ‖M c (z (p j))‖ : ℝ) : ℂ) := by
  apply ratio_prod_eq_prod_norm univ _ Fin.rev
  · intro i hi
    exact mem_univ _
  · intro i hi
    exact Fin.rev_rev i
  · intro i hi
    rw [show p (Fin.rev i) = -p i from hp.2.2 i, ratio_M_neg]
  · intro i hi
    exact ratio_M_ne_zero hc _
  · intro i hi hfix
    have hs := hp.2.2 i
    rw [hfix] at hs
    have hz : p i = 0 := by linarith
    simp [hz, M]

/-- The regular expression, for the even-root branch of the source. -/
theorem ratio_eigenvalueRegular {n : ℕ} {p : Fin n → ℝ}
    {c : ℝ} (hc : 2 < c) (hp : p ∈ S_n n) :
    eigenvalueRegular c p = ((2 * ∏ j, ‖M c (z (p j))‖ : ℝ) : ℂ) := by
  have hL : (∏ j, L c (z (p j))) = ∏ j, M c (z (p j)) := by
    calc
      _ = ∏ j, M c (z (p (Fin.rev j))) := by
        apply prod_congr rfl
        intro j hj
        rw [show p (Fin.rev j) = -p j from hp.2.2 j, ratio_L_eq_M_neg]
      _ = _ := Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin n)) (fun j => M c (z (p j)))
  rw [eigenvalueRegular, hL, ratio_symmetric_M_product hc hp]
  push_cast
  ring

/-- Pairing after removing the zero root gives the modulus product appearing
in the odd branch, without an extra factor of two. -/
theorem ratio_zero_erased_M_product {n : ℕ} {p : Fin n → ℝ}
    {c : ℝ} (hc : 2 < c) (hp : p ∈ S_n n) (l : Fin n) (hl : p l = 0) :
    (∏ j ∈ univ.erase l, M c (z (p j))) =
      ((∏ j ∈ univ.erase l, ‖M c (z (p j))‖ : ℝ) : ℂ) := by
  have hlrev : Fin.rev l = l := hp.2.1.injective (by rw [hp.2.2 l, hl, neg_zero])
  apply ratio_prod_eq_prod_norm (univ.erase l) _ Fin.rev
  · intro j hj
    simp only [mem_erase, mem_univ, and_true] at hj ⊢
    intro he
    have hi := congrArg Fin.rev he
    rw [Fin.rev_rev, hlrev] at hi
    exact hj hi
  · intro j hj
    exact Fin.rev_rev j
  · intro j hj
    rw [show p (Fin.rev j) = -p j from hp.2.2 j, ratio_M_neg]
  · intro j hj
    exact ratio_M_ne_zero hc _
  · intro j hj hfix
    have hs := hp.2.2 j
    rw [hfix] at hs
    have hz : p j = 0 := by linarith
    simp [hz, M]

/-- Exact real form of the source zero-root expression. -/
theorem ratio_eigenvalueZero {N n : ℕ} {p : Fin n → ℝ}
    {c : ℝ} (hc : 2 < c) (hp : p ∈ S_n n) (l : Fin n) (hl : p l = 0) :
    eigenvalueZero N c p l =
      (((2 + c ^ 2 * ((N : ℝ) - 1) + c ^ 2 *
        ∑ j ∈ univ.erase l, deriv (fun t => theta (anisotropy c) t (p j)) 0) *
        ∏ j ∈ univ.erase l, ‖M c (z (p j))‖ : ℝ) : ℂ) := by
  have hd (j : Fin n) :
      deriv (fun t : ℝ => (theta (anisotropy c) t (p j) : ℂ)) 0 =
        (deriv (fun t => theta (anisotropy c) t (p j)) 0 : ℝ) :=
    (analyticAt_theta_left (anisotropy_lt_neg_one hc) 0 (p j)).differentiableAt.hasDerivAt.ofReal_comp.deriv
  rw [eigenvalueZero, ratio_zero_erased_M_product hc hp l hl]
  push_cast
  simp_rw [hd]

end PottsDiscontinuity.Bethe
