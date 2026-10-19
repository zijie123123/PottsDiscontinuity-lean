module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.Conventions
public import PottsDiscontinuity.BetheAnsatz.Scattering
public import PottsDiscontinuity.SixVertex.Cor34BetheBase
public import PottsDiscontinuity.SixVertex.Cor34BetheEigenvalue
public import PottsDiscontinuity.SixVertex.Cor34Cyclotomic
public import PottsDiscontinuity.SixVertex.InfinityValue

/-!
# Corollary 3.4: specialize the Bethe eigenvalue limit at the discrete base

This module identifies the generic continuous-family eigenvalue limits with the centered
cyclotomic products in (3.5), then evaluates them for the full range `r ≥ 0`.
-/

@[expose] public section

open Finset Complex Filter Topology
open PottsDiscontinuity.PerronFrobenius
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

/-- The centered base momenta have total momentum zero, so their phases multiply to one. -/
theorem cor34_base_z_product_eq_one {N n : ℕ} (hN : 0 < N) (hn : 2 * n ≤ N) :
    (∏ j : Fin n, BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 1 := by
  rw [BetheAnsatz.prod_z_eq_exp_sum]
  have hp := Bethe.discreteBaseSolution_mem_S_n hN hn
  have hsum := Bethe.sum_eq_zero_of_mem_R_n_sym hp.2.2
  rw [hsum]
  simp

private theorem cor34_discreteIndex_ne_zero_of_even {n : ℕ} (hn : Even n) (j : Fin n) :
    Bethe.discreteBetheIndex n j ≠ 0 := by
  intro h
  have hnat : 2 * (j.val + 1) = n + 1 := by
    have hreal : 2 * ((j.val : ℝ) + 1) = (n : ℝ) + 1 := by
      dsimp [Bethe.discreteBetheIndex] at h
      linarith
    exact_mod_cast hreal
  rcases hn with ⟨k, hk⟩
  omega

private theorem cor34_base_momentum_ne_zero_of_even {N n : ℕ}
    (hn : Even n) (hbound : 2 * n ≤ N) (j : Fin n) :
    Bethe.discreteBaseSolution N n j ≠ 0 := by
  have hnpos : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hlt : n < N := by omega
  have hden : ((N - n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt))
  unfold Bethe.discreteBaseSolution
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (cor34_discreteIndex_ne_zero_of_even hn j)) hden

/-- No even-parity base momentum is a zero root. -/
theorem cor34_base_z_ne_one_of_even {N n : ℕ} (hN : 0 < N) (hbound : 2 * n ≤ N)
    (hn : Even n) (j : Fin n) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n j) ≠ 1 := by
  have hp := Bethe.discreteBaseSolution_mem_S_n hN hbound
  exact BetheAnsatz.z_ne_one (hp.1 j)
    (cor34_base_momentum_ne_zero_of_even hn hbound j)

/-- The normalized even Bethe eigenvalue has the denominator form in (3.5), before
cyclotomic evaluation. -/
theorem cor34_normalizedRegularEigenvalue_base_limit {N n : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hN : 0 < N) (hbound : 2 * n ≤ N) (hn : Even n) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 ((2 : ℂ) / ∏ j : Fin n,
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)))) := by
  have hlim := cor34_normalizedRegularEigenvalue_tendsto hp
    (fun j => by simpa [hp0] using cor34_base_z_ne_one_of_even hN hbound hn j)
  have hprod := cor34_base_z_product_eq_one hN hbound
  have hsign : (-1 : ℂ) ^ n = 1 := by
    obtain ⟨k, hk⟩ := hn
    rw [hk, pow_add]
    rw [← mul_pow]
    norm_num
  have hform :
      (∏ j : Fin n,
          BetheAnsatz.z (Bethe.discreteBaseSolution N n j) /
            (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j))) +
        ∏ j : Fin n,
          (-1 : ℂ) /
            (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
        (2 : ℂ) / ∏ j : Fin n,
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) := by
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hsign, hprod]
    ring
  rw [hp0] at hlim
  rw [hform] at hlim
  exact hlim

private theorem cor34_even_base_denominator_at_r_zero {N n : ℕ}
    (hnpos : 0 < n) (hn : Even n) (hN : N = 2 * n) :
    ∏ j : Fin n,
      (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 2 := by
  classical
  have hnN : n < N := by omega
  let η : ℂ := cor34_halfRoot n
  let ζ : ℂ := η ^ 2
  let α : ℂ := η ^ (n + 1)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  have h2n : 2 * n ≠ 0 := by omega
  have hηeq : η = Complex.exp (2 * Real.pi * Complex.I / (2 * n : ℂ)) := by
    dsimp [η, cor34_halfRoot]
    congr 1
    field_simp [hnR]
  have hηroot : IsPrimitiveRoot η (2 * n) := by
    rw [hηeq]
    convert Complex.isPrimitiveRoot_exp (2 * n) h2n using 1
    congr 1
    norm_num
  have hζroot : IsPrimitiveRoot ζ n := by
    dsimp [ζ]
    exact hηroot.pow (by omega) (by omega)
  have hηnroot : IsPrimitiveRoot (η ^ n) 2 :=
    hηroot.pow (by omega) (by omega)
  have hηn : η ^ n = -1 := hηnroot.eq_neg_one_of_two_right
  have hnplusOdd : Odd (n + 1) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, by omega⟩
  have hαpow : α ^ n = -1 := by
    dsimp [α]
    calc
      (η ^ (n + 1)) ^ n = (η ^ n) ^ (n + 1) := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ = (-1 : ℂ) ^ (n + 1) := by rw [hηn]
      _ = -1 := (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).2 hnplusOdd
  have hp := X_pow_sub_C_eq_prod hζroot (α := α) (a := -1) (by omega) hαpow
  have heval := congrArg (Polynomial.eval (1 : ℂ)) hp
  have hprod : (∏ i ∈ Finset.range n, (1 - ζ ^ i * α)) = 2 := by
    norm_num [Polynomial.eval_prod] at heval ⊢
    exact heval.symm
  have hηne : η ≠ 0 := by
    dsimp [η, cor34_halfRoot]
    exact Complex.exp_ne_zero _
  have hperiod : η ^ (2 * (n : ℤ)) = 1 := by
    convert hηroot.zpow_eq_one using 1; norm_cast
  have hphase (j : Fin n) :
      BetheAnsatz.z (Bethe.discreteBaseSolution N n j) = η ^ (n + 1 + 2 * j.val) := by
    have hNm : N - n = n := by omega
    calc
      BetheAnsatz.z (Bethe.discreteBaseSolution N n j) =
          η ^ (2 * (j.val : ℤ) + 1 - (n : ℤ)) := by
        simpa [η, hNm] using cor34_base_z_eq_halfRoot_zpow hnN j
      _ = η ^ (2 * (j.val : ℤ) + 1 - (n : ℤ)) * η ^ (2 * (n : ℤ)) := by
        rw [hperiod, mul_one]
      _ = η ^ ((2 * (j.val : ℤ) + 1 - (n : ℤ)) + 2 * (n : ℤ)) :=
        (zpow_add₀ hηne _ _).symm
      _ = η ^ ((n + 1 + 2 * j.val : ℕ) : ℤ) := by congr 1; omega
      _ = η ^ (n + 1 + 2 * j.val) := by rw [zpow_natCast]
  have hterm (j : Fin n) :
      η ^ (n + 1 + 2 * j.val) = ζ ^ j.val * α := by
    dsimp [ζ, α]
    rw [pow_add, pow_mul]
    ring
  let f : ℕ → ℂ := fun i => if hi : i < n then
    1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n ⟨i, hi⟩) else 1
  calc
    ∏ j : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
        ∏ j : Fin n, f j := by
          apply Finset.prod_congr rfl
          intro j hj
          simp [f]
    _ = ∏ i ∈ Finset.range n, f i := Fin.prod_univ_eq_prod_range f n
    _ = ∏ i ∈ Finset.range n, (1 - ζ ^ i * α) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hin : i < n := Finset.mem_range.mp hi
          simp only [f, dite_eq_left hin]
          simpa using congrArg (fun z : ℂ => 1 - z) (hphase ⟨i, hin⟩ |>.trans (hterm ⟨i, hin⟩))
    _ = 2 := hprod

private theorem cor34_odd_base_momentum_ne_zero {N n q : ℕ} (hnq : n + 1 = 2 * q)
    (hbound : 2 * n ≤ N) (j : Fin n)
    (hcenter : j ≠ ⟨q - 1, by omega⟩) :
    Bethe.discreteBaseSolution N n j ≠ 0 := by
  have hindex : Bethe.discreteBetheIndex n j ≠ 0 := by
    intro h
    have hval : j.val + 1 = q := by
      have hreal : 2 * ((j.val : ℝ) + 1) = (n : ℝ) + 1 := by
        dsimp [Bethe.discreteBetheIndex] at h
        linarith
      have hnat : 2 * (j.val + 1) = n + 1 := by exact_mod_cast hreal
      omega
    have hval' : j.val = (⟨q - 1, by omega⟩ : Fin n).val := by
      change j.val = q - 1
      omega
    exact hcenter (Fin.ext hval')
  have hnpos : 0 < n := by omega
  have hlt : n < N := by omega
  have hden : ((N - n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt))
  unfold Bethe.discreteBaseSolution
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hindex) hden

/-- All nonzero-root factors in the odd limiting eigenvalue are regular. -/
theorem cor34_odd_base_z_ne_one {N n q : ℕ} (hN : 0 < N) (hbound : 2 * n ≤ N)
    (hnq : n + 1 = 2 * q) (j : Fin n)
    (hj : j ∈ Finset.univ.erase ⟨q - 1, by omega⟩) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n j) ≠ 1 := by
  have hp := Bethe.discreteBaseSolution_mem_S_n hN hbound
  apply BetheAnsatz.z_ne_one (hp.1 j)
  exact cor34_odd_base_momentum_ne_zero hnq hbound j (by
    intro heq
    exact (Finset.mem_erase.mp hj).1 heq)

/-- The normalized odd Bethe eigenvalue has the denominator form in (3.5), before
cyclotomic evaluation. -/
theorem cor34_normalizedZeroEigenvalue_base_limit {N n q : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hN : 0 < N) (hbound : 2 * n ≤ N)
    (hnq : n + 1 = 2 * q) :
    Tendsto
      (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
        (⟨q - 1, by omega⟩ : Fin n))
      (𝓝 0)
      (𝓝 (((N : ℂ) - (n : ℂ)) /
        ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)))) := by
  let l : Fin n := ⟨q - 1, by omega⟩
  have hlim := cor34_normalizedZeroEigenvalue_tendsto (N := N) hp l
    (fun j hj => by simpa [hp0] using cor34_odd_base_z_ne_one hN hbound hnq j hj)
  have hsign : (-1 : ℂ) ^ (n - 1) = 1 := by
    have hnEven : Even (n - 1) := by
      refine ⟨q - 1, ?_⟩
      omega
    obtain ⟨k, hk⟩ := hnEven
    rw [hk, pow_add]
    rw [← mul_pow]
    norm_num
  have hform :
      ((N : ℂ) - (n : ℂ)) *
        ∏ j ∈ Finset.univ.erase l,
          (-1 : ℂ) / (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
      ((N : ℂ) - (n : ℂ)) /
        ∏ j ∈ Finset.univ.erase l,
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) := by
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_erase_of_mem, Finset.card_univ,
      Fintype.card_fin, Finset.mem_univ]
    rw [hsign]
    simp only [one_div]
    ring
  rw [hp0] at hlim
  rw [hform] at hlim
  simpa [l] using hlim

private theorem cor34_halfRoot_primitive {m : ℕ} (hm : m ≠ 0) :
    IsPrimitiveRoot (cor34_halfRoot m) (2 * m) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hηeq : cor34_halfRoot m = Complex.exp (2 * Real.pi * Complex.I / (2 * m : ℂ)) := by
    dsimp [cor34_halfRoot]
    congr 1
    field_simp [hmR]
  rw [hηeq]
  convert Complex.isPrimitiveRoot_exp (2 * m) (by omega) using 1
  congr 1
  norm_num

/-- For even `n` and positive `r`, the normalized regular Bethe eigenvalue tends to the
cosine product, which is the Perron root of the limiting transfer block. -/
private theorem cor34_normalizedRegularEigenvalue_tendsto_pfRoot_positive {N n r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 < r) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 (pfRoot (infinityBlock N n))) := by
  have hbase := cor34_normalizedRegularEigenvalue_base_limit hp hp0 hNpos hbound hn
  have hm : N - n = n + 2 * r := by omega
  let m : ℕ := n + 2 * r
  let η : ℂ := cor34_halfRoot m
  let k : ℕ := 2 * m + 1 - n
  have hmpos : 0 < m := by dsimp [m]; omega
  have hηroot : IsPrimitiveRoot η (2 * m) := by
    exact cor34_halfRoot_primitive (by omega)
  have hηne : η ≠ 0 := by
    dsimp [η, cor34_halfRoot]
    exact Complex.exp_ne_zero _
  have hperiod : η ^ (2 * (m : ℤ)) = 1 := by
    convert hηroot.zpow_eq_one using 1; norm_cast
  have heta : cor34_halfRoot (N - n) = η := by
    simp [η, m, hm]
  have hfactor (i : Fin n) :
      BetheAnsatz.z (Bethe.discreteBaseSolution N n i) = η ^ (k + 2 * i.val) := by
    rw [cor34_base_z_eq_halfRoot_zpow (by omega) i, heta]
    have hexp : ((k + 2 * i.val : ℕ) : ℤ) = (2 * m : ℤ) +
        (2 * (i.val : ℤ) + 1 - (n : ℤ)) := by
      dsimp [k, m]
      omega
    calc
      η ^ (2 * (i.val : ℤ) + 1 - (n : ℤ)) =
          η ^ ((2 * m : ℤ) + (2 * (i.val : ℤ) + 1 - (n : ℤ))) := by
            rw [zpow_add₀ hηne, hperiod, one_mul]
      _ = η ^ ((k + 2 * i.val : ℕ) : ℤ) := by rw [← hexp]
      _ = η ^ (k + 2 * i.val) := by rw [zpow_natCast]
  have hden :
      (∏ i : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i))) =
        ∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i)) := by
    let f : ℕ → ℂ := fun i => if hi : i < n then
      1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n ⟨i, hi⟩) else 1
    calc
      ∏ i : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) =
          ∏ i : Fin n, f i := by
            apply Finset.prod_congr rfl
            intro i hi
            simp [f]
      _ = ∏ i ∈ Finset.range n, f i := Fin.prod_univ_eq_prod_range f n
      _ = ∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i)) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hi' : i < n := Finset.mem_range.mp hi
            simp only [f, dite_eq_left hi']
            simpa using congrArg (fun z : ℂ => 1 - z) (hfactor ⟨i, hi'⟩)
  have hcyclo := cor34_cyclotomic_even_evaluation n r hn hr
  have hvalue :
      (2 : ℂ) / ∏ i : Fin n,
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) =
        (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
          ((1 + Real.cos
            (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / ((n : ℝ) + 2 * r))) : ℂ) := by
    rw [hden]
    simpa [m, η, k, cor34_halfRoot] using hcyclo
  rw [pfRoot_infinityBlock_value hnpos hN]
  simpa [hvalue] using hbase

/-- For even `n` and nonnegative `r`, the normalized regular Bethe eigenvalue tends to the
cosine product, which is the Perron root of the limiting transfer block. -/
theorem cor34_normalizedRegularEigenvalue_tendsto_pfRoot {N n r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 (pfRoot (infinityBlock N n))) := by
  by_cases hrpos : 0 < r
  · exact cor34_normalizedRegularEigenvalue_tendsto_pfRoot_positive
      hp hp0 hNpos hbound hnpos hn hN hrpos
  · have hrzero : r = 0 := by omega
    subst r
    have hN' : N = 2 * n := by simpa using hN
    have hden := cor34_even_base_denominator_at_r_zero hnpos hn hN'
    have hbase := cor34_normalizedRegularEigenvalue_base_limit hp hp0 hNpos hbound hn
    have hvalue : (2 : ℂ) /
        ∏ j : Fin n, (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 1 := by
      rw [hden]
      norm_num
    have hlim : Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε))
        (𝓝 0) (𝓝 (1 : ℂ)) := by
      rw [hvalue] at hbase
      exact hbase
    rw [pfRoot_infinityBlock_value hnpos hN]
    simpa using hlim

/-- The base phase at an odd centered index is the shifted power used in the odd
cyclotomic evaluation of `SixVertex/Cor34Cyclotomic.lean`, away from the zero root. -/
private theorem cor34_odd_base_phase_shift {N n q r : ℕ}
    (hbound : 2 * n ≤ N) (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r))
    (i : Fin n) :
    BetheAnsatz.z (Bethe.discreteBaseSolution N n i) =
      (cor34_halfRoot (n + 2 * r) ^ 2) ^
        ((n + 2 * r + 1 - q) + i.val) := by
  let m : ℕ := n + 2 * r
  let η : ℂ := cor34_halfRoot m
  let ζ : ℂ := η ^ 2
  let s : ℕ := m + 1 - q
  have hm : N - n = m := by dsimp [m]; omega
  have hmpos : 0 < m := by dsimp [m]; omega
  have hηroot : IsPrimitiveRoot η (2 * m) :=
    cor34_halfRoot_primitive (by omega)
  have hζroot : IsPrimitiveRoot ζ m := by
    dsimp [ζ]
    exact hηroot.pow (by omega) (by omega)
  have hζne : ζ ≠ 0 := by
    dsimp [ζ, η, cor34_halfRoot]
    exact pow_ne_zero _ (Complex.exp_ne_zero _)
  have hζperiod : ζ ^ (m : ℤ) = 1 := by
    convert hζroot.zpow_eq_one using 1
  have hbase : BetheAnsatz.z (Bethe.discreteBaseSolution N n i) =
      η ^ (2 * ((i.val : ℤ) + 1 - q)) := by
    rw [cor34_base_z_eq_halfRoot_zpow (by omega) i, hm]
    have he : 2 * (i.val : ℤ) + 1 - (n : ℤ) =
        2 * ((i.val : ℤ) + 1 - q) := by omega
    rw [he]
  have hshift : ((s + i.val : ℕ) : ℤ) =
      (m : ℤ) + (i.val : ℤ) + 1 - q := by
    dsimp [s]
    omega
  have hpow : ζ ^ (s + i.val) = η ^ (2 * ((i.val : ℤ) + 1 - q)) := by
    rw [← zpow_natCast, hshift]
    calc
      ζ ^ ((m : ℤ) + (i.val : ℤ) + 1 - q) =
          ζ ^ ((m : ℤ) + ((i.val : ℤ) + 1 - q)) := by congr 1; ring
      _ = ζ ^ ((i.val : ℤ) + 1 - q) := by
        rw [zpow_add₀ hζne, hζperiod, one_mul]
      _ = η ^ (2 * ((i.val : ℤ) + 1 - q)) := by
        dsimp [ζ, η]
        exact (zpow_mul η 2 ((i.val : ℤ) + 1 - q)).symm
  rw [hbase, ← hpow]

/-- The odd cyclotomic denominator is exactly the cyclotomic product of
`SixVertex/Cor34Cyclotomic.lean`, with the zero-root factor replaced by one. -/
private theorem cor34_odd_base_denominator_eq_cyclotomic {N n q r : ℕ}
    (hbound : 2 * n ≤ N) (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) :
    ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
      ∏ i ∈ Finset.range n,
        (if i = q - 1 then 1 else
          1 - (cor34_halfRoot (n + 2 * r) ^ 2) ^ (n + 2 * r + 1 - q + i)) := by
  let l : Fin n := ⟨q - 1, by omega⟩
  let gFin : Fin n → ℂ := fun i => if i = l then 1 else
    1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)
  have hgFin : ∏ i : Fin n, gFin i =
      ∏ i ∈ Finset.univ.erase l,
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) := by
    calc
      ∏ i : Fin n, gFin i = ∏ i ∈ Finset.univ, gFin i := by simp
      _ = (∏ i ∈ Finset.univ.erase l, gFin i) * gFin l := by
        symm
        exact Finset.prod_erase_mul Finset.univ gFin (Finset.mem_univ l)
      _ = ∏ i ∈ Finset.univ.erase l,
            (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n i)) := by
        simp only [gFin, ↓reduceIte, mul_one]
        apply Finset.prod_congr rfl
        intro i hi
        have hne : i ≠ l := (Finset.mem_erase.mp hi).1
        simp [hne]
  let f : ℕ → ℂ := fun i => if hi : i < n then gFin ⟨i, hi⟩ else 1
  have hrange : ∏ i ∈ Finset.range n,
        (if i = q - 1 then 1 else
          1 - (cor34_halfRoot (n + 2 * r) ^ 2) ^ (n + 2 * r + 1 - q + i)) =
      ∏ i : Fin n, gFin i := by
    have hfrange := Fin.prod_univ_eq_prod_range f n
    have heq : ∀ i ∈ Finset.range n,
        f i = (if i = q - 1 then 1 else
          1 - (cor34_halfRoot (n + 2 * r) ^ 2) ^ (n + 2 * r + 1 - q + i)) := by
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      by_cases hc : i = q - 1
      · have hfi : (⟨i, hin⟩ : Fin n) = l := by
          apply Fin.ext
          change i = q - 1
          exact hc
        rw [ite_eq_left hc]
        simp [f, gFin, hin, hfi]
      · have hphase := cor34_odd_base_phase_shift hbound hnq hN ⟨i, hin⟩
        have hfi : (⟨i, hin⟩ : Fin n) ≠ l := by
          intro heq
          exact hc (congrArg Fin.val heq)
        rw [ite_eq_right hc]
        calc
          f i = gFin ⟨i, hin⟩ := by simp [f, hin]
          _ = 1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n ⟨i, hin⟩) := by
            simp [gFin, hfi]
          _ = 1 - (cor34_halfRoot (n + 2 * r) ^ 2) ^
                (n + 2 * r + 1 - q + i) := by
            simpa using congrArg (fun z : ℂ => 1 - z) hphase
    calc
      _ = ∏ i ∈ Finset.range n, f i := Finset.prod_congr rfl (fun i hi => (heq i hi).symm)
      _ = ∏ i : Fin n, f i := hfrange.symm
      _ = ∏ i : Fin n, gFin i := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [f]
  rw [show (⟨q - 1, by omega⟩ : Fin n) = l by rfl]
  rw [← hgFin, hrange]

/-- At half filling, the odd centered denominator is the product over all nontrivial
powers of a primitive `n`th root, hence equals `n`. -/
private theorem cor34_odd_base_denominator_at_r_zero {N n q : ℕ}
    (hnpos : 0 < n) (hbound : 2 * n ≤ N) (hnq : n + 1 = 2 * q)
    (hN : N = 2 * n) :
    ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
      (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = (n : ℂ) := by
  let ζ : ℂ := cor34_halfRoot n ^ 2
  let s : ℕ := n + 1 - q
  let g : ℕ → ℂ := fun i => if i = q - 1 then 1 else 1 - ζ ^ (s + i)
  let u : ℕ → ℂ := fun i => 1 - ζ ^ (s + i)
  have hζroot : IsPrimitiveRoot ζ n := by
    dsimp [ζ]
    exact cor34_halfRoot_primitive (by omega) |>.pow (by omega) (by omega)
  have hden := cor34_odd_base_denominator_eq_cyclotomic
    hbound hnq (r := 0) (by simpa using hN)
  have hden' :
      ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
        (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
      ∏ i ∈ Finset.range n, g i := by
    simpa [g, ζ, s] using hden
  have hpre : (∏ i ∈ Finset.range q, g i) =
      ∏ i ∈ Finset.range (q - 1), u i := by
    rw [show q = (q - 1) + 1 by omega, Finset.prod_range_add]
    have hprefix : (∏ i ∈ Finset.range (q - 1), g i) =
        ∏ i ∈ Finset.range (q - 1), u i := by
      apply Finset.prod_congr rfl
      intro i hi
      have hneq : i ≠ q - 1 := by
        have hlt := Finset.mem_range.mp hi
        omega
      simp [g, u, hneq]
    rw [hprefix]
    simp [g]
  have hpost : (∏ i ∈ Finset.range (n - q), g (q + i)) =
      ∏ i ∈ Finset.range (n - q), (1 - ζ ^ (i + 1)) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hskip : q + i ≠ q - 1 := by
      have hlt := Finset.mem_range.mp hi
      omega
    have hexp : s + (q + i) = n + (i + 1) := by
      dsimp [s]
      omega
    have hpow : ζ ^ (s + (q + i)) = ζ ^ (i + 1) := by
      rw [hexp, pow_add, hζroot.pow_eq_one, one_mul]
    simp [g, hskip, hpow]
  have hsplit : (∏ i ∈ Finset.range n, g i) =
      (∏ i ∈ Finset.range (q - 1), u i) *
        ∏ i ∈ Finset.range (n - q), (1 - ζ ^ (i + 1)) := by
    calc
      ∏ i ∈ Finset.range n, g i =
          (∏ i ∈ Finset.range q, g i) *
            ∏ i ∈ Finset.range (n - q), g (q + i) := by
        have hadd := Finset.prod_range_add g q (n - q)
        rw [show q + (n - q) = n by omega] at hadd
        exact hadd
      _ = _ := by rw [hpre, hpost]
  have hcanonical :
      (∏ i ∈ Finset.range (n - 1), (1 - ζ ^ (i + 1))) =
        (∏ i ∈ Finset.range (n - q), (1 - ζ ^ (i + 1))) *
          ∏ i ∈ Finset.range (q - 1), u i := by
    rw [show n - 1 = (n - q) + (q - 1) by omega, Finset.prod_range_add]
    apply congrArg₂ (· * ·) rfl
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [u, s]
    congr 2
    omega
  have hζroot' : IsPrimitiveRoot ζ (n - 1 + 1) := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    exact hζroot
  have hprod := hζroot'.prod_one_sub_pow_eq_order
  have hprod' :
      (∏ i ∈ Finset.range (n - 1), (1 - ζ ^ (i + 1))) = (n : ℂ) := by
    norm_cast at hprod
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hprod
    exact hprod
  calc
    _ = ∏ i ∈ Finset.range n, g i := hden'
    _ = (∏ i ∈ Finset.range (q - 1), u i) *
          ∏ i ∈ Finset.range (n - q), (1 - ζ ^ (i + 1)) := hsplit
    _ = (∏ i ∈ Finset.range (n - q), (1 - ζ ^ (i + 1))) *
          ∏ i ∈ Finset.range (q - 1), u i := mul_comm _ _
    _ = ∏ i ∈ Finset.range (n - 1), (1 - ζ ^ (i + 1)) := hcanonical.symm
    _ = (n : ℂ) := hprod'

/-- For odd `n` and positive `r`, the normalized zero-root Bethe eigenvalue tends to the
cyclotomic cosine product, hence to the Perron root of the limiting transfer block. -/
private theorem cor34_normalizedZeroEigenvalue_tendsto_pfRoot_positive {N n q r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 < r) :
    Tendsto
      (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
        (⟨q - 1, by omega⟩ : Fin n))
      (𝓝 0) (𝓝 (pfRoot (infinityBlock N n))) := by
  have hbase := cor34_normalizedZeroEigenvalue_base_limit hp hp0 hNpos hbound hnq
  have hden := cor34_odd_base_denominator_eq_cyclotomic hbound hnq hN
  have hcyclo := cor34_cyclotomic_odd_evaluation n r q hnq hr
  have hvalue :
      ((N : ℂ) - (n : ℂ)) /
        ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
          (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) =
        (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
          ((1 + Real.cos
            (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / ((n : ℝ) + 2 * r))) : ℂ) := by
    have hcast : (N : ℂ) - (n : ℂ) = (n + 2 * r : ℕ) := by
      rw [hN]
      push_cast
      ring
    rw [hden, hcast]
    simpa [cor34_halfRoot] using hcyclo
  rw [pfRoot_infinityBlock_value hnpos hN]
  simpa [hvalue] using hbase

/-- For odd `n` and nonnegative `r`, the normalized zero-root Bethe eigenvalue tends to the
cosine product, hence to the Perron root of the limiting transfer block. -/
theorem cor34_normalizedZeroEigenvalue_tendsto_pfRoot {N n q r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    Tendsto
      (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
        (⟨q - 1, by omega⟩ : Fin n))
      (𝓝 0) (𝓝 (pfRoot (infinityBlock N n))) := by
  by_cases hrpos : 0 < r
  · exact cor34_normalizedZeroEigenvalue_tendsto_pfRoot_positive
      hp hp0 hNpos hbound hnpos hnq hN hrpos
  · have hrzero : r = 0 := by omega
    subst r
    have hN' : N = 2 * n := by simpa using hN
    have hden := cor34_odd_base_denominator_at_r_zero hnpos hbound hnq hN'
    have hbase := cor34_normalizedZeroEigenvalue_base_limit
      hp hp0 hNpos hbound hnq
    have hvalue :
        ((N : ℂ) - (n : ℂ)) /
          ∏ j ∈ Finset.univ.erase (⟨q - 1, by omega⟩ : Fin n),
            (1 - BetheAnsatz.z (Bethe.discreteBaseSolution N n j)) = 1 := by
      rw [hden, hN']
      push_cast
      field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hnpos)]
      norm_num
    have hlim : Tendsto
        (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
          (⟨q - 1, by omega⟩ : Fin n))
        (𝓝 0) (𝓝 (1 : ℂ)) := by
      rw [hvalue] at hbase
      exact hbase
    rw [pfRoot_infinityBlock_value hnpos hN]
    simpa using hlim

end PottsDiscontinuity.SixVertex
