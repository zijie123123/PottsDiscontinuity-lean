module

public import Mathlib

/-!
# Corollary 3.4: cyclotomic determinant calculation

The Vandermonde factor occurring in the cyclotomic calculation is nonzero whenever the
primitive root has order strictly greater than the number of rows.
-/

@[expose] public section

namespace PottsDiscontinuity.SixVertex

/-- Pairing the complementary conjugate roots in the even cyclotomic calculation gives the
real product displayed in Corollary 3.4. -/
theorem cor34_cyclotomic_even_real_product (n r : ℕ) (hm : n + 2 * r ≠ 0) :
    (∏ j ∈ Finset.range r,
      (2 - 2 * Real.cos (Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ)))) =
    2 ^ r * ∏ j ∈ Finset.range r,
      (1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))) := by
  have hmR : (n + 2 * r : ℝ) ≠ 0 := by exact_mod_cast hm
  calc
    (∏ j ∈ Finset.range r,
        (2 - 2 * Real.cos (Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ)))) =
      ∏ j ∈ Finset.range r,
        (2 - 2 * Real.cos
          (Real.pi * ((n + 1 + 2 * (r - 1 - j) : ℕ) : ℝ) / (n + 2 * r : ℝ))) := by
      rw [← Finset.prod_range_reflect]
    _ = ∏ j ∈ Finset.range r,
        (2 * (1 + Real.cos
          (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ)))) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjr : j < r := Finset.mem_range.mp hj
      have hnum : n + 1 + 2 * (r - 1 - j) = n + 2 * r - (2 * j + 1) := by omega
      have harg :
          Real.pi * ((n + 1 + 2 * (r - 1 - j) : ℕ) : ℝ) / (n + 2 * r : ℝ) =
            Real.pi - Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ) := by
        rw [hnum]
        have hle : 2 * j + 1 ≤ n + 2 * r := by omega
        rw [Nat.cast_sub hle]
        push_cast
        field_simp
      rw [harg, Real.cos_pi_sub]
      ring
    _ = 2 ^ r * ∏ j ∈ Finset.range r,
        (1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- A conjugate pair of unit-circle factors is the corresponding real cosine factor. -/
theorem cor34_one_sub_exp_pair (θ : ℝ) :
    (1 - Complex.exp ((θ : ℂ) * Complex.I)) *
      (1 - Complex.exp (-(θ : ℂ) * Complex.I)) =
        (2 - 2 * Real.cos θ : ℂ) := by
  have hneg : Complex.exp (-(θ : ℂ) * Complex.I) =
      (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    simpa [sub_eq_add_neg] using (Complex.exp_ofReal_mul_I (-θ))
  rw [Complex.exp_ofReal_mul_I θ, hneg]
  have htrigR : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have htrig : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast htrigR
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  linear_combination htrig

/-- The complementary `2r` shifted roots in either parity case pair into the real product
appearing in Corollary 3.4. -/
theorem cor34_cyclotomic_complement_product (n r : ℕ) (hm : n + 2 * r ≠ 0) :
    (∏ j ∈ Finset.range (2 * r),
      (1 - Complex.exp
        (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ) : ℝ) : ℂ) * Complex.I))) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos
          (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))) : ℂ) := by
  let θ : ℕ → ℝ := fun j => Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (n + 2 * r : ℝ)
  let f : ℕ → ℂ := fun j => 1 - Complex.exp ((θ j : ℂ) * Complex.I)
  have hmR : (n + 2 * r : ℝ) ≠ 0 := by exact_mod_cast hm
  have hrev : (∏ j ∈ Finset.range r, f (r + j)) =
      ∏ j ∈ Finset.range r, f (r + (r - 1 - j)) := by
    exact (Finset.prod_range_reflect (fun j => f (r + j)) r).symm
  have hpair : ∀ j ∈ Finset.range r,
      f j * f (r + (r - 1 - j)) = (2 - 2 * Real.cos (θ j) : ℂ) := by
    intro j hj
    have hjr : j < r := Finset.mem_range.mp hj
    have hnum : n + 1 + 2 * (r + (r - 1 - j)) =
        2 * (n + 2 * r) - (n + 1 + 2 * j) := by omega
    have hle : n + 1 + 2 * j ≤ 2 * (n + 2 * r) := by omega
    have hangle : θ (r + (r - 1 - j)) = 2 * Real.pi - θ j := by
      dsimp [θ]
      rw [hnum, Nat.cast_sub hle]
      push_cast
      field_simp
    have hexp : Complex.exp ((θ (r + (r - 1 - j)) : ℂ) * Complex.I) =
        Complex.exp (-(θ j : ℂ) * Complex.I) := by
      rw [hangle, show 2 * Real.pi - θ j = -θ j + 2 * Real.pi by ring]
      convert Complex.exp_mul_I_periodic (-θ j) using 1
      push_cast
      ring
    dsimp [f]
    rw [hexp]
    exact_mod_cast cor34_one_sub_exp_pair (θ j)
  calc
    ∏ j ∈ Finset.range (2 * r), f j =
        (∏ j ∈ Finset.range r, f j) * ∏ j ∈ Finset.range r, f (r + j) := by
      rw [show 2 * r = r + r by omega, Finset.prod_range_add]
    _ = (∏ j ∈ Finset.range r, f j) *
        ∏ j ∈ Finset.range r, f (r + (r - 1 - j)) := by rw [hrev]
    _ = ∏ j ∈ Finset.range r, (f j * f (r + (r - 1 - j))) := by
      rw [← Finset.prod_mul_distrib]
    _ = ∏ j ∈ Finset.range r, (2 - 2 * Real.cos (θ j) : ℂ) :=
      Finset.prod_congr rfl hpair
    _ = (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos
          (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (n + 2 * r : ℝ))) : ℂ) := by
      have hreal := cor34_cyclotomic_even_real_product n r hm
      dsimp [θ]
      exact_mod_cast hreal

/-- Even-parity cyclotomic evaluation. The shifted powers `η ^ (k + 2i)` encode the
half-integer exponents in the source, with the shift by `2m` fixing a nonnegative exponent. -/
theorem cor34_cyclotomic_even_evaluation (n r : ℕ) (hn : Even n) (hr : 0 < r) :
    let m := n + 2 * r
    let η := Complex.exp (Real.pi * Complex.I / (m : ℂ))
    let k := 2 * m + 1 - n
    (2 : ℂ) / (∏ i ∈ Finset.range n, (1 - η ^ (k + 2 * i))) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
  dsimp
  let m : ℕ := n + 2 * r
  let η : ℂ := Complex.exp (Real.pi * Complex.I / (m : ℂ))
  let k : ℕ := 2 * m + 1 - n
  let ζ : ℂ := η ^ 2
  let α : ℂ := η ^ k
  let f : ℕ → ℂ := fun i => 1 - η ^ (k + 2 * i)
  have hm : m ≠ 0 := by dsimp [m]; omega
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have h2m : 2 * m ≠ 0 := by omega
  have hηroot : IsPrimitiveRoot η (2 * m) := by
    have hηeq : η = Complex.exp (2 * Real.pi * Complex.I / (2 * m : ℂ)) := by
      dsimp [η]
      congr 1
      field_simp [hmR]
    rw [hηeq]
    convert Complex.isPrimitiveRoot_exp (2 * m) h2m using 1
    congr 1
    norm_num
  have hζroot : IsPrimitiveRoot ζ m := by
    dsimp [ζ]
    exact hηroot.pow (by omega) (by omega)
  have hηmroot : IsPrimitiveRoot (η ^ m) 2 := by
    exact hηroot.pow (by omega) (by omega)
  have hηm : η ^ m = -1 := hηmroot.eq_neg_one_of_two_right
  have hkodd : Odd k := by
    dsimp [k]
    apply Nat.Odd.sub_even (by dsimp [m]; omega)
    · exact ⟨m, by omega⟩
    · exact hn
  have hαpow : α ^ m = -1 := by
    dsimp [α]
    calc
      (η ^ k) ^ m = (η ^ m) ^ k := by
        rw [← pow_mul, Nat.mul_comm k m, pow_mul]
      _ = (-1 : ℂ) ^ k := by rw [hηm]
      _ = -1 := (neg_one_pow_eq_neg_one_iff_odd (by norm_num)).2 hkodd
  have hηpow (e : ℕ) :
      η ^ e = Complex.exp (((Real.pi * (e : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I) := by
    dsimp [η]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp [hmR]
  have htotal : (∏ i ∈ Finset.range m, f i) = 2 := by
    have hp := X_pow_sub_C_eq_prod hζroot (α := α) (a := -1) (by omega) hαpow
    have heval := congrArg (Polynomial.eval (1 : ℂ)) hp
    have hrootprod :
        (∏ i ∈ Finset.range m, (1 - ζ ^ i * α)) = 2 := by
      norm_num [Polynomial.eval_prod] at heval ⊢
      exact heval.symm
    calc
      ∏ i ∈ Finset.range m, f i =
          ∏ i ∈ Finset.range m, (1 - ζ ^ i * α) := by
        apply Finset.prod_congr rfl
        intro i hi
        dsimp [f, ζ, α]
        rw [← pow_mul, ← pow_add, Nat.add_comm]
      _ = 2 := hrootprod
  have hsplit :
      (∏ i ∈ Finset.range m, f i) =
        (∏ i ∈ Finset.range n, f i) * ∏ j ∈ Finset.range (2 * r), f (n + j) := by
    dsimp [m]
    rw [Finset.prod_range_add]
  have hcomp :
      (∏ j ∈ Finset.range (2 * r), f (n + j)) =
        (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
          ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
    calc
      ∏ j ∈ Finset.range (2 * r), f (n + j) =
          ∏ j ∈ Finset.range (2 * r),
            (1 - Complex.exp
              (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I)) := by
        apply Finset.prod_congr rfl
        intro j hj
        have he : k + 2 * (n + j) = 2 * m + (n + 1 + 2 * j) := by
          dsimp [k, m]
          omega
        dsimp [f]
        rw [he, pow_add, hηroot.pow_eq_one, one_mul, hηpow]
      _ = _ := by
        simpa [m] using cor34_cyclotomic_complement_product n r (by dsimp [m]; omega)
  have hDne : (∏ i ∈ Finset.range n, f i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hpowne : η ^ (k + 2 * i) ≠ 1 := by
      intro hEq
      have hdvd : 2 * m ∣ k + 2 * i := (hηroot.pow_eq_one_iff_dvd _).mp hEq
      have h2dvd : 2 ∣ k + 2 * i := dvd_trans ⟨m, by omega⟩ hdvd
      have hev : Even (k + 2 * i) := even_iff_two_dvd.mpr h2dvd
      have hodd : Odd (k + 2 * i) := hkodd.add_even ⟨i, by omega⟩
      obtain ⟨a, ha⟩ := hodd
      obtain ⟨b, hb⟩ := hev
      omega
    dsimp [f]
    exact sub_ne_zero.mpr hpowne.symm
  have hDC :
      (∏ i ∈ Finset.range n, f i) * ∏ j ∈ Finset.range (2 * r), f (n + j) = 2 := by
    calc
      _ = ∏ i ∈ Finset.range m, f i := hsplit.symm
      _ = 2 := htotal
  calc
    (2 : ℂ) / (∏ i ∈ Finset.range n, f i) =
        ((∏ i ∈ Finset.range n, f i) * ∏ j ∈ Finset.range (2 * r), f (n + j)) /
          (∏ i ∈ Finset.range n, f i) := by rw [hDC]
    _ = ∏ j ∈ Finset.range (2 * r), f (n + j) := by field_simp [hDne]
    _ = _ := hcomp

/-- Odd-parity cyclotomic evaluation. The skipped index `q - 1` is the factor with exponent
zero; all other prefix factors are the shifted form of the source's `ζ^(j-q)` factors. -/
theorem cor34_cyclotomic_odd_evaluation (n r q : ℕ) (hnq : n + 1 = 2 * q) (hr : 0 < r) :
    let m := n + 2 * r
    let η := Complex.exp (Real.pi * Complex.I / (m : ℂ))
    let ζ := η ^ 2
    let s := m + 1 - q
    let g : ℕ → ℂ := fun i => if i = q - 1 then 1 else 1 - ζ ^ (s + i)
    (m : ℂ) / (∏ i ∈ Finset.range n, g i) =
      (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
        ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
  dsimp
  let m : ℕ := n + 2 * r
  let η : ℂ := Complex.exp (Real.pi * Complex.I / (m : ℂ))
  let ζ : ℂ := η ^ 2
  let s : ℕ := m + 1 - q
  let g : ℕ → ℂ := fun i => if i = q - 1 then 1 else 1 - ζ ^ (s + i)
  have hm : m ≠ 0 := by dsimp [m]; omega
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have h2m : 2 * m ≠ 0 := by omega
  have hηeq : η = Complex.exp (2 * Real.pi * Complex.I / (2 * m : ℂ)) := by
    dsimp [η]
    congr 1
    field_simp [hmR]
  have hηroot : IsPrimitiveRoot η (2 * m) := by
    rw [hηeq]
    convert Complex.isPrimitiveRoot_exp (2 * m) h2m using 1
    congr 1
    norm_num
  have hζroot : IsPrimitiveRoot ζ m := by
    dsimp [ζ]
    exact hηroot.pow (by omega) (by omega)
  have hηpow (e : ℕ) :
      η ^ e = Complex.exp (((Real.pi * (e : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I) := by
    dsimp [η]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp [hmR]
  have hqpos : 0 < q := by omega
  have hqle : q ≤ m := by dsimp [m]; omega
  let u : ℕ → ℂ := fun i => 1 - ζ ^ (s + i)
  have hprefix : (∏ i ∈ Finset.range (q - 1), g i) =
      ∏ i ∈ Finset.range (q - 1), u i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hlt : i < q - 1 := Finset.mem_range.mp hi
    have hneq : i ≠ q - 1 := by omega
    simp [g, u, hneq]
  have hpre : (∏ i ∈ Finset.range q, g i) = ∏ i ∈ Finset.range (q - 1), u i := by
    rw [show q = (q - 1) + 1 by omega, Finset.prod_range_add]
    rw [hprefix]
    simp [g]
  have hpost : (∏ i ∈ Finset.range (m - q), g (q + i)) =
      ∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1)) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hskip : q + i ≠ q - 1 := by omega
    have hexp : s + (q + i) = m + (i + 1) := by dsimp [s]; omega
    have hpow : ζ ^ (s + (q + i)) = ζ ^ (i + 1) := by
      rw [hexp, pow_add, hζroot.pow_eq_one, one_mul]
    simp [g, hskip, hpow]
  have hsplit :
      (∏ i ∈ Finset.range m, g i) =
        (∏ i ∈ Finset.range (q - 1), u i) *
          ∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1)) := by
    calc
      ∏ i ∈ Finset.range m, g i =
          (∏ i ∈ Finset.range q, g i) * ∏ i ∈ Finset.range (m - q), g (q + i) := by
        have hadd := Finset.prod_range_add g q (m - q)
        rw [show q + (m - q) = m by omega] at hadd
        exact hadd
      _ = _ := by rw [hpre, hpost]
  have hcanonical :
      (∏ i ∈ Finset.range (m - 1), (1 - ζ ^ (i + 1))) =
        (∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1))) *
          ∏ i ∈ Finset.range (q - 1), u i := by
    rw [show m - 1 = (m - q) + (q - 1) by omega, Finset.prod_range_add]
    apply congrArg₂ (· * ·) rfl
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [u, s]
    congr 2
    omega
  have htotal : (∏ i ∈ Finset.range m, g i) = (m : ℂ) := by
    have hζroot' : IsPrimitiveRoot ζ (m - 1 + 1) := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
      exact hζroot
    have hprod := hζroot'.prod_one_sub_pow_eq_order
    have hprod' :
        (∏ i ∈ Finset.range (m - 1), (1 - ζ ^ (i + 1))) = (m : ℂ) := by
      norm_cast at hprod
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at hprod
      exact hprod
    calc
      ∏ i ∈ Finset.range m, g i =
          (∏ i ∈ Finset.range (q - 1), u i) *
            ∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1)) := hsplit
      _ = (∏ i ∈ Finset.range (m - q), (1 - ζ ^ (i + 1))) *
            ∏ i ∈ Finset.range (q - 1), u i := mul_comm _ _
      _ = ∏ i ∈ Finset.range (m - 1), (1 - ζ ^ (i + 1)) := hcanonical.symm
      _ = (m : ℂ) := hprod'
  have hfactor_ne : ∀ i ∈ Finset.range n, g i ≠ 0 := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    by_cases hskip : i = q - 1
    · simp [g, hskip]
    · have hpowne : ζ ^ (s + i) ≠ 1 := by
        intro hEq
        by_cases hilow : i < q - 1
        · have hlt : s + i < m := by dsimp [s]; omega
          exact hζroot.pow_ne_one_of_pos_of_lt (by omega) hlt hEq
        · have hihigh : q - 1 < i := by omega
          have hred : s + i = m + (i - q + 1) := by dsimp [s]; omega
          have hredpow : ζ ^ (s + i) = ζ ^ (i - q + 1) := by
            rw [hred, pow_add, hζroot.pow_eq_one, one_mul]
          have hlt : i - q + 1 < m := by dsimp [m]; omega
          exact hζroot.pow_ne_one_of_pos_of_lt (by omega) hlt (hredpow.symm.trans hEq)
      simp [g, hskip]
      exact sub_ne_zero.mpr hpowne.symm
  have hDne : (∏ i ∈ Finset.range n, g i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfactor_ne
  have hcomp :
      (∏ j ∈ Finset.range (2 * r), g (n + j)) =
        (2 ^ r : ℂ) * ∏ j ∈ Finset.range r,
          ((1 + Real.cos (Real.pi * ((2 * j + 1 : ℕ) : ℝ) / (m : ℝ))) : ℂ) := by
    calc
      ∏ j ∈ Finset.range (2 * r), g (n + j) =
          ∏ j ∈ Finset.range (2 * r),
            (1 - Complex.exp
              (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I)) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hskip : n + j ≠ q - 1 := by omega
        have hexp : s + (n + j) = m + (q + j) := by dsimp [s]; omega
        have hpow : ζ ^ (s + (n + j)) =
            Complex.exp (((Real.pi * ((n + 1 + 2 * j : ℕ) : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I) := by
          dsimp [ζ]
          rw [hexp, pow_add, hζroot.pow_eq_one, one_mul, ← pow_mul, hηpow]
          have hnum : 2 * (q + j) = n + 1 + 2 * j := by omega
          rw [hnum]
        simp [g, hskip, hpow]
      _ = _ := by
        simpa [m] using cor34_cyclotomic_complement_product n r (by dsimp [m]; omega)
  have hDC :
      (∏ i ∈ Finset.range n, g i) * ∏ j ∈ Finset.range (2 * r), g (n + j) = (m : ℂ) := by
    calc
      _ = ∏ i ∈ Finset.range m, g i := by
        symm
        simpa [m] using (Finset.prod_range_add g n (2 * r))
      _ = (m : ℂ) := htotal
  calc
    (m : ℂ) / (∏ i ∈ Finset.range n, g i) =
        ((∏ i ∈ Finset.range n, g i) * ∏ j ∈ Finset.range (2 * r), g (n + j)) /
          (∏ i ∈ Finset.range n, g i) := by rw [hDC]
    _ = ∏ j ∈ Finset.range (2 * r), g (n + j) := by field_simp [hDne]
    _ = _ := hcomp

end PottsDiscontinuity.SixVertex
