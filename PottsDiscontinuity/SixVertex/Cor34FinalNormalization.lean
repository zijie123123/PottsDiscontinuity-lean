module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34BethePF
public import PottsDiscontinuity.SixVertex.Cor34FinalEigen

/-! # Corollary 3.4: normalize Theorem 3.1 for the infinite-anisotropy branch -/

@[expose] public section

open Matrix
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

private theorem cor34_final_normalizedTransferBlock_scale {N n : ℕ} {ε : ℝ}
    (hε : ε < 0) :
    cor34_normalizedTransferBlock N n ε =
      (-ε / 2) ^ n • transferBlock N (Real.sqrt (2 - 2 / ε)) n := by
  rw [cor34_normalizedTransferBlock_eq_scaled_transferBlock ε hε]
  have hbase : ((-2 / ε : ℝ)⁻¹) = -ε / 2 := by
    field_simp [ne_of_lt hε]
  have hpow : ((-2 / ε : ℝ) ^ n)⁻¹ = (-ε / 2) ^ n := by
    rw [← inv_pow, hbase]
  rw [hpow]

private theorem cor34_final_normalizedBlockWave_scale {N n : ℕ} {ε : ℝ}
    (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedBlockWave (N := N) ε p =
      (((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n) •
        BetheAnsatz.blockWave (N := N) (1 / ε) p := by
  funext x
  change cor34_normalizedCoordinate ε p (BetheAnsatz.positions x) = _
  rw [cor34_normalizedCoordinate_eq_scaled_coordinateWave ε p
    (BetheAnsatz.positions x) (ne_of_lt hε)]
  rfl

theorem cor34_final_normalizedRegularEigenvalue_scale {n : ℕ} {ε : ℝ}
    (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedRegularEigenvalue ε p =
      (((-ε / 2 : ℝ) : ℂ) ^ n) *
        BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) p := by
  let q : ℂ := ((-ε / 2 : ℝ) : ℂ)
  let c : ℝ := Real.sqrt (2 - 2 / ε)
  have hroot : c ^ 2 = 2 - 2 / ε := by
    dsimp [c]
    have hrec : 2 / ε < 0 := div_neg_of_pos_of_neg (by norm_num) hε
    exact Real.sq_sqrt (by linarith)
  have hcoeffR : (-ε / 2) * (2 - 2 / ε) = 1 - ε := by
    field_simp [ne_of_lt hε]
    ring
  have hcoeff : q * (c : ℂ) ^ 2 = ((1 - ε : ℝ) : ℂ) := by
    dsimp [q, c]
    rw [show ((Real.sqrt (2 - 2 / ε) : ℝ) : ℂ) ^ 2 =
      ((2 - 2 / ε : ℝ) : ℂ) by exact_mod_cast hroot]
    exact_mod_cast hcoeffR
  have hL (j : Fin n) :
      cor34_normalizedL ε (p j) = q * BetheAnsatz.L c (BetheAnsatz.z (p j)) := by
    unfold cor34_normalizedL BetheAnsatz.L
    rw [← hcoeff]
    ring
  have hM (j : Fin n) :
      cor34_normalizedM ε (p j) = q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    unfold cor34_normalizedM BetheAnsatz.M
    rw [← hcoeff]
    ring
  have hprodL :
      (∏ j : Fin n, cor34_normalizedL ε (p j)) =
        q ^ n * ∏ j : Fin n, BetheAnsatz.L c (BetheAnsatz.z (p j)) := by
    calc
      _ = ∏ j : Fin n, q * BetheAnsatz.L c (BetheAnsatz.z (p j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact hL j
      _ = (∏ j : Fin n, q) * ∏ j : Fin n, BetheAnsatz.L c (BetheAnsatz.z (p j)) :=
        Finset.prod_mul_distrib
      _ = _ := by simp [Finset.prod_const, Fintype.card_fin]
  have hprodM :
      (∏ j : Fin n, cor34_normalizedM ε (p j)) =
        q ^ n * ∏ j : Fin n, BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    calc
      _ = ∏ j : Fin n, q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact hM j
      _ = (∏ j : Fin n, q) * ∏ j : Fin n, BetheAnsatz.M c (BetheAnsatz.z (p j)) :=
        Finset.prod_mul_distrib
      _ = _ := by simp [Finset.prod_const, Fintype.card_fin]
  unfold cor34_normalizedRegularEigenvalue BetheAnsatz.eigenvalueRegular
  rw [hprodL, hprodM]
  simp only [q]
  ring

private theorem cor34_final_derivativeCorrection_eq_rational {ε y : ℝ}
    (hε : ε < 0) :
    cor34_derivativeCorrection ε y =
      2 * (1 + Real.cos y - 2 / ε) /
        ((1 + Real.cos y - 2 / ε) ^ 2 + (Real.sin y) ^ 2) := by
  have hden :
      (ε * (1 + Real.cos y) - 2) ^ 2 + ε ^ 2 * (Real.sin y) ^ 2 =
        ε ^ 2 * ((1 + Real.cos y - 2 / ε) ^ 2 + (Real.sin y) ^ 2) := by
    field_simp [ne_of_lt hε]
  have hnum :
      2 * ε * (ε * (1 + Real.cos y) - 2) =
        ε ^ 2 * (2 * (1 + Real.cos y - 2 / ε)) := by
    field_simp [ne_of_lt hε]
  have hdiv : 2 / ε < 0 := div_neg_of_pos_of_neg (by norm_num) hε
  have hd : 0 < 1 + Real.cos y - 2 / ε := by
    have hcos := Real.neg_one_le_cos y
    linarith
  have hdenpos :
      0 < (1 + Real.cos y - 2 / ε) ^ 2 + (Real.sin y) ^ 2 := by
    positivity
  have hdenne :
      (ε * (1 + Real.cos y) - 2) ^ 2 + ε ^ 2 * (Real.sin y) ^ 2 ≠ 0 := by
    rw [hden]
    exact mul_ne_zero (pow_ne_zero _ (ne_of_lt hε)) (ne_of_gt hdenpos)
  unfold cor34_derivativeCorrection
  rw [hnum, hden]
  field_simp [ne_of_lt hε, ne_of_gt hdenpos]

theorem cor34_final_normalizedZeroEigenvalue_scale {N n : ℕ} (l : Fin n)
    {ε : ℝ} (hInv : 1 / ε < -1) (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedZeroEigenvalue (N := N) ε p l =
      (((-ε / 2 : ℝ) : ℂ) ^ n) *
        BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) p l := by
  let q : ℂ := ((-ε / 2 : ℝ) : ℂ)
  let c : ℝ := Real.sqrt (2 - 2 / ε)
  have hroot : c ^ 2 = 2 - 2 / ε := by
    dsimp [c]
    have hdiv : 2 / ε < 0 := div_neg_of_pos_of_neg (by norm_num) hε
    exact Real.sq_sqrt (by linarith)
  have hcoeffR : (-ε / 2) * (2 - 2 / ε) = 1 - ε := by
    field_simp [ne_of_lt hε]
    ring
  have hcoeff : q * (c : ℂ) ^ 2 = ((1 - ε : ℝ) : ℂ) := by
    dsimp [q, c]
    rw [show ((Real.sqrt (2 - 2 / ε) : ℝ) : ℂ) ^ 2 =
      ((2 - 2 / ε : ℝ) : ℂ) by exact_mod_cast hroot]
    exact_mod_cast hcoeffR
  have hanisotropy : BetheAnsatz.anisotropy c = 1 / ε := by
    unfold BetheAnsatz.anisotropy
    rw [hroot]
    ring
  have hderiv (j : Fin n) :
      (deriv (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0 : ℝ) =
        -1 + cor34_derivativeCorrection ε (p j) := by
    rw [hanisotropy, cor34_deriv_theta_at_zero hInv]
    rw [show 2 * (1 / ε) = 2 / ε by ring]
    rw [cor34_final_derivativeCorrection_eq_rational hε]
  have hderivC (j : Fin n) :
      deriv (fun t : ℝ => (Bethe.theta (BetheAnsatz.anisotropy c) t (p j) : ℂ)) 0 =
        ((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ) := by
    have hdiff : DifferentiableAt ℝ
        (fun t : ℝ => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0 := by
      simpa [hanisotropy] using
        (Bethe.analyticAt_theta_left hInv 0 (p j)).differentiableAt
    have hcast := hdiff.hasDerivAt.ofReal_comp
    rw [hcast.deriv, hderiv j]
  have hsum :
      (∑ j ∈ Finset.univ.erase l,
          (deriv (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0 : ℂ)) =
        ∑ j ∈ Finset.univ.erase l,
          (((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hderivC j
  have htwo : q * (2 : ℂ) = ((-ε : ℝ) : ℂ) := by
    dsimp [q]
    push_cast
    ring
  have hcoef :
      q * (2 + (c : ℂ) ^ 2 * ((N : ℂ) - 1) + (c : ℂ) ^ 2 *
        ∑ j ∈ Finset.univ.erase l,
          (deriv (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0 : ℂ)) =
        ((-ε : ℝ) : ℂ) + ((1 - ε : ℝ) : ℂ) *
          (((N : ℂ) - 1) + ∑ j ∈ Finset.univ.erase l,
            (((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ))) := by
    rw [hsum]
    calc
      _ = q * 2 + (q * (c : ℂ) ^ 2) * ((N : ℂ) - 1) +
          (q * (c : ℂ) ^ 2) *
            ∑ j ∈ Finset.univ.erase l,
              (((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ)) := by ring
      _ = ((-ε : ℝ) : ℂ) + ((1 - ε : ℝ) : ℂ) * ((N : ℂ) - 1) +
          ((1 - ε : ℝ) : ℂ) *
            ∑ j ∈ Finset.univ.erase l,
              (((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ)) := by
            rw [htwo, hcoeff]
      _ = _ := by ring
  have hM (j : Fin n) :
      cor34_normalizedM ε (p j) = q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    unfold cor34_normalizedM BetheAnsatz.M
    rw [← hcoeff]
    ring
  have hprodM :
      (∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j)) =
        q ^ (n - 1) * ∏ j ∈ Finset.univ.erase l,
          BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    calc
      _ = ∏ j ∈ Finset.univ.erase l,
          q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact hM j
      _ = (∏ j ∈ Finset.univ.erase l, q) *
          ∏ j ∈ Finset.univ.erase l, BetheAnsatz.M c (BetheAnsatz.z (p j)) :=
        Finset.prod_mul_distrib
      _ = _ := by simp [Finset.prod_const, Finset.card_erase_of_mem]
  have hpow : q * q ^ (n - 1) = q ^ n := by
    have hnpos : 0 < n := Nat.zero_lt_of_lt l.isLt
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
    calc
      q * q ^ (n - 1) = q ^ (n - 1) * q := by ring
      _ = q ^ (n - 1 + 1) := (pow_succ q (n - 1)).symm
      _ = q ^ n := by rw [hsub]
  have hmain :
      (((-ε : ℝ) : ℂ) + ((1 - ε : ℝ) : ℂ) *
          (((N : ℂ) - 1) + ∑ j ∈ Finset.univ.erase l,
            (((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ)))) *
        ∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j) =
      q ^ n *
        ((2 + (c : ℂ) ^ 2 * ((N : ℂ) - 1) + (c : ℂ) ^ 2 *
            ∑ j ∈ Finset.univ.erase l,
              (deriv (fun t : ℝ =>
                (Bethe.theta (BetheAnsatz.anisotropy c) t (p j) : ℂ)) 0 : ℂ)) *
          ∏ j ∈ Finset.univ.erase l,
            BetheAnsatz.M c (BetheAnsatz.z (p j))) := by
    calc
      _ = (q * (2 + (c : ℂ) ^ 2 * ((N : ℂ) - 1) + (c : ℂ) ^ 2 *
            ∑ j ∈ Finset.univ.erase l,
              (deriv (fun t : ℝ =>
                (Bethe.theta (BetheAnsatz.anisotropy c) t (p j) : ℂ)) 0 : ℂ))) *
          ∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j) := by
        rw [← hcoef]
      _ = _ := by
        rw [hprodM]
        rw [← hpow]
        ring_nf
  simpa [cor34_normalizedZeroEigenvalue, BetheAnsatz.eigenvalueZero, c, q] using hmain

private theorem cor34_final_scale_eigen_equation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {v : ι → ℂ} {μ a b : ℂ}
    (hEig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (a • A.map (algebraMap ℝ ℂ)) *ᵥ (b • v) = (a * μ) • (b • v) := by
  ext i
  have hi := congrFun hEig i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi ⊢
  have hi' : (∑ j, (A i j : ℂ) * v j) = μ * v i := by
    change (∑ j, (algebraMap ℝ ℂ) (A i j) * v j) = μ * v i
    exact hi
  calc
    (∑ j, (a * A i j) * (b * v j)) =
        a * b * ∑ j, A i j * v j := by
          calc
            _ = ∑ j, (a * b) * (A i j * v j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = _ := by rw [Finset.mul_sum]
    _ = a * b * (μ * v i) := by rw [hi']
    _ = (a * μ) * (b * v i) := by ring

/-- The normalized even-branch coordinate wave satisfies the normalized block eigen-equation
at every physical parameter. -/
theorem cor34_final_even_normalized_eigen {N n : ℕ} {ε : ℝ}
    (hε : ε < 0) (hInv : 1 / ε < -1)
    (p : Fin n → ℝ) (hp : p ∈ Bethe.S_n n) (hn : Even n)
    (hBE : Bethe.DiscreteBetheEquation (1 / ε) N n p) :
    (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) *ᵥ
        cor34_normalizedBlockWave ε p =
      cor34_normalizedRegularEigenvalue ε p • cor34_normalizedBlockWave ε p := by
  let c : ℝ := Real.sqrt (2 - 2 / ε)
  have hcSq : c ^ 2 = 2 - 2 / ε := by
    dsimp [c]
    have hdiv : 2 / ε < 0 := div_neg_of_pos_of_neg (by norm_num) hε
    exact Real.sq_sqrt (by linarith)
  have hc : 2 < c := by
    have hconv : 2 / ε = 2 * (1 / ε) := by ring
    have hparam : 4 < 2 - 2 / ε := by rw [hconv]; nlinarith [hInv]
    have hcpos : 0 < c := Real.sqrt_pos.2 (by linarith [hparam])
    nlinarith [hcSq, hparam]
  have hAni : BetheAnsatz.anisotropy c = 1 / ε := by
    unfold BetheAnsatz.anisotropy
    rw [hcSq]
    ring
  have hraw := cor34_final_even_block_eigen hc hAni p hp hn hBE
  have hmatrixR := cor34_final_normalizedTransferBlock_scale (N := N) (n := n) hε
  have hmatrixC :
      (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) =
        (((-ε / 2 : ℝ) : ℂ) ^ n) •
          (transferBlock N c n).map (algebraMap ℝ ℂ) := by
    rw [hmatrixR]
    ext x y
    simp [c, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  have hwave := cor34_final_normalizedBlockWave_scale (N := N) (n := n) hε p
  rw [hmatrixC, hwave]
  have hscale := cor34_final_normalizedRegularEigenvalue_scale hε p
  rw [hscale]
  exact cor34_final_scale_eigen_equation hraw

/-- The normalized odd zero-root coordinate wave satisfies the normalized block
eigen-equation at every physical parameter. -/
theorem cor34_final_odd_normalized_eigen {N n q : ℕ} {ε : ℝ}
    (hε : ε < 0) (hInv : 1 / ε < -1)
    (p : Fin n → ℝ) (hp : p ∈ Bethe.S_n n) (hnq : n + 1 = 2 * q)
    (hBE : Bethe.DiscreteBetheEquation (1 / ε) N n p) :
    (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) *ᵥ
        cor34_normalizedBlockWave ε p =
      cor34_normalizedZeroEigenvalue (N := N) ε p
          (⟨q - 1, by omega⟩ : Fin n) • cor34_normalizedBlockWave ε p := by
  let c : ℝ := Real.sqrt (2 - 2 / ε)
  have hcSq : c ^ 2 = 2 - 2 / ε := by
    dsimp [c]
    have hdiv : 2 / ε < 0 := div_neg_of_pos_of_neg (by norm_num) hε
    exact Real.sq_sqrt (by linarith)
  have hc : 2 < c := by
    have hconv : 2 / ε = 2 * (1 / ε) := by ring
    have hparam : 4 < 2 - 2 / ε := by rw [hconv]; nlinarith [hInv]
    have hcpos : 0 < c := Real.sqrt_pos.2 (by linarith [hparam])
    nlinarith [hcSq, hparam]
  have hAni : BetheAnsatz.anisotropy c = 1 / ε := by
    unfold BetheAnsatz.anisotropy
    rw [hcSq]
    ring
  have hraw := cor34_final_odd_block_eigen hc hAni p hp hnq hBE
  have hmatrixR := cor34_final_normalizedTransferBlock_scale (N := N) (n := n) hε
  have hmatrixC :
      (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) =
        (((-ε / 2 : ℝ) : ℂ) ^ n) •
          (transferBlock N c n).map (algebraMap ℝ ℂ) := by
    rw [hmatrixR]
    ext x y
    simp [c, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  have hwave := cor34_final_normalizedBlockWave_scale (N := N) (n := n) hε p
  rw [hmatrixC, hwave]
  have hscale := cor34_final_normalizedZeroEigenvalue_scale
    (N := N) (n := n) (⟨q - 1, by omega⟩ : Fin n) hInv hε p
  rw [hscale]
  exact cor34_final_scale_eigen_equation hraw

end PottsDiscontinuity.SixVertex
