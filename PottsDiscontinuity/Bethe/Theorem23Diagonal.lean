module

public import PottsDiscontinuity.Bethe.Theorem23GKernel
public import PottsDiscontinuity.Bethe.Theorem23Comparison

/-! # Diagonal estimates for the rescaled Bethe Jacobian -/

@[expose] public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

/-- Exact expression for a rescaled diagonal entry in terms of the counting
function. The two omitted phase derivatives give only a mesh-size error. -/
theorem discreteBetheMatrixATilde_diag_counting {Δ : ℝ} {N n : ℕ}
    (hNnat : 0 < N) (p : Fin n → ℝ) (i : Fin (n / 2)) :
    discreteBetheMatrixATilde Δ N n p i i =
      (p (discreteHalfNextIndex n i) - p (discreteHalfIndex n i)) *
        ((N : ℝ) * (2 * Real.pi) *
            betheCountingDerivative Δ N n p (p (discreteHalfIndex n i)) -
          thetaPartialFirst Δ (p (discreteHalfIndex n i)) (p (discreteHalfIndex n i)) -
          thetaPartialSecond Δ (p (discreteHalfIndex n i))
            (p (Fin.rev (discreteHalfIndex n i)))) := by
  classical
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hNnat.ne'
  rw [discreteBetheMatrixATilde, discreteBetheMatrixB, Matrix.mul_diagonal]
  simp only [discreteBetheMatrixA, ite_true]
  have hsum := Finset.add_sum_erase Finset.univ
    (fun ell => thetaPartialFirst Δ (p (discreteHalfIndex n i)) (p ell))
    (Finset.mem_univ (discreteHalfIndex n i))
  unfold betheCountingDerivative
  change _ = _ * ((N : ℝ) * (2 * Real.pi) *
    ((1 + (∑ ell, thetaPartialFirst Δ (p (discreteHalfIndex n i)) (p ell)) / N) /
      (2 * Real.pi)) - _ - _)
  rw [← hsum]
  field_simp [hN, Real.pi_ne_zero]
  ring
/-- The counting derivative has its reciprocal-gap value at an interior point
between two consecutive roots. -/
theorem exists_betheCountingDerivative_half_mean {Δ : ℝ} (hΔ : Δ < -1)
    {N n : ℕ} (hN : 0 < N) (p : Fin n → ℝ) (hp : p ∈ S_n n)
    (hBE : DiscreteBetheEquation Δ N n p) (i : Fin (n / 2)) :
    ∃ ξ ∈ Ioo (p (discreteHalfIndex n i)) (p (discreteHalfNextIndex n i)),
      betheCountingDerivative Δ N n p ξ =
        1 / ((N : ℝ) * (p (discreteHalfNextIndex n i) - p (discreteHalfIndex n i))) := by
  have hlt : discreteHalfIndex n i < discreteHalfNextIndex n i := by
    change i.val < i.val + 1
    omega
  have hcont : Continuous (betheCountingFunction Δ N n p) :=
    continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_betheCountingFunction hΔ N n p x).continuousAt
  obtain ⟨ξ, hξ, heq⟩ := exists_hasDerivAt_eq_slope
    (betheCountingFunction Δ N n p) (betheCountingDerivative Δ N n p)
    (hp.2.1 hlt) hcont.continuousOn
    (fun x _ => hasDerivAt_betheCountingFunction hΔ N n p x)
  refine ⟨ξ, hξ, ?_⟩
  rw [betheCountingFunction_root_value hN p hBE,
    betheCountingFunction_root_value hN p hBE, ← sub_div] at heq
  have hdiff : discreteBetheIndex n (discreteHalfNextIndex n i) -
      discreteBetheIndex n (discreteHalfIndex n i) = 1 := by
    simp only [discreteBetheIndex, discreteHalfNextIndex, discreteHalfIndex,
      Nat.cast_add, Nat.cast_one, Fin.val_mk]
    ring
  rw [hdiff] at heq
  simpa only [div_div] using heq

/-- Uniform diagonal approximation. A Bethe solution and an `O(1/N)` mesh
already suffice: the mean-value identity replaces the source's intermediate
rho-dependent calculation. -/
theorem exists_uniform_rescaled_diagonal_estimate {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ ≤ Δ₀, ∀ (N n : ℕ), 0 < N → 2 * n ≤ N →
      ∀ (p : Fin n → ℝ), p ∈ S_n n → DiscreteBetheEquation Δ N n p →
      ∀ D : ℝ, 0 ≤ D →
      (∀ i : Fin (n / 2), p (discreteHalfNextIndex n i) -
        p (discreteHalfIndex n i) ≤ D / (N : ℝ)) →
      ∀ i : Fin (n / 2),
        |discreteBetheMatrixATilde Δ N n p i i - 2 * Real.pi| ≤
          C * (D ^ 2 + D) / (N : ℝ) := by
  obtain ⟨L, hL, hLip⟩ := exists_uniform_countingDerivative_lipschitz hΔ₀
  obtain ⟨B, hB, hbound⟩ := exists_uniform_d1Theta_bounds hΔ₀
  let C := 2 * Real.pi * L + 2 * B
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun Δ hΔ N n hN hs p hp hBE D hD hmesh i => ?_⟩
  have hvalid := lt_of_le_of_lt hΔ hΔ₀
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  let a := p (discreteHalfIndex n i)
  let b := p (discreteHalfNextIndex n i)
  let d := b - a
  have hd : 0 < d := sub_pos.mpr (hp.2.1 (by
    change i.val < i.val + 1
    omega))
  have hdm : d ≤ D / (N : ℝ) := hmesh i
  obtain ⟨ξ, hξ, hmean⟩ := exists_betheCountingDerivative_half_mean hvalid hN p hp hBE i
  have ha := hp.1 (discreteHalfIndex n i)
  have hb := hp.1 (discreteHalfNextIndex n i)
  have haBox : a ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) := by
    constructor <;> dsimp [a] <;> linarith [Real.pi_pos]
  have hξBox : ξ ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) := by
    constructor <;> linarith [hξ.1, hξ.2, Real.pi_pos]
  have hlip := hLip Δ hΔ N n hN p hp hs a haBox ξ hξBox
  have hdist : |a - ξ| ≤ d := by
    rw [abs_of_nonpos (by linarith [hξ.1] : a - ξ ≤ 0)]
    dsimp [d, a, b]
    linarith [hξ.2]
  have hfd : |betheCountingDerivative Δ N n p a -
      betheCountingDerivative Δ N n p ξ| ≤ L * d :=
    hlip.trans (mul_le_mul_of_nonneg_left hdist hL.le)
  have hfirst : |2 * Real.pi * (N : ℝ) * d *
      (betheCountingDerivative Δ N n p a - betheCountingDerivative Δ N n p ξ)| ≤
      (2 * Real.pi * L) * D ^ 2 / (N : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * (N : ℝ) * d)]
    have hm := mul_le_mul_of_nonneg_left hfd
      (by positivity : 0 ≤ 2 * Real.pi * (N : ℝ) * d)
    have hsq : d ^ 2 ≤ (D / (N : ℝ)) ^ 2 := sq_le_sq₀ hd.le (by positivity) |>.2 hdm
    have hscale := mul_le_mul_of_nonneg_left hsq
      (by positivity : 0 ≤ 2 * Real.pi * (N : ℝ) * L)
    calc
      _ ≤ (2 * Real.pi * (N : ℝ) * L) * d ^ 2 := by nlinarith only [hm]
      _ ≤ (2 * Real.pi * (N : ℝ) * L) * (D / (N : ℝ)) ^ 2 := hscale
      _ = _ := by field_simp
  have hba : |thetaPartialFirst Δ a a| ≤ B := (hbound Δ hΔ).1 a ⟨ha.1.le, ha.2.le⟩ a ⟨ha.1.le, ha.2.le⟩ |>.1
  have hrev := hp.1 (Fin.rev (discreteHalfIndex n i))
  have hbs : |thetaPartialSecond Δ a (p (Fin.rev (discreteHalfIndex n i)))| ≤ B := by
    rw [thetaPartialSecond_eq_neg_d1Theta hvalid, abs_neg]
    exact ((hbound Δ hΔ).1 _ ⟨hrev.1.le, hrev.2.le⟩ a ⟨ha.1.le, ha.2.le⟩).1
  have hsecond : |d * (thetaPartialFirst Δ a a +
      thetaPartialSecond Δ a (p (Fin.rev (discreteHalfIndex n i))))| ≤
      (2 * B) * D / (N : ℝ) := by
    rw [abs_mul, abs_of_pos hd]
    calc
      _ ≤ d * (|thetaPartialFirst Δ a a| +
          |thetaPartialSecond Δ a (p (Fin.rev (discreteHalfIndex n i)))|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hd.le
      _ ≤ d * (B + B) := mul_le_mul_of_nonneg_left (add_le_add hba hbs) hd.le
      _ ≤ (D / (N : ℝ)) * (B + B) := mul_le_mul_of_nonneg_right hdm (by positivity)
      _ = _ := by ring
  have hid : discreteBetheMatrixATilde Δ N n p i i - 2 * Real.pi =
      2 * Real.pi * (N : ℝ) * d *
        (betheCountingDerivative Δ N n p a - betheCountingDerivative Δ N n p ξ) -
      d * (thetaPartialFirst Δ a a +
        thetaPartialSecond Δ a (p (Fin.rev (discreteHalfIndex n i)))) := by
    rw [discreteBetheMatrixATilde_diag_counting hN, hmean]
    dsimp only [d, b, a] at hd ⊢
    field_simp [hNc.ne', hd.ne']
    ring
  rw [hid]
  calc
    _ ≤ _ := by simpa only [sub_eq_add_neg, abs_neg] using (abs_add_le
      (2 * Real.pi * (N : ℝ) * d *
        (betheCountingDerivative Δ N n p a - betheCountingDerivative Δ N n p ξ))
      (-(d * (thetaPartialFirst Δ a a +
        thetaPartialSecond Δ a (p (Fin.rev (discreteHalfIndex n i)))))))
    _ ≤ (2 * Real.pi * L) * D ^ 2 / (N : ℝ) + (2 * B) * D / (N : ℝ) :=
      add_le_add hfirst hsecond
    _ ≤ C * (D ^ 2 + D) / (N : ℝ) := by
      rw [← add_div]
      apply (div_le_div_iff_of_pos_right hNc).2
      dsimp [C]
      nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi * L) hD) (by norm_num : (0:ℝ) ≤ 1),
        mul_nonneg hB.le (sq_nonneg D)]

end PottsDiscontinuity.Bethe
