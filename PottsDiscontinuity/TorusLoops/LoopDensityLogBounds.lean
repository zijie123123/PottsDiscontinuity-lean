module

public import PottsDiscontinuity.TorusLoops.LoopDensityExpectation
public import PottsDiscontinuity.TorusLoops.LoopDensityExponentialTail

/-!
# Logarithmic rate bounds for the weighted loop observable

The expectation truncation bounds and exponentially small weighted tail give a
uniform estimate for the absolute logarithmic rate at every sufficiently large
even width.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.TorusRC

variable {N : ℕ}

noncomputable section

/-- The expectation's logarithmic rate along positive even widths `M=2(n+1)`. -/
noncomputable def windingLoopDensityLogRate
    (hN : Even N) (hNp : 0 < N) (q : Set.Ici (1 : ℝ)) (n : ℕ) : ℝ := by
  let M := 2 * (n + 1)
  let hM : Even M := ⟨n + 1, by omega⟩
  let hMp : 0 < M := by dsimp [M]; omega
  exact Real.log (phi_T_windingLoopDensityExpectation hN hM hNp hMp q) / (M : ℝ)

/-- Constant contribution of the two finite factors in the logarithmic bounds. -/
noncomputable def windingLoopDensityLogOffset (q : Set.Ici (1 : ℝ)) : ℝ :=
  Real.log 2 + Real.log (2 * q.val)

/-- Coefficient of the truncated loop count in the logarithmic bounds. -/
noncomputable def windingLoopDensityLogSlope (q : Set.Ici (1 : ℝ)) : ℝ :=
  Real.log (windingLoopDensityUpperBase q) - Real.log (windingLoopDensityLowerBase q)

theorem windingLoopDensityLogOffset_nonneg (q : Set.Ici (1 : ℝ)) :
    0 ≤ windingLoopDensityLogOffset q := by
  have hq : (1 : ℝ) ≤ q.val := q.property
  have h2q : 1 ≤ 2 * q.val := by nlinarith
  unfold windingLoopDensityLogOffset
  exact add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg h2q)

theorem windingLoopDensityLogSlope_nonneg (q : Set.Ici (1 : ℝ)) :
    0 ≤ windingLoopDensityLogSlope q := by
  have hU : 0 ≤ Real.log (windingLoopDensityUpperBase q) :=
    Real.log_nonneg (windingLoopDensityUpperBase_ge_one q)
  have hD : Real.log (windingLoopDensityLowerBase q) ≤ 0 :=
    Real.log_nonpos (windingLoopDensityLowerBase_pos q).le
      (windingLoopDensityLowerBase_le_one q)
  unfold windingLoopDensityLogSlope
  linarith

/-- Once the one-arm input meets the exponential-tail threshold, the absolute
logarithmic rate has the stated finite-size bound. -/
theorem abs_windingLoopDensityLogRate_le
    (hN : Even N) (hNp : 0 < N) (q : Set.Ici (1 : ℝ))
    (r n : ℕ) (hr : 0 < r)
    (hNle : N ≤ 2 * (n + 1))
    (hthreshold : 9 * N ≤ (n + 1) / r + 1)
    (harm : rectangleFreeOneArmProbability q (N / 2 - 1) ≤
      windingLoopTailArmThreshold q r) :
    |windingLoopDensityLogRate hN hNp q n| ≤
      windingLoopDensityLogSlope q / (2 * (r : ℝ)) +
        (windingLoopDensityLogOffset q + windingLoopDensityLogSlope q) /
          (2 * ((n + 1 : ℕ) : ℝ)) := by
  classical
  let M : ℕ := 2 * (n + 1)
  let hM : Even M := ⟨n + 1, by omega⟩
  let hMp : 0 < M := by dsimp [M]; omega
  let m : ℕ := (n + 1) / r + 1
  let U : ℝ := windingLoopDensityUpperBase q
  let D : ℝ := windingLoopDensityLowerBase q
  let E : ℝ := phi_T_windingLoopDensityExpectation hN hM hNp hMp q
  let P : ℝ := phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m)
  let up : ℝ := Real.log 2 + (m : ℝ) * Real.log U
  let low : ℝ := (m : ℝ) * Real.log D - Real.log (2 * q.val)
  have hqpos : 0 < q.val := lt_of_lt_of_le zero_lt_one q.property
  have hU : 1 ≤ U := by dsimp [U]; exact windingLoopDensityUpperBase_ge_one q
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hDpos : 0 < D := by dsimp [D]; exact windingLoopDensityLowerBase_pos q
  have hDle : D ≤ 1 := by dsimp [D]; exact windingLoopDensityLowerBase_le_one q
  have htail := phi_T_windingLoopDensityWeightedTail_le_pow
    hN hNp q r (n + 1) hr hNle hthreshold harm
  have hPnonneg : 0 ≤ P := by dsimp [P]; exact torusRCProbability_nonneg hN hM q _
  have hUexp : 1 ≤ U ^ (N + 2 * (n + 1)) := one_le_pow₀ hU
  have hPmul : P ≤ U ^ (N + 2 * (n + 1)) * P := by
    calc
      P = 1 * P := by ring
      _ ≤ U ^ (N + 2 * (n + 1)) * P :=
        mul_le_mul_of_nonneg_right hUexp hPnonneg
  have hPsmall : P ≤ (1 / 16 : ℝ) ^ (n + 1) := by
    dsimp [P, M] at htail ⊢
    exact hPmul.trans htail
  have hPhalf : P ≤ 1 / 2 := by
    have hbase0 : 0 ≤ (1 / 16 : ℝ) := by norm_num
    have hbase1 : (1 / 16 : ℝ) ≤ 1 := by norm_num
    have hpow : (1 / 16 : ℝ) ^ (n + 1) ≤ 1 / 16 := by
      simpa using pow_le_pow_of_le_one hbase0 hbase1
        (show 1 ≤ n + 1 by omega)
    exact hPsmall.trans (le_trans hpow (by norm_num))
  have hlowprob : 1 / 2 ≤ 1 - P := by linarith
  have htailUpper : U ^ (N + M) * P ≤ 1 := by
    have hbase0 : 0 ≤ (1 / 16 : ℝ) := by norm_num
    have hbase1 : (1 / 16 : ℝ) ≤ 1 := by norm_num
    have hpow : (1 / 16 : ℝ) ^ (n + 1) ≤ 1 := by
      exact pow_le_one₀ hbase0 hbase1
    calc
      U ^ (N + M) * P =
          windingLoopDensityUpperBase q ^ (N + 2 * (n + 1)) *
            phi_T_probability hN (show Even (2 * (n + 1)) from ⟨n + 1, by omega⟩) q
              (windingLoopTailEvent hN (show Even (2 * (n + 1)) from ⟨n + 1, by omega⟩)
                hNp (by omega) ((n + 1) / r + 1)) := by
          simp only [M, P, U, m]
      _ ≤ (1 / 16 : ℝ) ^ (n + 1) := htail
      _ ≤ 1 := hpow
  have hEupper : E ≤ 2 * U ^ m := by
    have htrunc := phi_T_windingLoopDensityExpectation_le_tail hN hM hNp hMp q m
    have htrunc' : E ≤ U ^ m + U ^ (N + M) * P := by
      simpa [E, P, U] using htrunc
    have hUm : 1 ≤ U ^ m := one_le_pow₀ hU
    calc
      E ≤ U ^ m + U ^ (N + M) * P := htrunc'
      _ ≤ U ^ m + 1 := add_le_add le_rfl htailUpper
      _ ≤ 2 * U ^ m := by nlinarith
  have hElower : D ^ m / (2 * q.val) ≤ E := by
    have htrunc := phi_T_windingLoopDensityExpectation_ge_tail hN hM hNp hMp q m
    have htrunc' : D ^ m / q.val * (1 - P) ≤ E := by
      simpa [E, P, D] using htrunc
    have hcoef : 0 ≤ D ^ m / q.val := div_nonneg (pow_nonneg hDpos.le _) hqpos.le
    have hrel : D ^ m / 2 / q.val ≤ D ^ m / q.val * (1 - P) := by
      have hmul := mul_le_mul_of_nonneg_left hlowprob hcoef
      calc
        D ^ m / 2 / q.val = D ^ m / q.val * (1 / 2 : ℝ) := by ring
        _ ≤ D ^ m / q.val * (1 - P) := by nlinarith [hmul]
    have hden : D ^ m / 2 / q.val = D ^ m / (2 * q.val) := by ring
    rw [← hden]
    exact hrel.trans htrunc'
  have hEpos : 0 < E := by
    dsimp [E]
    exact phi_T_windingLoopDensityExpectation_pos hN hM hNp hMp q
  have hupperPos : 0 < 2 * U ^ m := by positivity
  have hlogUp : Real.log E ≤ up := by
    have h := Real.log_le_log hEpos hEupper
    have heq : Real.log (2 * U ^ m) = up := by
      dsimp [up, U]
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ hUpos.ne'), Real.log_pow]
    rw [heq] at h
    exact h
  have hlowerPos : 0 < D ^ m / (2 * q.val) := by positivity
  have hlogLow : low ≤ Real.log E := by
    have h := Real.log_le_log hlowerPos hElower
    have heq : Real.log (D ^ m / (2 * q.val)) = low := by
      dsimp [low, D]
      rw [Real.log_div (pow_ne_zero _ hDpos.ne') (by positivity), Real.log_pow]
    rw [heq] at h
    exact h
  have hup0 : 0 ≤ up := by
    dsimp [up]
    exact add_nonneg (Real.log_nonneg (by norm_num))
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hU))
  have hlow0 : low ≤ 0 := by
    dsimp [low]
    have hlogD : Real.log D ≤ 0 := Real.log_nonpos hDpos.le hDle
    have hlogDen : 0 ≤ Real.log (2 * q.val) := by
      apply Real.log_nonneg
      have hq : (1 : ℝ) ≤ q.val := q.property
      nlinarith
    nlinarith
  let C₀ := windingLoopDensityLogOffset q
  let C₁ := windingLoopDensityLogSlope q
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; exact windingLoopDensityLogOffset_nonneg q
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; exact windingLoopDensityLogSlope_nonneg q
  have hgap : up - low = C₀ + (m : ℝ) * C₁ := by
    dsimp [up, low, C₀, C₁, windingLoopDensityLogOffset,
      windingLoopDensityLogSlope, U, D]
    ring
  have hgapNonneg : 0 ≤ up - low := by linarith
  have habs : |Real.log E| ≤ up - low := by
    rw [abs_le]
    constructor
    · have hcmp : -up + low ≤ 0 := by linarith [hup0]
      linarith [hlogLow]
    · linarith [hlogUp, hlow0]
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hMp
  have hMcast : (M : ℝ) = 2 * ((n + 1 : ℕ) : ℝ) := by
    simp [M]
  have hrateAbs :
      |Real.log E / (M : ℝ)| ≤ (C₀ + (m : ℝ) * C₁) /
        (2 * ((n + 1 : ℕ) : ℝ)) := by
    calc
      |Real.log E / (M : ℝ)| = |Real.log E| / (M : ℝ) := by
        rw [abs_div, abs_of_pos hMR]
      _ ≤ (up - low) / (M : ℝ) :=
        div_le_div_of_nonneg_right habs hMR.le
      _ = (C₀ + (m : ℝ) * C₁) /
          (2 * ((n + 1 : ℕ) : ℝ)) := by rw [hgap, hMcast]
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnR : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hquot : (((n + 1) / r : ℕ) : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) / (r : ℝ) := by
    apply (le_div_iff₀ hrR).2
    exact_mod_cast Nat.div_mul_le_self (n + 1) r
  have hquotMul : (((n + 1) / r : ℕ) : ℝ) * (r : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self (n + 1) r
  have hmratio : (m : ℝ) / (2 * ((n + 1 : ℕ) : ℝ)) ≤
      1 / (2 * (r : ℝ)) + 1 / (2 * ((n + 1 : ℕ) : ℝ)) := by
    apply (div_le_iff₀ (by positivity)).2
    have hmcast : (m : ℝ) = (((n + 1) / r : ℕ) : ℝ) + 1 := by simp [m]
    rw [hmcast]
    field_simp
    nlinarith [hquotMul]
  have hfinish : (C₀ + (m : ℝ) * C₁) /
        (2 * ((n + 1 : ℕ) : ℝ)) ≤
      C₁ / (2 * (r : ℝ)) + (C₀ + C₁) /
        (2 * ((n + 1 : ℕ) : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hmratio hC₁
    calc
      _ = C₀ / (2 * ((n + 1 : ℕ) : ℝ)) +
          ((m : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) * C₁ := by ring
      _ ≤ C₀ / (2 * ((n + 1 : ℕ) : ℝ)) +
          (1 / (2 * (r : ℝ)) +
            1 / (2 * ((n + 1 : ℕ) : ℝ))) * C₁ := add_le_add le_rfl hmul
      _ = C₁ / (2 * (r : ℝ)) + (C₀ + C₁) /
          (2 * ((n + 1 : ℕ) : ℝ)) := by ring
  have hrate : |Real.log E / (M : ℝ)| ≤
      C₁ / (2 * (r : ℝ)) + (C₀ + C₁) /
        (2 * ((n + 1 : ℕ) : ℝ)) := hrateAbs.trans hfinish
  simpa [windingLoopDensityLogRate, M, E, hM, hMp, C₀, C₁] using hrate

end

end PottsDiscontinuity.TorusLoops
