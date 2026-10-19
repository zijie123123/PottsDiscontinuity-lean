module

public import PottsDiscontinuity.TorusLoops.LoopDensityObservable
public import PottsDiscontinuity.TorusLoops.LoopTailProbability

/-!
# Exponential control of the weighted large-loop tail

For a threshold proportional to the width, a sufficiently small one-arm
probability makes both the large-loop probability and its maximal observable
contribution exponentially small in the width.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.TorusRC

variable {N : ℕ}

noncomputable section

/-- Amplification factor combining the maximal observable with the seam cost. -/
noncomputable def windingLoopTailAmplification (q : Set.Ici (1 : ℝ)) : ℝ :=
  2 * windingLoopDensityUpperBase q /
    (1 - (rcCriticalParameter q).val)

/-- A one-arm probability threshold that absorbs the seam and observable
amplification for a loop threshold of scale `n / r`. -/
noncomputable def windingLoopTailArmThreshold (q : Set.Ici (1 : ℝ)) (r : ℕ) : ℝ :=
  (1 / (16 * windingLoopTailAmplification q ^ 4)) ^ (3 * r)

theorem windingLoopTailAmplification_ge_one (q : Set.Ici (1 : ℝ)) :
    1 ≤ windingLoopTailAmplification q := by
  have hU : 1 ≤ windingLoopDensityUpperBase q := windingLoopDensityUpperBase_ge_one q
  have ha : 0 < 1 - (rcCriticalParameter q).val := by
    exact sub_pos.mpr (criticalParameter_lt_one q)
  have ha_le : 1 - (rcCriticalParameter q).val ≤ 1 := by
    linarith [criticalParameter_pos q]
  unfold windingLoopTailAmplification
  apply (le_div_iff₀ ha).2
  nlinarith

theorem windingLoopTailArmThreshold_pos (q : Set.Ici (1 : ℝ)) (r : ℕ) :
    0 < windingLoopTailArmThreshold q r := by
  have hB : 0 < windingLoopTailAmplification q :=
    lt_of_lt_of_le zero_lt_one (windingLoopTailAmplification_ge_one q)
  unfold windingLoopTailArmThreshold
  positivity

/-- At width `2*n`, with threshold `n/r+1`, the maximal observable times the
large-loop probability is at most `16^{-n}` when the one-arm input is small
enough. -/
theorem phi_T_windingLoopDensityWeightedTail_le_pow
    (hN : Even N) (hNp : 0 < N) (q : Set.Ici (1 : ℝ))
    (r n : ℕ) (hr : 0 < r) (hNle : N ≤ 2 * n)
    (hthreshold : 9 * N ≤ n / r + 1)
    (harm : rectangleFreeOneArmProbability q (N / 2 - 1) ≤
      windingLoopTailArmThreshold q r) :
    windingLoopDensityUpperBase q ^ (N + 2 * n) *
      phi_T_probability hN (show Even (2 * n) from ⟨n, by omega⟩) q
        (windingLoopTailEvent hN (show Even (2 * n) from ⟨n, by omega⟩)
          hNp (by omega) (n / r + 1)) ≤
      (1 / 16 : ℝ) ^ n := by
  classical
  let M : ℕ := 2 * n
  let hM : Even M := ⟨n, by omega⟩
  let hMp : 0 < M := by dsimp [M]; omega
  let m : ℕ := n / r + 1
  let U : ℝ := windingLoopDensityUpperBase q
  let B : ℝ := windingLoopTailAmplification q
  let θ : ℝ := 1 / (16 * B ^ 4)
  let ρ : ℝ := rectangleFreeOneArmProbability q (N / 2 - 1)
  let k : ℕ := (m - 3 * N + 1) / 2
  have hU : 1 ≤ U := by dsimp [U]; exact windingLoopDensityUpperBase_ge_one q
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hB : 1 ≤ B := by dsimp [B]; exact windingLoopTailAmplification_ge_one q
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hθ0 : 0 < θ := by
    dsimp [θ]
    positivity
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    have hpow : 1 ≤ B ^ 4 := one_le_pow₀ hB
    apply (div_le_one (by positivity)).2
    nlinarith
  have hρ0 : 0 ≤ ρ := by
    change 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1)
    unfold rectangleFreeOneArmProbability
    exact NNReal.coe_nonneg _
  have hρle : ρ ≤ θ ^ (3 * r) := by
    dsimp [ρ, θ, B, U] at harm ⊢
    exact harm
  have hmlarge : 9 * N ≤ m := by simpa [m] using hthreshold
  have hklarge : m ≤ 3 * k := by
    have hdiv := Nat.mod_add_div (m - 3 * N + 1) 2
    have hmod := Nat.mod_lt (m - 3 * N + 1) (by norm_num : 0 < 2)
    dsimp [k]
    omega
  have hnr : n ≤ r * m := by
    have hmod := Nat.mod_lt n hr
    dsimp [m]
    calc
      n = n % r + r * (n / r) := (Nat.mod_add_div n r).symm
      _ ≤ r + r * (n / r) := Nat.add_le_add_right hmod.le _
      _ = r * (n / r + 1) := by rw [Nat.mul_add]; omega
  have hρpow : ρ ^ k ≤ θ ^ n := by
    calc
      ρ ^ k ≤ (θ ^ (3 * r)) ^ k :=
        pow_le_pow_left₀ hρ0 hρle k
      _ = θ ^ (3 * r * k) := by rw [← pow_mul]
      _ ≤ θ ^ (r * m) := by
        apply pow_le_pow_of_le_one hθ0.le hθ1
        nlinarith [Nat.mul_le_mul_left r hklarge]
      _ ≤ θ ^ n := pow_le_pow_of_le_one hθ0.le hθ1 hnr
  have htail := torusRCProbability_windingTail_le_rootUnion
    hN hM hNp hMp q m
  have ha : 0 < 1 - (rcCriticalParameter q).val := by
    exact sub_pos.mpr (criticalParameter_lt_one q)
  have hexp : N + M = N + 2 * n := by dsimp [M]
  have hpow2 : (2 : ℝ) ^ M ≤ 2 ^ (N + M) := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hfactor : U ^ (N + M) *
      ((2 : ℝ) ^ M / (1 - (rcCriticalParameter q).val) ^ (N + M)) ≤
        B ^ (N + M) := by
    have hnum : U ^ (N + M) * 2 ^ M ≤ U ^ (N + M) * 2 ^ (N + M) :=
      mul_le_mul_of_nonneg_left hpow2 (pow_nonneg hU0 _)
    have hdenPos : 0 <
        (1 - (rcCriticalParameter q).val) ^ (N + M) := pow_pos ha _
    have heq : (U ^ (N + M) * 2 ^ (N + M)) /
        (1 - (rcCriticalParameter q).val) ^ (N + M) = B ^ (N + M) := by
      dsimp [B, windingLoopTailAmplification]
      rw [div_pow, mul_pow]
      ring
    dsimp [B, windingLoopTailAmplification] at heq ⊢
    calc
      U ^ (N + M) *
          (2 ^ M / (1 - (rcCriticalParameter q).val) ^ (N + M)) ≤
        (U ^ (N + M) * 2 ^ (N + M)) /
          (1 - (rcCriticalParameter q).val) ^ (N + M) := by
            calc
              _ = (U ^ (N + M) * 2 ^ M) /
                  (1 - (rcCriticalParameter q).val) ^ (N + M) := by ring
              _ ≤ (U ^ (N + M) * 2 ^ (N + M)) /
                  (1 - (rcCriticalParameter q).val) ^ (N + M) :=
                div_le_div_of_nonneg_right hnum hdenPos.le
      _ = B ^ (N + M) := heq
  have hweighted : U ^ (N + M) *
      phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
        B ^ (N + M) * ρ ^ k := by
    have hprob : 0 ≤ phi_T_probability hN hM q
        (windingLoopTailEvent hN hM hNp hMp m) :=
      torusRCProbability_nonneg hN hM q _
    have htail' := mul_le_mul_of_nonneg_left htail (pow_nonneg hU0 (N + M))
    calc
      _ ≤ U ^ (N + M) *
          ((2 : ℝ) ^ M * ρ ^ k /
            (1 - (rcCriticalParameter q).val) ^ (N + M)) := htail'
      _ = (U ^ (N + M) *
          (2 ^ M / (1 - (rcCriticalParameter q).val) ^ (N + M))) * ρ ^ k := by ring
      _ ≤ B ^ (N + M) * ρ ^ k :=
        mul_le_mul_of_nonneg_right hfactor (pow_nonneg hρ0 _)
  have hsmall : B ^ (N + M) * ρ ^ k ≤ (1 / 16 : ℝ) ^ n := by
    rw [hexp]
    calc
      B ^ (N + 2 * n) * ρ ^ k ≤ B ^ (N + 2 * n) * θ ^ n :=
        mul_le_mul_of_nonneg_left hρpow (pow_nonneg hB0 _)
      _ = B ^ N * (B ^ 2 * θ) ^ n := by
        rw [pow_add, pow_mul]
        ring
      _ ≤ (1 / 16 : ℝ) ^ n := by
        have hBpowN : B ^ N ≤ B ^ (2 * n) := pow_le_pow_right₀ hB (by omega)
        have hprod : B ^ N * (B ^ 2 * θ) ^ n ≤
            B ^ (2 * n) * (B ^ 2 * θ) ^ n :=
          mul_le_mul_of_nonneg_right hBpowN (pow_nonneg (mul_nonneg (pow_nonneg hB0 _) hθ0.le) _)
        have hid : B ^ (2 * n) * (B ^ 2 * θ) ^ n = (1 / 16 : ℝ) ^ n := by
          rw [show B ^ (2 * n) = (B ^ 2) ^ n by rw [pow_mul]]
          rw [← mul_pow]
          congr 1
          dsimp [θ]
          field_simp
        exact hprod.trans_eq hid
  have hfinal : U ^ (N + M) *
      phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
        (1 / 16 : ℝ) ^ n := hweighted.trans hsmall
  simpa [M, m, hN, hM, hMp, U, B] using hfinal

end

end PottsDiscontinuity.TorusLoops
