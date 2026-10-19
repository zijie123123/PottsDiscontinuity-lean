module

public import Mathlib

/-!
# Exponential-growth comparison for the dominance repair

This real-analysis lemma isolates the inequality behind the large-`N` repair.  One-sided eventual
bounds for the two logarithmic growth rates are a reusable formulation of the corresponding
limsup hypotheses.  To apply it along even heights, replace each sequence `F M` by `F (2*M)`.
-/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.SixVertex

/-- If a positive exponential lower bound for `X` is controlled above by `Y * Z`, then the
exponential rate of `X` cannot exceed the sum of the one-sided rates of `Y` and `Z`. -/
theorem log_growth_le_of_eventually_factorized
    {C Λ Λmax a b : ℝ} (hC : 0 < C) (hΛ : 0 < Λ)
    (X Y Z : ℕ → ℝ)
    (hYpos : ∀ᶠ M : ℕ in atTop, 0 < Y M)
    (hZpos : ∀ᶠ M : ℕ in atTop, 0 < Z M)
    (hlower : ∀ᶠ M : ℕ in atTop, C * Λ ^ M ≤ X M)
    (hupper : ∀ᶠ M : ℕ in atTop, X M ≤ Y M * Z M)
    (hYrate : ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop,
      (1 / (M : ℝ)) * Real.log (Y M) ≤ a + ε)
    (hZrate : ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop,
      (1 / (M : ℝ)) * Real.log (Z M) ≤ Real.log Λmax + b + ε) :
    Real.log Λ ≤ Real.log Λmax + a + b := by
  by_contra hnot
  have hgap : Real.log Λmax + a + b < Real.log Λ := lt_of_not_ge hnot
  let ε : ℝ := (Real.log Λ - (Real.log Λmax + a + b)) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hinv : Tendsto (fun M : ℕ => 1 / (M : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsmall : Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log C) atTop (𝓝 0) := by
    simpa using hinv.mul_const (Real.log C)
  have hsum : Tendsto (fun M : ℕ => Real.log Λ +
      (1 / (M : ℝ)) * Real.log C) atTop (𝓝 (Real.log Λ)) := by
    simpa using (tendsto_const_nhds (x := Real.log Λ)).add hsmall
  have hleft : Tendsto (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log (C * Λ ^ M)) atTop (𝓝 (Real.log Λ)) := by
    have heq : (fun M : ℕ => (1 / (M : ℝ)) * Real.log (C * Λ ^ M)) =ᶠ[atTop]
        (fun M : ℕ => Real.log Λ + (1 / (M : ℝ)) * Real.log C) := by
      filter_upwards [eventually_gt_atTop 0] with M hM
      have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      have hpow : Λ ^ M ≠ 0 := pow_ne_zero _ hΛ.ne'
      rw [Real.log_mul hC.ne' hpow]
      simp only [Real.log_pow]
      field_simp
      ring
    exact hsum.congr' heq.symm
  have hleftEvent : ∀ᶠ M : ℕ in atTop,
      Real.log Λmax + a + b + 3 * ε <
        (1 / (M : ℝ)) * Real.log (C * Λ ^ M) := by
    have hthreshold : Real.log Λmax + a + b + 3 * ε < Real.log Λ := by
      dsimp [ε]
      linarith
    exact hleft.eventually (Ioi_mem_nhds hthreshold)
  have hY := hYrate ε hε
  have hZ := hZrate ε hε
  have hMpos : ∀ᶠ M : ℕ in atTop, 0 < M := eventually_gt_atTop 0
  have hfalse : ∀ᶠ M : ℕ in atTop, False := by
    filter_upwards [hleftEvent, hlower, hupper, hYpos, hZpos, hY, hZ, hMpos]
      with M hleftM hlowerM hupperM hYposM hZposM hYM hZM hMposM
    have hbasepos : 0 < C * Λ ^ M := mul_pos hC (pow_pos hΛ M)
    have hXpos : 0 < X M := lt_of_lt_of_le hbasepos hlowerM
    have hlog₁ := Real.log_le_log hbasepos hlowerM
    have hlog₂ := Real.log_le_log hXpos hupperM
    rw [Real.log_mul hYposM.ne' hZposM.ne'] at hlog₂
    have hlog : Real.log (C * Λ ^ M) ≤ Real.log (Y M) + Real.log (Z M) :=
      hlog₁.trans hlog₂
    have hscaled := mul_le_mul_of_nonneg_left hlog (by positivity :
      0 ≤ (1 / (M : ℝ)))
    have htarget : (1 / (M : ℝ)) * Real.log (C * Λ ^ M) ≤
        Real.log Λmax + a + b + 2 * ε := by
      calc
        (1 / (M : ℝ)) * Real.log (C * Λ ^ M) ≤
            (1 / (M : ℝ)) * Real.log (Y M) +
              (1 / (M : ℝ)) * Real.log (Z M) := by
                simpa [mul_add] using hscaled
        _ ≤ Real.log Λmax + a + b + 2 * ε := by linarith
    linarith
  rcases hfalse.exists with ⟨M, hM⟩
  exact hM

end PottsDiscontinuity.SixVertex
