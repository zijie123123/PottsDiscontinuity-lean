module

public import PottsDiscontinuity.Bethe.Theorem23RegularRegion
public import PottsDiscontinuity.Bethe.Theorem23CompactIFT

/-! # The analytic family of Bethe roots -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

/-- Theorem 2.3, with the exact root count encoded as `N=2*(n+r)` and positive
root count written as `n=k+1`. The finite-parameter analytic domain is open and
contains the requested endpoint. Analyticity at minus infinity is supplied by
an actual analytic inverse-parameter family through the explicit base root. -/
theorem theorem23_analytic_family (r : ℕ) {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 0 < N₀ ∧ ∃ Δ₁ : ℝ, Δ₀ < Δ₁ ∧ Δ₁ < -1 ∧
      ∀ (N k : ℕ), N₀ ≤ N → N = 2 * ((k + 1) + r) →
      ∀ hs : 2 * (k + 1) ≤ N,
      ∃ p : ℝ → (Fin (k + 1) → ℝ),
      ∃ hp : ∀ (Δ : ℝ), Δ ≤ Δ₀ → p Δ ∈ S_n (k + 1),
        (∀ Δ ≤ Δ₀, DiscreteBetheEquation Δ N (k + 1) (p Δ)) ∧
        AnalyticOnNhd ℝ p (Iio Δ₁) ∧
        (∃ P : ℝ → (Fin (k + 1) → ℝ), AnalyticAt ℝ P 0 ∧
          P 0 = discreteBaseSolution N (k + 1) ∧ ∀ Δ ≤ Δ₀, p Δ = P (1 / Δ)) ∧
        ∀ (Δ : ℝ) (hΔ : Δ ≤ Δ₀),
          densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
            (fun x => rootStepDensity N (k + 1) (p Δ) (hp Δ hΔ) (by omega) hs x - rho Δ x)
            (rootStepDensity_error_bddAbove (lt_of_le_of_lt hΔ hΔ₀) _ (hp Δ hΔ) (by omega) hs) ≤ K / N := by
  let Δ₁ := (Δ₀ - 1) / 2
  have hΔ₁ : Δ₁ < -1 := by dsimp [Δ₁]; linarith
  have hΔ₀₁ : Δ₀ < Δ₁ := by dsimp [Δ₁]; linarith
  obtain ⟨c, D, K, hc, _, _, hK, N₀, hN₀, hregion⟩ :=
    exists_uniform_regular_Bethe_region r hΔ₁
  refine ⟨K, hK, N₀, hN₀, Δ₁, hΔ₀₁, hΔ₁, fun N k hlarge hcount hs => ?_⟩
  have hN : 0 < N := lt_of_lt_of_le hN₀ hlarge
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  let C := betheGapRegion k (c / N) (D / N)
  let F := fun z : ℝ × (Fin ((k + 1) / 2) → ℝ) => discreteCoordinateResidualInv z.1 N (k + 1) z.2
  obtain ⟨hbaseInterior, hregular, hnorm⟩ := hregion N k hlarge hcount hs
  have hcompact : IsCompact C := isCompact_betheGapRegion k (div_pos hc hNc)
  have hbaseC : discreteBaseCoordinates N (k + 1) ∈ C := interior_subset hbaseInterior
  have hbase : ∃! q : C, F (0, q.val) = 0 := by
    refine ⟨⟨discreteBaseCoordinates N (k + 1), hbaseC⟩,
      discreteCoordinateResidualInv_base_zero hN hs, fun q hq => ?_⟩
    apply Subtype.ext
    exact (discreteCoordinateResidualInv_base_unique hN hs).unique hq
      (discreteCoordinateResidualInv_base_zero hN hs)
  have ha : 1 / Δ₁ < 0 := one_div_neg.mpr (by linarith)
  obtain ⟨b, hb, ψ, hψanalytic, hψzero, hψC⟩ :=
    exists_analytic_implicit_family_on_open_interval hcompact ha
      (fun ε hε q _ => analyticAt_discreteCoordinateResidualInv
        (abs_compact_inverse_parameter_lt_one hΔ₁ hε) N (k + 1) q)
      hregular hbase
  let P : ℝ → (Fin (k + 1) → ℝ) := fun ε => discreteSymLift (k + 1) (ψ ε)
  let p : ℝ → (Fin (k + 1) → ℝ) := fun Δ => P (1 / Δ)
  have hparameter (Δ : ℝ) (hΔ : Δ ≤ Δ₀) : 1 / Δ ∈ Icc (1 / Δ₁) 0 :=
    inverse_parameter_mem hΔ₁ (hΔ.trans hΔ₀₁.le)
  have hp (Δ : ℝ) (hΔ : Δ ≤ Δ₀) : p Δ ∈ S_n (k + 1) :=
    betheGapRegion_mem_S_n (div_pos hc hNc) (hψC _ (hparameter Δ hΔ)).1
  have hBE (Δ : ℝ) (hΔ : Δ ≤ Δ₀) : DiscreteBetheEquation Δ N (k + 1) (p Δ) := by
    apply (discreteCoordinateResidual_zero_iff hN (ψ (1 / Δ))).1
    rw [← discreteCoordinateResidualInv_eq (lt_of_le_of_lt hΔ hΔ₀)]
    exact (hψC _ (hparameter Δ hΔ)).2
  have hPanalytic (ε : ℝ) (hε : ε ∈ Ioo (1 / Δ₁) b) : AnalyticAt ℝ P ε :=
    (discreteSymLift (k + 1)).toContinuousLinearMap.analyticAt _ |>.comp (hψanalytic ε hε)
  have hpAnalytic : AnalyticOnNhd ℝ p (Iio Δ₁) := by
    intro Δ hΔ
    have hvalid : Δ < -1 := lt_trans hΔ hΔ₁
    have hε : 1 / Δ ∈ Ioo (1 / Δ₁) b := by
      have hΔneg : Δ < 0 := by linarith
      have hΔ₁neg : Δ₁ < 0 := by linarith
      refine ⟨?_, (one_div_neg.mpr hΔneg).trans hb⟩
      exact one_div_lt_one_div_of_neg_of_lt hΔ₁neg hΔ
    have hinv : AnalyticAt ℝ (fun t : ℝ => 1 / t) Δ :=
      analyticAt_const.div analyticAt_id (ne_of_lt (by linarith : Δ < 0))
    exact (hPanalytic _ hε).comp hinv
  have hPzero : P 0 = discreteBaseSolution N (k + 1) := by
    have hqzero := (hψC 0 ⟨ha.le, le_rfl⟩).2
    have hqbase : ψ 0 = discreteBaseCoordinates N (k + 1) :=
      (discreteCoordinateResidualInv_base_unique hN hs).unique hqzero
        (discreteCoordinateResidualInv_base_zero hN hs)
    dsimp only [P]
    rw [hqbase]
    exact discreteSymLift_coordinates _ (discreteBaseSolution_mem_S_n hN hs).2.2
  refine ⟨p, hp, hBE, hpAnalytic, ⟨P, hPanalytic 0 ⟨ha, hb⟩, hPzero, fun _ _ => rfl⟩, ?_⟩
  intro Δ hΔ
  exact hnorm Δ (hΔ.trans hΔ₀₁.le) (ψ (1 / Δ)) (hψC _ (hparameter Δ hΔ)).1
    (hBE Δ hΔ) (hp Δ hΔ)

end PottsDiscontinuity.Bethe
