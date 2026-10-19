module

public import PottsDiscontinuity.Bethe.Theorem23Family

/-! # Theorem 2.3 in the even-size formulation of the source -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

/-- Theorem 2.3 for every sufficiently large even N, with n=N/2-r. -/
theorem theorem23 (r : ℕ) {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 0 < N₀ ∧ ∃ Δ₁ : ℝ, Δ₀ < Δ₁ ∧ Δ₁ < -1 ∧
      ∀ N : ℕ, N₀ ≤ N → Even N →
      let n := N / 2 - r
      ∃ hn : 0 < n, ∃ hs : 2 * n ≤ N,
      ∃ p : ℝ → (Fin n → ℝ),
      ∃ hp : ∀ (Δ : ℝ), Δ ≤ Δ₀ → p Δ ∈ S_n n,
        (∀ Δ ≤ Δ₀, DiscreteBetheEquation Δ N n (p Δ)) ∧
        AnalyticOnNhd ℝ p (Iio Δ₁) ∧
        (∃ P : ℝ → (Fin n → ℝ), AnalyticAt ℝ P 0 ∧
          P 0 = discreteBaseSolution N n ∧ ∀ Δ ≤ Δ₀, p Δ = P (1 / Δ)) ∧
        ∀ (Δ : ℝ) (hΔ : Δ ≤ Δ₀),
          densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
            (fun x => rootStepDensity N n (p Δ) (hp Δ hΔ) hn hs x - rho Δ x)
            (rootStepDensity_error_bddAbove (lt_of_le_of_lt hΔ hΔ₀) _ (hp Δ hΔ) hn hs) ≤ K / N := by
  obtain ⟨K, hK, M₀, hM₀, Δ₁, hΔ₀₁, hΔ₁, hfamily⟩ := theorem23_analytic_family r hΔ₀
  refine ⟨K, hK, max M₀ (2 * (r + 1)), lt_of_lt_of_le hM₀ (le_max_left _ _),
    Δ₁, hΔ₀₁, hΔ₁, fun N hlarge heven => ?_⟩
  have hMlarge : M₀ ≤ N := (le_max_left _ _).trans hlarge
  have hrlarge : 2 * (r + 1) ≤ N := (le_max_right _ _).trans hlarge
  obtain ⟨m, hm⟩ := heven
  have hn : 0 < N / 2 - r := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  dsimp only
  rw [hk]
  have hcount : N = 2 * ((k + 1) + r) := by omega
  have hs : 2 * (k + 1) ≤ N := by omega
  exact ⟨by omega, hs, hfamily N k hMlarge hcount hs⟩

end PottsDiscontinuity.Bethe
