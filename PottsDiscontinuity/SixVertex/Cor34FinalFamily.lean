module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34FinalNormalization
public import PottsDiscontinuity.SixVertex.Cor34FinalWave

/-! # Corollary 3.4: discharge the conditional Bethe branch premise -/

@[expose] public section

open Filter Topology
open Matrix
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

/-- The even Theorem 2.3 family satisfies the normalized block eigenvector premise of
`cor34_even_bethe_branch_eventually_physical_pfRoot` (the Bethe side of Corollary 3.4) and hence
agrees eventually with the physical Perron root. -/
theorem cor34_final_even_family_eventually_physical_pfRoot {N n r : ℕ}
    {d₀ : ℝ} {p P : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < -1) (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n)
    (hBE : ∀ d ≤ d₀, Bethe.DiscreteBetheEquation d N n (p d))
    (hformula : ∀ d ≤ d₀, p d = P (1 / d))
    (hPanalytic : AnalyticAt ℝ P 0)
    (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    ∀ᶠ ε in 𝓝[<] (0 : ℝ),
      BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) (P ε) =
        (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
  have hPcont : ContinuousAt P 0 := hPanalytic.continuousAt
  have hInv : ∀ᶠ ε in 𝓝[<] (0 : ℝ), 1 / ε ≤ d₀ := by
    simpa only [one_div] using tendsto_inv_nhdsLT_zero.eventually (Iic_mem_atBot d₀)
  have hnonzero := cor34_final_eventually_normalizedBlockWave_ne_zero
    hPcont hP0 hNpos hbound
  have hEig : ∀ᶠ ε in 𝓝[<] (0 : ℝ),
      cor34_normalizedBlockWave (N := N) ε (P ε) ≠ 0 ∧
        (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) *ᵥ
            cor34_normalizedBlockWave (N := N) ε (P ε) =
          cor34_normalizedRegularEigenvalue ε (P ε) •
            cor34_normalizedBlockWave (N := N) ε (P ε) := by
    filter_upwards [hnonzero, hInv, self_mem_nhdsWithin] with ε hw hΔ hε
    have hε' : ε < 0 := by simpa only [Set.mem_Iio] using hε
    have hrecip : 1 / (1 / ε) = ε := by field_simp [ne_of_lt hε']
    have hS : P ε ∈ Bethe.S_n n := by
      rw [← hrecip, ← hformula (1 / ε) hΔ]
      exact hp (1 / ε) hΔ
    have hBEε := hBE (1 / ε) hΔ
    rw [hformula (1 / ε) hΔ, hrecip] at hBEε
    exact ⟨hw, cor34_final_even_normalized_eigen hε
      (lt_of_le_of_lt hΔ hd₀) (P ε) hS hn hBEε⟩
  exact cor34_even_bethe_branch_eventually_physical_pfRoot
    hPcont hP0 hNpos hbound hnpos hn hN hr hEig

/-- The odd Theorem 2.3 family satisfies the centered normalized block eigenvector premise of
`cor34_odd_bethe_branch_eventually_physical_pfRoot` (the Bethe side of Corollary 3.4)
and hence agrees eventually with the physical Perron root. -/
theorem cor34_final_odd_family_eventually_physical_pfRoot {N n q r : ℕ}
    {d₀ : ℝ} {p P : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < -1) (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n)
    (hBE : ∀ d ≤ d₀, Bethe.DiscreteBetheEquation d N n (p d))
    (hformula : ∀ d ≤ d₀, p d = P (1 / d))
    (hPanalytic : AnalyticAt ℝ P 0)
    (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    ∀ᶠ ε in 𝓝[<] (0 : ℝ),
      BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) (P ε)
          (⟨q - 1, by omega⟩ : Fin n) =
        (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
  have hPcont : ContinuousAt P 0 := hPanalytic.continuousAt
  have hInv : ∀ᶠ ε in 𝓝[<] (0 : ℝ), 1 / ε ≤ d₀ := by
    simpa only [one_div] using tendsto_inv_nhdsLT_zero.eventually (Iic_mem_atBot d₀)
  have hnonzero := cor34_final_eventually_normalizedBlockWave_ne_zero
    hPcont hP0 hNpos hbound
  have hEig : ∀ᶠ ε in 𝓝[<] (0 : ℝ),
      cor34_normalizedBlockWave (N := N) ε (P ε) ≠ 0 ∧
        (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) *ᵥ
            cor34_normalizedBlockWave (N := N) ε (P ε) =
          cor34_normalizedZeroEigenvalue (N := N) ε (P ε)
              (⟨q - 1, by omega⟩ : Fin n) •
            cor34_normalizedBlockWave (N := N) ε (P ε) := by
    filter_upwards [hnonzero, hInv, self_mem_nhdsWithin] with ε hw hΔ hε
    have hε' : ε < 0 := by simpa only [Set.mem_Iio] using hε
    have hrecip : 1 / (1 / ε) = ε := by field_simp [ne_of_lt hε']
    have hS : P ε ∈ Bethe.S_n n := by
      rw [← hrecip, ← hformula (1 / ε) hΔ]
      exact hp (1 / ε) hΔ
    have hBEε := hBE (1 / ε) hΔ
    rw [hformula (1 / ε) hΔ, hrecip] at hBEε
    exact ⟨hw, cor34_final_odd_normalized_eigen hε
      (lt_of_le_of_lt hΔ hd₀) (P ε) hS hnq hBEε⟩
  exact cor34_odd_bethe_branch_eventually_physical_pfRoot
    hPcont hP0 hNpos hbound hnpos hnq hN hr hEig

end PottsDiscontinuity.SixVertex
