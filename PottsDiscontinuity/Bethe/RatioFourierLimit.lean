module

public import PottsDiscontinuity.Bethe.RatioEvenLimit
public import PottsDiscontinuity.Bethe.RatioOddLimit

/-! # Section 4 Fourier composition for the even eigenvalue-ratio limit -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

section

variable {Δ : ℝ} (hΔ : Δ < -1) (r : ℕ) (N : ℕ → ℕ) (h4 : ∀ i, 4 ∣ N i)
    (hr : ∀ i, r ≤ N i / 2) (hN : ∀ i, 0 < N i) (hn : ∀ i, 0 < N i / 2 - r)
    (p : ∀ i, Fin (N i / 2) → ℝ) (q : ∀ i, Fin (N i / 2 - r) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (hq : ∀ i, q i ∈ S_n (N i / 2 - r))
    (hpBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2) (p i))
    (hqBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2 - r) (q i))
    (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    (hbp : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hbq : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    {K : ℝ} (hK : 0 ≤ K)
    (hrate : ∀ᶠ i in atTop,
      densityNorm Δ hΔ (fun x => rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) x - rho Δ x) (hbp i) ≤ K / N i ∧
      densityNorm Δ hΔ (fun x => rootStepDensity (N i) (N i / 2 - r) (q i) (hq i)
        (hn i) (two_mul_half_sub_le N r i) x - rho Δ x) (hbq i) ≤ K / N i)


include hΔ h4 hr hN hp hq hpBE hqBE hNlim hbp hbq hK hrate

/-- The even-branch quotient limit in the explicit Section 4 Fourier form.
The same alternating-series limit `S` gives the exponent `-r(λ+2S)`. -/
theorem ratio_even_eigenvalue_limit_fourier (heven : r % 2 = 0)
    (hrpos : 1 ≤ r) {c : ℝ} (hc : 2 < c) (hcΔ : anisotropy c = Δ) :
    ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial (lamOf Δ)) atTop (𝓝 S) ∧
      Tendsto (fun i => eigenvalueRegular c (q i) / eigenvalueRegular c (p i)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) * (lamOf Δ + 2 * S)) : ℝ) : ℂ)) := by
  have hlam : 0 < lamOf Δ := lamOf_pos hΔ
  have hrnat : 0 < r := by omega
  obtain ⟨S, hS, hW15⟩ := PottsDiscontinuity.fourierRatioExponent
    (lam := lamOf Δ) (r := (r : ℝ)) hlam
  have hparam : -Real.cosh (lamOf Δ) = Δ := by rw [cosh_lamOf hΔ]; ring
  have hlog : Real.log |Δ| = Real.log |-(Real.cosh (lamOf Δ))| := by rw [hparam]
  have hIntegral := ratio_integral_eq_fourier hΔ hc hcΔ
  have hExponent : -(r : ℝ) * Real.log |Δ| +
      (r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x =
      -(r : ℝ) * (lamOf Δ + 2 * S) := by
    simpa only [hlog, hIntegral] using hW15
  have hlimit := ratio_even_eigenvalue_limit hΔ r N h4 hr hN hn p q hp hq
    hpBE hqBE hNlim hbp hbq hK hrate heven hc hcΔ
  have hcomposed : Tendsto (fun i => eigenvalueRegular c (q i) / eigenvalueRegular c (p i)) atTop
      (𝓝 ((Real.exp (-(r : ℝ) * (lamOf Δ + 2 * S)) : ℝ) : ℂ)) := by
    simpa only [hExponent] using hlimit
  exact ⟨S, hS, hcomposed⟩

end

end PottsDiscontinuity.Bethe
