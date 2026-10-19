module

public import PottsDiscontinuity.Bethe.RatioFourierLimit

/-! # Sign-invariant formulation for the parameter `c` -/

@[expose] public section

open Set Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

/-- The Bethe factors depend on `c` only through `c²`. -/
theorem ratio_L_abs (c : ℝ) (w : ℂ) : L (|c|) w = L c w := by
  have hsquare : (((|c| : ℝ) : ℂ) ^ 2) = (c : ℂ) ^ 2 := by
    exact_mod_cast (sq_abs c)
  unfold L
  rw [hsquare]

theorem ratio_M_abs (c : ℝ) (w : ℂ) : M (|c|) w = M c w := by
  have hsquare : (((|c| : ℝ) : ℂ) ^ 2) = (c : ℂ) ^ 2 := by
    exact_mod_cast (sq_abs c)
  unfold M
  rw [hsquare]

theorem ratio_eigenvalueRegular_abs {n : ℕ} (c : ℝ) (p : Fin n → ℝ) :
    eigenvalueRegular (|c|) p = eigenvalueRegular c p := by
  simp only [eigenvalueRegular, ratio_L_abs, ratio_M_abs]

theorem ratio_eigenvalueZero_abs {n : ℕ} (N : ℕ) (c : ℝ)
    (p : Fin n → ℝ) (l : Fin n) :
    eigenvalueZero N (|c|) p l = eigenvalueZero N c p l := by
  have hani : anisotropy (|c|) = anisotropy c := by
    unfold anisotropy
    rw [sq_abs]
  have hsquare : (((|c| : ℝ) : ℂ) ^ 2) = (c : ℂ) ^ 2 := by
    exact_mod_cast (sq_abs c)
  unfold eigenvalueZero
  rw [hsquare, hani]
  simp only [ratio_M_abs]

/-- The relation `anisotropy c = Δ < -1` forces `|c| > 2`. -/
theorem ratio_abs_gt_two {Δ c : ℝ} (hΔ : Δ < -1) (hcΔ : anisotropy c = Δ) :
    2 < |c| := by
  have hc2 : 4 < c ^ 2 := by
    unfold anisotropy at hcΔ
    nlinarith
  nlinarith [sq_abs c, abs_nonneg c]

theorem ratio_anisotropy_abs {Δ c : ℝ} (hcΔ : anisotropy c = Δ) :
    anisotropy (|c|) = Δ := by
  have h := hcΔ
  unfold anisotropy at h ⊢
  rw [sq_abs]
  exact h

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

/-- Both Fourier-composed parity limits for either sign of `c`. -/
theorem ratio_even_eigenvalue_limit_fourier_any_sign (heven : r % 2 = 0)
    (hrpos : 1 ≤ r) {c : ℝ} (hcΔ : anisotropy c = Δ) :
    ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial (lamOf Δ)) atTop (𝓝 S) ∧
      Tendsto (fun i => eigenvalueRegular c (q i) / eigenvalueRegular c (p i)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) * (lamOf Δ + 2 * S)) : ℝ) : ℂ)) := by
  obtain ⟨S, hS, hlimit⟩ := ratio_even_eigenvalue_limit_fourier hΔ r N h4 hr hN hn p q
    hp hq hpBE hqBE hNlim hbp hbq hK hrate heven hrpos (ratio_abs_gt_two hΔ hcΔ)
    (ratio_anisotropy_abs hcΔ)
  refine ⟨S, hS, ?_⟩
  apply hlimit.congr
  intro i
  rw [ratio_eigenvalueRegular_abs c (q i), ratio_eigenvalueRegular_abs c (p i)]

theorem ratio_odd_eigenvalue_limit_fourier_any_sign (hodd : r % 2 ≠ 0)
    (hrpos : 1 ≤ r) {c : ℝ} (hcΔ : anisotropy c = Δ) :
    ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial (lamOf Δ)) atTop (𝓝 S) ∧
      Tendsto (fun i => eigenvalueZero (N i) c (q i)
        ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hn i) Nat.one_lt_two⟩ /
          eigenvalueRegular c (p i)) atTop
        (𝓝 ((Real.exp (-(r : ℝ) * (lamOf Δ + 2 * S)) : ℝ) : ℂ)) := by
  obtain ⟨S, hS, hlimit⟩ := ratio_odd_eigenvalue_limit_fourier hΔ r N h4 hr hN hn p q
    hp hq hpBE hqBE hNlim hbp hbq hK hrate hodd hrpos (ratio_abs_gt_two hΔ hcΔ)
    (ratio_anisotropy_abs hcΔ)
  refine ⟨S, hS, ?_⟩
  apply hlimit.congr
  intro i
  rw [ratio_eigenvalueZero_abs (N i) c (q i) _,
    ratio_eigenvalueRegular_abs c (p i)]

end

end PottsDiscontinuity.Bethe
