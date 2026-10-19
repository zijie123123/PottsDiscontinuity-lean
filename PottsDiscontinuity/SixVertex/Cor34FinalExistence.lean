module

public import Mathlib
public import PottsDiscontinuity.Bethe.Theorem23
public import PottsDiscontinuity.SixVertex.Cor34Final

/-! # Endpoint and existence forms of Corollary 3.4 -/

@[expose] public section

open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

/-- The real Bethe eigenvalue `Λ(p)` in the two source formulas, selected by root parity. -/
noncomputable def cor34BetheLambda (N n : ℕ) (c : ℝ) (p : Fin n → ℝ) : ℝ := by
  classical
  exact if he : Even n then
    2 * ∏ j : Fin n, ‖BetheAnsatz.M c (BetheAnsatz.z (p j))‖
  else
    let q : ℕ := n / 2 + 1
    let l : Fin n := ⟨q - 1, by
      have ho : Odd n := Nat.not_even_iff_odd.mp he
      obtain ⟨k, hk⟩ := ho
      omega
    ⟩
    (2 + c ^ 2 * ((N : ℝ) - 1) + c ^ 2 *
      ∑ j ∈ Finset.univ.erase l,
        deriv (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0) *
      ∏ j ∈ Finset.univ.erase l, ‖BetheAnsatz.M c (BetheAnsatz.z (p j))‖

/-- Endpoint specialization for even root count. -/
theorem cor34_final_even_at_endpoint {N n r : ℕ}
    {d₀ d₁ : ℝ} {p P : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < -1) (hd₀₁ : d₀ < d₁) (hd₁ : d₁ < -1)
    (hpAnalytic : AnalyticOnNhd ℝ p (Set.Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n)
    (hBE : ∀ d ≤ d₀, Bethe.DiscreteBetheEquation d N n (p d))
    (hformula : ∀ d ≤ d₀, p d = P (1 / d))
    (hPanalytic : AnalyticAt ℝ P 0)
    (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    (pfRoot (transferBlock N (Real.sqrt (2 - 2 * d₀)) n) : ℂ) =
      BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 * d₀)) (p d₀) :=
  cor34_final_even_all_parameters hd₀ hd₀₁ hd₁ hpAnalytic hp hBE hformula
    hPanalytic hP0 hNpos hbound hnpos hn hN hr d₀ le_rfl

/-- Endpoint specialization for odd root count, including its central zero root. -/
theorem cor34_final_odd_at_endpoint {N n q r : ℕ}
    {d₀ d₁ : ℝ} {p P : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < -1) (hd₀₁ : d₀ < d₁) (hd₁ : d₁ < -1)
    (hpAnalytic : AnalyticOnNhd ℝ p (Set.Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n)
    (hBE : ∀ d ≤ d₀, Bethe.DiscreteBetheEquation d N n (p d))
    (hformula : ∀ d ≤ d₀, p d = P (1 / d))
    (hPanalytic : AnalyticAt ℝ P 0)
    (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 ≤ r) :
    (pfRoot (transferBlock N (Real.sqrt (2 - 2 * d₀)) n) : ℂ) =
      BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 * d₀)) (p d₀)
        (⟨q - 1, by omega⟩ : Fin n) :=
  cor34_final_odd_all_parameters hd₀ hd₀₁ hd₁ hpAnalytic hp hBE hformula
    hPanalytic hP0 hNpos hbound hnpos hnq hN hr d₀ le_rfl

/-- Theorem 2.3 supplies a density-controlled Bethe state at `Δ₀`; Corollary 3.4 identifies its
real Bethe eigenvalue with the `r`-sector Perron root for every sufficiently large even `N`. -/
theorem cor34_final_exists_family_at_endpoint (r : ℕ) {d₀ : ℝ} (hd₀ : d₀ < -1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → Even N →
      let n := N / 2 - r
      ∃ hn : 0 < n, ∃ hs : 2 * n ≤ N, ∃ p : Fin n → ℝ,
        ∃ hp : p ∈ Bethe.S_n n,
        Bethe.DiscreteBetheEquation d₀ N n p ∧
        Bethe.densityNorm d₀ hd₀
          (fun x => Bethe.rootStepDensity N n p hp hn hs x - Bethe.rho d₀ x)
          (Bethe.rootStepDensity_error_bddAbove hd₀ _ hp hn hs) ≤ K / N ∧
        cor34BetheLambda N n (Real.sqrt (2 - 2 * d₀)) p =
          Lambda (Real.sqrt (2 - 2 * d₀)) N r := by
  obtain ⟨K, hK, N₀, hN₀, d₁, hd₀₁, hd₁, hfamily⟩ := Bethe.theorem23 r hd₀
  refine ⟨K, hK, N₀, hN₀, ?_⟩
  intro N hlarge hEvenN
  let n : ℕ := N / 2 - r
  obtain ⟨hn, hs, p, hp, hBE, hpAnalytic, hP, hDensity⟩ := hfamily N hlarge hEvenN
  obtain ⟨P, hPanalytic, hP0, hformula⟩ := hP
  let p₀ : Fin n → ℝ := p d₀
  have hp₀ : p₀ ∈ Bethe.S_n n := by
    exact hp d₀ le_rfl
  have hBE₀ : Bethe.DiscreteBetheEquation d₀ N n p₀ := hBE d₀ le_rfl
  have hDensity₀ :
      Bethe.densityNorm d₀ hd₀
        (fun x => Bethe.rootStepDensity N n p₀ hp₀ hn hs x - Bethe.rho d₀ x)
        (Bethe.rootStepDensity_error_bddAbove hd₀ _ hp₀ hn hs) ≤ K / N := by
    simpa [p₀] using hDensity d₀ le_rfl
  have hNindex : N / 2 - r = n := by rfl
  obtain ⟨m, hm⟩ := hEvenN
  have hNhalf : N = 2 * (N / 2) := by
    rw [hm]
    omega
  have hNform : N = 2 * (n + r) := by
    calc
      N = 2 * (N / 2) := hNhalf
      _ = 2 * ((N / 2 - r) + r) := by omega
      _ = 2 * (n + r) := by simp [n]
  have hNpos : 0 < N := by omega
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · have hCor := cor34_final_even_at_endpoint (N := N) (n := n) (r := r)
      (d₀ := d₀) (d₁ := d₁) (p := p) (P := P)
      hd₀ hd₀₁ hd₁ hpAnalytic hp hBE hformula hPanalytic hP0 hNpos hs hn
      hnEven hNform (Nat.zero_le r)
    have hc : 2 < Real.sqrt (2 - 2 * d₀) := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [hd₀]
    have hratio := Bethe.ratio_eigenvalueRegular hc hp₀
    have hroot : pfRoot (transferBlock N (Real.sqrt (2 - 2 * d₀)) n) =
        2 * ∏ j : Fin n,
          ‖BetheAnsatz.M (Real.sqrt (2 - 2 * d₀))
            (BetheAnsatz.z (p₀ j))‖ := by
      have h := congrArg Complex.re (hCor.trans hratio)
      simpa only [Complex.ofReal_re] using h
    have hindex : Lambda (Real.sqrt (2 - 2 * d₀)) N r =
        pfRoot (transferBlock N (Real.sqrt (2 - 2 * d₀)) n) := by
      unfold Lambda
      rw [hNindex]
    have hvalue : cor34BetheLambda N n (Real.sqrt (2 - 2 * d₀)) p₀ =
        2 * ∏ j : Fin n,
          ‖BetheAnsatz.M (Real.sqrt (2 - 2 * d₀))
            (BetheAnsatz.z (p₀ j))‖ := by
      simp [cor34BetheLambda, hnEven, p₀]
    refine ⟨hn, hs, p₀, hp₀, hBE₀, hDensity₀, ?_⟩
    exact hvalue.trans (hroot.symm.trans hindex.symm)
  · let q : ℕ := n / 2 + 1
    have hnotEven : ¬ Even n := Nat.not_even_iff_odd.mpr hnOdd
    obtain ⟨k, hk⟩ := hnOdd
    have hnq : n + 1 = 2 * q := by dsimp [q]; omega
    let l : Fin n := ⟨q - 1, by omega⟩
    have hCor := cor34_final_odd_at_endpoint (N := N) (n := n) (q := q) (r := r)
      (d₀ := d₀) (d₁ := d₁) (p := p) (P := P)
      hd₀ hd₀₁ hd₁ hpAnalytic hp hBE hformula hPanalytic hP0 hNpos hs hn
      hnq hNform (Nat.zero_le r)
    have hc : 2 < Real.sqrt (2 - 2 * d₀) := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [hd₀]
    have hcenter : p₀ l = 0 :=
      cor34_odd_S_n_center_zero hp₀ hnq
    have hratio := Bethe.ratio_eigenvalueZero (N := N) (n := n)
      hc hp₀ l hcenter
    have hroot : pfRoot (transferBlock N (Real.sqrt (2 - 2 * d₀)) n) =
        (2 + (Real.sqrt (2 - 2 * d₀)) ^ 2 * ((N : ℝ) - 1) +
          (Real.sqrt (2 - 2 * d₀)) ^ 2 *
            ∑ j ∈ Finset.univ.erase l,
              deriv (fun t => Bethe.theta
                (BetheAnsatz.anisotropy (Real.sqrt (2 - 2 * d₀))) t (p₀ j)) 0) *
          ∏ j ∈ Finset.univ.erase l,
            ‖BetheAnsatz.M (Real.sqrt (2 - 2 * d₀))
              (BetheAnsatz.z (p₀ j))‖ := by
      have h := congrArg Complex.re (hCor.trans hratio)
      simpa only [Complex.ofReal_re] using h
    have hindex : Lambda (Real.sqrt (2 - 2 * d₀)) N r =
        pfRoot (transferBlock N (Real.sqrt (2 - 2 * d₀)) n) := by
      unfold Lambda
      rw [hNindex]
    have hvalue : cor34BetheLambda N n (Real.sqrt (2 - 2 * d₀)) p₀ =
        (2 + (Real.sqrt (2 - 2 * d₀)) ^ 2 * ((N : ℝ) - 1) +
          (Real.sqrt (2 - 2 * d₀)) ^ 2 *
            ∑ j ∈ Finset.univ.erase l,
              deriv (fun t => Bethe.theta
                (BetheAnsatz.anisotropy (Real.sqrt (2 - 2 * d₀))) t (p₀ j)) 0) *
          ∏ j ∈ Finset.univ.erase l,
            ‖BetheAnsatz.M (Real.sqrt (2 - 2 * d₀))
              (BetheAnsatz.z (p₀ j))‖ := by
      simp [cor34BetheLambda, hnotEven, q, l, p₀]
    refine ⟨hn, hs, p₀, hp₀, hBE₀, hDensity₀, ?_⟩
    exact hvalue.trans (hroot.symm.trans hindex.symm)

end PottsDiscontinuity.SixVertex
