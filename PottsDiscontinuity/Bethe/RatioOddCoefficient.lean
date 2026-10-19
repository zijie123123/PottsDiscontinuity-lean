module

public import PottsDiscontinuity.Bethe.Asymptotic26Cast
public import PottsDiscontinuity.Bethe.AsymptoticLimitTools
public import PottsDiscontinuity.Bethe.RatioProducts

/-! # The zero-root prefactor: positivity and its leading asymptotic

Source: Section 3.2 of arXiv:1611.09877v2, proof of (1.7) for odd `r`: the prefactor (A) of
`Λ_r(N) / Λ₀(N)` and its asymptotic `(A) = (c²/2) · 2πρ(0) N + o(N)`. The continuous derivative
test is nonsingular, so
Theorem 2.6 suffices; the offset theorem is not needed for this factor.
-/

@[expose] public section

open Set Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

/-- The full real coefficient of the erased product in the zero-root formula. -/
noncomputable def ratioZeroCoefficient {n : ℕ} (Δ c : ℝ) (N : ℕ)
    (q : Fin n → ℝ) (l : Fin n) : ℝ :=
  2 + c ^ 2 * ((N : ℝ) - 1) + c ^ 2 * ∑ j ∈ univ.erase l, d1Theta Δ 0 (q j)

theorem ratio_eigenvalueZero_eq_coefficient {N n : ℕ} {q : Fin n → ℝ}
    {c : ℝ} (hc : 2 < c) (hq : q ∈ S_n n) (l : Fin n) (hl : q l = 0) :
    BetheAnsatz.eigenvalueZero N c q l =
      ((ratioZeroCoefficient (BetheAnsatz.anisotropy c) c N q l *
        ∏ j ∈ univ.erase l, ‖BetheAnsatz.M c (BetheAnsatz.z (q j))‖ : ℝ) : ℂ) := by
  exact ratio_eigenvalueZero hc hq l hl

/-- Exact source `(A)(B)` factorization, before any asymptotics. -/
theorem ratio_odd_eigenvalue_quotient {N m n : ℕ}
    {p : Fin m → ℝ} {q : Fin n → ℝ} {c : ℝ} (hc : 2 < c)
    (hp : p ∈ S_n m) (hq : q ∈ S_n n) (l : Fin n) (hl : q l = 0) :
    BetheAnsatz.eigenvalueZero N c q l / BetheAnsatz.eigenvalueRegular c p =
      (((ratioZeroCoefficient (BetheAnsatz.anisotropy c) c N q l / 2) *
        ((∏ j ∈ univ.erase l, ‖BetheAnsatz.M c (BetheAnsatz.z (q j))‖) /
          ∏ j, ‖BetheAnsatz.M c (BetheAnsatz.z (p j))‖) : ℝ) : ℂ) := by
  rw [ratio_eigenvalueZero_eq_coefficient hc hq l hl, ratio_eigenvalueRegular hc hp]
  push_cast
  ring

/-- `(A)/N → c²πρ(0)`, under the root-density convergence premises of Theorem 2.6.
The erased root is exactly zero, so its single derivative term is `O(1/N)`.
-/
theorem ratio_odd_A_tendsto {ι : Type*} {f : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (c : ℝ) (r : ℕ) (N n : ι → ℕ) (q : ∀ i, Fin (n i) → ℝ)
    (hq : ∀ i, q i ∈ S_n (n i)) (hn : ∀ i, 0 < n i) (hs : ∀ i, 2 * n i ≤ N i)
    (hcount : ∀ i, N i = 2 * (n i + r))
    (hNlim : Tendsto (fun i => (N i : ℝ)) f atTop)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (n i) (q i) (hq i) (hn i) (hs i) x - rho Δ x) (hb i)) f (𝓝 0))
    (l : ∀ i, Fin (n i)) (hl : ∀ i, q i (l i) = 0) :
    Tendsto (fun i => ratioZeroCoefficient Δ c (N i) (q i) (l i) / (2 * N i)) f
      (𝓝 (c ^ 2 * Real.pi * rho Δ 0)) := by
  have hg : Continuous (d1Theta Δ 0) :=
    (continuous_d1Theta_pair hΔ).comp (continuous_const.prodMk continuous_id)
  have hweak := theorem26_sums_of_pos hΔ r N n q hq hn hs hcount hNlim (hb) hlim
    (d1Theta Δ 0) hg
  have hinv : Tendsto (fun i => (N i : ℝ)⁻¹) f (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hNlim
  have hcb := rho_isCBESolution hΔ 0
    (show (0 : ℝ) ∈ Icc (-Real.pi) Real.pi from
      ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩)
  change 2 * Real.pi * rho Δ 0 = 1 +
    ∫ x in (-Real.pi)..Real.pi, d1Theta Δ 0 x * rho Δ x at hcb
  have ht := (((tendsto_const_nhds (x := (1 : ℝ))).add hweak).const_mul (c ^ 2 / 2)).add
    (hinv.const_mul ((2 - c ^ 2 - c ^ 2 * d1Theta Δ 0 0) / 2))
  have htarget : c ^ 2 / 2 * (1 +
      ∫ x in (-Real.pi)..Real.pi, d1Theta Δ 0 x * rho Δ x) +
      ((2 - c ^ 2 - c ^ 2 * d1Theta Δ 0 0) / 2) * 0 = c ^ 2 * Real.pi * rho Δ 0 := by
    rw [← hcb]
    ring
  rw [htarget] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun i => by
    have hN : (N i : ℝ) ≠ 0 := by exact_mod_cast (show N i ≠ 0 by have := hn i; have := hs i; omega)
    have he := sum_erase_add (s := (univ : Finset (Fin (n i))))
      (fun j => d1Theta Δ 0 (q i j)) (mem_univ (l i))
    rw [hl i] at he
    unfold ratioZeroCoefficient
    field_simp
    nlinarith only [he])

end PottsDiscontinuity.Bethe
