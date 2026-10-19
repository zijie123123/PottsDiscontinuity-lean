module

public import PottsDiscontinuity.Bethe.Theorem23Base
public import PottsDiscontinuity.Bethe.Theorem23Dominance
public import PottsDiscontinuity.Bethe.Theorem23GapInterior
public import PottsDiscontinuity.Bethe.Theorem23Local

/-! # All zeros in the compact Bethe region are interior and regular -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

theorem abs_compact_inverse_parameter_lt_one {Δ₀ ε : ℝ} (hΔ₀ : Δ₀ < -1)
    (hε : ε ∈ Icc (1 / Δ₀) 0) : |ε| < 1 := by
  have h0 := abs_lt.mp (abs_inverse_parameter_lt_one hΔ₀)
  exact abs_lt.mpr ⟨by linarith [hε.1], by linarith [hε.2]⟩

theorem inverse_parameter_le_cutoff {Δ₀ ε : ℝ} (_hΔ₀ : Δ₀ < -1)
    (hε : ε ∈ Icc (1 / Δ₀) 0) (hne : ε ≠ 0) : 1 / ε ≤ Δ₀ := by
  have hneg : ε < 0 := lt_of_le_of_ne hε.2 hne
  have h := one_div_le_one_div_of_neg_of_le hneg hε.1
  simpa only [one_div_one_div] using h

/-- Uniform compact-region data for the continuation theorem. Every zero in
the region is strictly interior and has invertible state derivative, including
the base parameter epsilon=0. -/
theorem exists_uniform_regular_Bethe_region (r : ℕ) {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ c D K : ℝ, 0 < c ∧ c ≤ Real.pi ∧
      8 * Real.pi * (2 * r + 1 : ℝ) < D ∧ 0 < K ∧
      ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (N k : ℕ), N₀ ≤ N → N = 2 * ((k + 1) + r) →
      ∀ hs : 2 * (k + 1) ≤ N,
      discreteBaseCoordinates N (k + 1) ∈ interior (betheGapRegion k (c / N) (D / N)) ∧
      (∀ ε ∈ Icc (1 / Δ₀) 0, ∀ q ∈ betheGapRegion k (c / N) (D / N),
        discreteCoordinateResidualInv ε N (k + 1) q = 0 →
        q ∈ interior (betheGapRegion k (c / N) (D / N)) ∧
        ∃ e : (Fin ((k + 1) / 2) → ℝ) ≃L[ℝ] (Fin ((k + 1) / 2) → ℝ),
          (fderiv ℝ (fun z : ℝ × (Fin ((k + 1) / 2) → ℝ) =>
            discreteCoordinateResidualInv z.1 N (k + 1) z.2) (ε, q)).comp
              (ContinuousLinearMap.inr ℝ ℝ (Fin ((k + 1) / 2) → ℝ)) =
            (e : (Fin ((k + 1) / 2) → ℝ) →L[ℝ] (Fin ((k + 1) / 2) → ℝ))) ∧
      (∀ (Δ : ℝ) (hΔ : Δ ≤ Δ₀) (q : Fin ((k + 1) / 2) → ℝ)
        (_hq : q ∈ betheGapRegion k (c / N) (D / N)),
        DiscreteBetheEquation Δ N (k + 1) (discreteSymLift (k + 1) q) →
        ∀ hp : discreteSymLift (k + 1) q ∈ S_n (k + 1),
        densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀)
          (fun x => rootStepDensity N (k + 1) (discreteSymLift (k + 1) q) hp (by omega) hs x - rho Δ x)
          (rootStepDensity_error_bddAbove (lt_of_le_of_lt hΔ hΔ₀) _ hp (by omega) hs) ≤ K / N) := by
  obtain ⟨c, D, K, hc, hcpi, hDlarge, hK, M₀, hM₀, hbootstrap⟩ :=
    exists_uniform_strict_gap_bootstrap r hΔ₀
  have hD : 0 < D := lt_trans (by positivity) hDlarge
  obtain ⟨L₀, hL₀, hmatrix⟩ := exists_uniform_Bethe_matrix_nonsingular hΔ₀ D hD.le
  refine ⟨c, D, K, hc, hcpi, hDlarge, hK, max M₀ L₀,
    lt_of_lt_of_le hM₀ (le_max_left _ _), fun N k hlarge hcount hs => ?_⟩
  have hMlarge : M₀ ≤ N := (le_max_left _ _).trans hlarge
  have hLlarge : L₀ ≤ N := (le_max_right _ _).trans hlarge
  have hN : 0 < N := lt_of_lt_of_le hM₀ hMlarge
  have hNc : (0 : ℝ) < N := by exact_mod_cast hN
  have hbase : discreteBaseCoordinates N (k + 1) ∈ interior (betheGapRegion k (c / N) (D / N)) :=
    mem_interior_betheGapRegion (discreteBaseCoordinates_strict_gaps hN hs hcount hcpi hDlarge)
  refine ⟨hbase, ?_, ?_⟩
  · intro ε hε q hq hzero
    by_cases hεzero : ε = 0
    · subst ε
      have hqbase : q = discreteBaseCoordinates N (k + 1) :=
        (discreteCoordinateResidualInv_base_unique hN hs).unique hzero
          (discreteCoordinateResidualInv_base_zero hN hs)
      refine ⟨hqbase ▸ hbase, ?_⟩
      exact exists_discreteCoordinateResidualInv_stateEquiv_zero hN hs q
    · let Δ := 1 / ε
      have hΔ : Δ ≤ Δ₀ := inverse_parameter_le_cutoff hΔ₀ hε hεzero
      have hvalid : Δ < -1 := lt_of_le_of_lt hΔ hΔ₀
      have hInv : 1 / Δ = ε := one_div_one_div ε
      have hp : discreteSymLift (k + 1) q ∈ S_n (k + 1) :=
        betheGapRegion_mem_S_n (div_pos hc hNc) hq
      have hfinite : discreteCoordinateResidual Δ N (k + 1) q = 0 := by
        rw [← discreteCoordinateResidualInv_eq hvalid, hInv]
        exact hzero
      have hBE := (discreteCoordinateResidual_zero_iff hN q).1 hfinite
      have hmesh := fun j => (hq j).2
      have hstrict := (hbootstrap Δ hΔ N k hMlarge hcount _ hp hs hBE hmesh).2
      have hdet := hmatrix Δ hΔ N k hLlarge hs _ hp hBE hmesh
      obtain ⟨e, he⟩ := exists_discreteCoordinateResidual_stateEquiv hvalid N (k + 1) q hdet
      refine ⟨mem_interior_betheGapRegion hstrict, e, ?_⟩
      rw [← hInv, discreteCoordinateResidualInv_stateDerivative hvalid,
        ← discreteCoordinateResidual_stateDerivative hvalid]
      exact he
  · intro Δ hΔ q hq hBE hp
    exact (hbootstrap Δ hΔ N k hMlarge hcount _ hp hs hBE (fun j => (hq j).2)).1

end PottsDiscontinuity.Bethe
