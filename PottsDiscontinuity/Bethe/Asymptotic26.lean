module

public import PottsDiscontinuity.Bethe.AsymptoticQuadrature

/-! # Theorem 2.6: convergence of the empirical integrals

The positive root count is written `k i + 1`; the count identity
`N i = 2 * (k i + 1 + r)` is precisely `n=N/2-r`.  The index filter is
arbitrary, so the statement applies in particular to `N ∈ 4ℕ` tending to
infinity. No discrete Bethe equation and no rate of density convergence are
assumed.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

theorem integral_empiricalMeasure (N : ℕ) (hN : 0 < N) (n : ℕ)
    (p : Fin n → ℝ) (g : ℝ → ℝ) :
    (∫ x, g x ∂empiricalMeasure N hN n p) = (∑ j, g (p j)) / (N : ℝ) := by
  unfold empiricalMeasure
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
      div_eq_mul_inv, mul_comm]
  · intro j _
    exact integrable_dirac (by simp)

/-- The test-function form of Theorem 2.6, for the actual empirical measures.
The finite error estimate treats the two boundary tails separately. -/
theorem theorem26_integrals {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (r : ℕ) (N k : ι → ℕ) (p : ∀ i, Fin (k i + 1) → ℝ)
    (hp : ∀ i, p i ∈ S_n (k i + 1)) (hs : ∀ i, 2 * (k i + 1) ≤ N i)
    (hcount : ∀ i, N i = 2 * (k i + 1 + r))
    (hNlim : Tendsto (fun i => (N i : ℝ)) l atTop)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i) x - rho Δ x)
      (hb i)) l (𝓝 0))
    (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun i => ∫ x, g x ∂empiricalMeasure (N i)
      (by have := hs i; omega) (k i + 1) (p i)) l
      (𝓝 (∫ x in (-Real.pi)..Real.pi, g x * rho Δ x)) := by
  have hNpos (i : ι) : 0 < N i := by have := hs i; omega
  have hNreal (i : ι) : (0 : ℝ) < N i := by exact_mod_cast hNpos i
  let E : ι → ℝ := fun i => densityNorm Δ hΔ
    (fun x => rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i) x - rho Δ x)
    (hb i) / (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1))
  have hE : Tendsto E l (𝓝 0) :=
    tendsto_densityNorm_div hΔ
      (fun i x => rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i) x - rho Δ x)
      hb hlim
  have hEnonneg (i : ι) : 0 ≤ E i :=
    div_nonneg (densityNorm_nonneg hΔ _ (hb i)) (density_weight_lower_pos hΔ).le
  have herror (i : ι) (x : ℝ) (hx : x ∈ Icc (-Real.pi) Real.pi) :
      |rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i) x - rho Δ x| ≤ E i :=
    abs_le_densityNorm_div hΔ
      (fun x => rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i) x - rho Δ x)
      (hb i) hx
  obtain ⟨m, hm, hmesh⟩ := eventually_rootPartition_gap_le hΔ r N (fun i => k i + 1) p hp
    (fun i => by omega) hs hcount hb hlim
  let d : ι → ℝ := fun i => 2 * (2 * r + 1 : ℝ) / (m * (N i : ℝ))
  have hinv : Tendsto (fun i => (N i : ℝ)⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp hNlim
  have hd : Tendsto d l (𝓝 0) := by
    have ht := hinv.const_mul (2 * (2 * r + 1 : ℝ) / m)
    simpa only [mul_zero, d, div_mul_eq_div_mul_one_div, one_div] using ht
  have hdnonneg (i : ι) : 0 ≤ d i := by dsimp [d]; positivity
  obtain ⟨G₀, hG₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuous_rho hΔ).continuousOn
  let G := max G₀ 1
  let M := max M₀ 1
  have hGpos : 0 < G := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hgBound : ∀ x ∈ Icc (-Real.pi) Real.pi, |g x| ≤ G := by
    intro x hx
    exact (show |g x| ≤ G₀ by simpa only [Real.norm_eq_abs] using hG₀ x hx).trans (le_max_left _ _)
  have hρBound : ∀ x ∈ Icc (-Real.pi) Real.pi, |rho Δ x| ≤ M := by
    intro x hx
    exact (show |rho Δ x| ≤ M₀ by simpa only [Real.norm_eq_abs] using hM₀ x hx).trans (le_max_left _ _)
  let B : ι → ℝ := fun i => 2 * Real.pi * G * E i + 2 * G * M * d i + G * (N i : ℝ)⁻¹
  have hB : Tendsto B l (𝓝 0) := by
    have ht := ((hE.const_mul (2 * Real.pi * G)).add (hd.const_mul (2 * G * M))).add
      (hinv.const_mul G)
    simpa only [mul_zero, add_zero] using ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let w : ℝ := ε / (4 * Real.pi * M)
  have hwpos : 0 < w := by dsimp [w]; positivity
  have hwid : 2 * Real.pi * (w * M) = ε / 2 := by
    dsimp [w]
    field_simp [hMpos.ne', Real.pi_ne_zero]
    ring
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn) w hwpos
  filter_upwards [hmesh, hd.eventually (gt_mem_nhds hδ),
    hB.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))] with i hmi hdi hBi
  rw [Real.dist_eq, integral_empiricalMeasure, abs_sub_comm]
  have hquad := root_quadrature_error (hp i) (hs i) hΔ hg hGpos.le hMpos.le (hEnonneg i)
    hwpos.le hgBound hρBound (herror i) hmi
    (fun x hx y hy hxy => by
      apply hmod x hx y hy
      rw [Real.dist_eq]
      exact hxy.trans hdi.le)
  apply hquad.trans_lt
  have hidentity : 2 * Real.pi * (w * M + G * E i) + 2 * G * M * d i + G / (N i : ℝ) =
      ε / 2 + B i := by
    rw [mul_add, hwid]
    dsimp [B]
    rw [div_eq_mul_inv]
    ring
  rw [hidentity]
  linarith

/-- The empirical measure regarded as an element of the space of finite
measures with its weak topology. -/
noncomputable def empiricalFiniteMeasure (N : ℕ) (hN : 0 < N) (n : ℕ)
    (p : Fin n → ℝ) : FiniteMeasure ℝ :=
  ⟨empiricalMeasure N hN n p, by
    unfold empiricalMeasure
    apply Measure.smul_finite
    simp only [ne_eq, ENNReal.inv_eq_top, Nat.cast_eq_zero]
    exact Nat.ne_of_gt hN⟩

/-- The finite measure `ρ(x) dx` on `[-π,π]`, extended by zero outside it. -/
noncomputable def rhoFiniteMeasure (Δ : ℝ) (hΔ : Δ < -1) : FiniteMeasure ℝ :=
  ⟨(volume.restrict (Icc (-Real.pi) Real.pi)).withDensity (fun x => ENNReal.ofReal (rho Δ x)), by
    have hi : Integrable (rho Δ) (volume.restrict (Icc (-Real.pi) Real.pi)) :=
      integrableOn_Icc_of_continuous (continuous_rho hΔ)
    apply isFiniteMeasure_withDensity
    exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (rho_pos hΔ x).le)).mpr hi⟩

theorem integral_rhoFiniteMeasure {Δ : ℝ} (hΔ : Δ < -1) (g : ℝ → ℝ) :
    (∫ x, g x ∂(rhoFiniteMeasure Δ hΔ : Measure ℝ)) =
      ∫ x in (-Real.pi)..Real.pi, g x * rho Δ x := by
  change (∫ x, g x ∂(volume.restrict (Icc (-Real.pi) Real.pi)).withDensity
    (fun x => ENNReal.ofReal (rho Δ x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_rho hΔ).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) g]
  simp_rw [ENNReal.toReal_ofReal (rho_pos hΔ _).le, smul_eq_mul]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ← integral_Icc_eq_integral_Ioc]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- **Theorem 2.6.** Weak convergence of the empirical finite measures under
weighted norm convergence alone. The general filter formulation includes
the downstream subsequence `N ∈ 4ℕ`. -/
theorem theorem26 {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (r : ℕ) (N k : ι → ℕ) (p : ∀ i, Fin (k i + 1) → ℝ)
    (hp : ∀ i, p i ∈ S_n (k i + 1)) (hs : ∀ i, 2 * (k i + 1) ≤ N i)
    (hcount : ∀ i, N i = 2 * (k i + 1 + r))
    (hNlim : Tendsto (fun i => (N i : ℝ)) l atTop)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i) x - rho Δ x)
      (hb i)) l (𝓝 0)) :
    Tendsto (fun i => empiricalFiniteMeasure (N i) (by have := hs i; omega)
      (k i + 1) (p i)) l (𝓝 (rhoFiniteMeasure Δ hΔ)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  change Tendsto (fun i => ∫ x, g x ∂empiricalMeasure (N i) (by have := hs i; omega) (k i + 1) (p i)) l
    (𝓝 (∫ x, g x ∂(rhoFiniteMeasure Δ hΔ : Measure ℝ)))
  rw [integral_rhoFiniteMeasure hΔ]
  exact theorem26_integrals hΔ r N k p hp hs hcount hNlim hb hlim g g.continuous

end PottsDiscontinuity.Bethe
