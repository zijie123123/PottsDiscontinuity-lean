module

public import PottsDiscontinuity.Bethe.AsymptoticNorm

/-! # Density consequences used in the source-family specialization -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

theorem ratio_densityNorm_tendsto_of_rate {ι : Type*} {l : Filter ι} {Δ K : ℝ}
    (hΔ : Δ < -1) (N : ι → ℕ) (hN : Tendsto (fun i => (N i : ℝ)) l atTop)
    (f : ι → ℝ → ℝ)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f i (kMap (lamOf Δ) α)|))
    (hrate : ∀ᶠ i in l, densityNorm Δ hΔ (f i) (hb i) ≤ K / N i) :
    Tendsto (fun i => densityNorm Δ hΔ (f i) (hb i)) l (𝓝 0) := by
  have hKlim : Tendsto (fun i => K / (N i : ℝ)) l (𝓝 0) := tendsto_const_nhds.div_atTop hN
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hrate, hKlim.eventually (gt_mem_nhds hε)] with i hi hKi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (densityNorm_nonneg hΔ _ (hb i))]
  exact hi.trans_lt hKi

theorem ratio_density_tendsto {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (f : ι → ℝ → ℝ)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (f i (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ (fun x => f i x - rho Δ x) (hb i)) l (𝓝 0))
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    Tendsto (fun i => f i x) l (𝓝 (rho Δ x)) := by
  have he := tendsto_densityNorm_div hΔ (fun i x => f i x - rho Δ x) hb hlim
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with i hi
  rw [Real.dist_eq]
  exact (abs_le_densityNorm_div hΔ (fun x => f i x - rho Δ x) (hb i) hx).trans_lt hi

theorem ratio_density_eventually_bounded {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (f : ι → ℝ → ℝ)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (f i (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ (fun x => f i x - rho Δ x) (hb i)) l (𝓝 0)) :
    ∃ M ≥ 0, ∀ᶠ i in l, ∀ x ∈ Icc (-Real.pi) Real.pi, f i x ≤ M := by
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuous_rho hΔ).continuousOn
  let M := max M₀ 1 + 1
  have hM : 0 ≤ M := by dsimp [M]; linarith [le_max_right M₀ 1]
  refine ⟨M, hM, ?_⟩
  have he := tendsto_densityNorm_div hΔ (fun i x => f i x - rho Δ x) hb hlim
  filter_upwards [he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with i hi x hx
  have herror := (abs_le.mp (abs_le_densityNorm_div hΔ (fun x => f i x - rho Δ x) (hb i) hx)).2
  have hρ : rho Δ x ≤ M₀ := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM₀ x hx)
  dsimp [M]
  linarith [le_max_left M₀ 1]

/-- The weighted rate gives the unweighted rate used by the geometric lemmas. -/
theorem ratio_density_error_of_rate {ι : Type*} {l : Filter ι} {Δ K : ℝ} (hΔ : Δ < -1)
    (N : ι → ℕ) (f : ι → ℝ → ℝ)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (f i (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hrate : ∀ᶠ i in l, densityNorm Δ hΔ (fun x => f i x - rho Δ x) (hb i) ≤ K / N i) :
    ∀ᶠ i in l, ∀ x ∈ Icc (-Real.pi) Real.pi,
      |f i x - rho Δ x| ≤
        (K / (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1))) / N i := by
  have hw := (density_weight_lower_pos hΔ).le
  filter_upwards [hrate] with i hi x hx
  calc
    _ ≤ densityNorm Δ hΔ (fun x => f i x - rho Δ x) (hb i) /
        (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1)) :=
      abs_le_densityNorm_div hΔ (fun x => f i x - rho Δ x) (hb i) hx
    _ ≤ (K / (N i : ℝ)) / (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1)) :=
      div_le_div_of_nonneg_right hi hw
    _ = _ := by ring

end PottsDiscontinuity.Bethe
