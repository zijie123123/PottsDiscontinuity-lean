module

public import PottsDiscontinuity.Bethe.Asymptotic26Cast
public import PottsDiscontinuity.Bethe.Asymptotic29Control
public import PottsDiscontinuity.Bethe.AsymptoticGeometry
public import PottsDiscontinuity.Bethe.AsymptoticUniformConvergence

/-! # Theorem 2.9 for `N ∈ 4ℕ`

The families are indexed by a sequence of sizes tending to infinity. The
positive root-count premises express the source's “sufficiently large N”.
The two weighted `O(1/N)` assumptions use one eventual nonnegative constant;
separate constants can always be replaced by their maximum.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

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

include hΔ hN hp hq hpBE hqBE hNlim hbp hbq hK hrate

/-- **Theorem 2.9, item 1.** Uniform convergence on the closed interval to
the continuous representative of the offset-equation solution. -/
theorem theorem29_convergence :
    TendstoUniformlyOn (fun i x => rho Δ x * offsetFunction (N i) r (h4 i) (hr i) (p i) (q i) (hn i) x)
      (fun x => (r : ℝ) * tauCont Δ x) atTop (Icc (-Real.pi) Real.pi) := by
  let w := Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1)
  have hw : 0 < w := density_weight_lower_pos hΔ
  have herror : ∀ᶠ i in atTop, ∀ x ∈ Icc (-Real.pi) Real.pi,
      |rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) x - rho Δ x| ≤
        (K / w) / N i ∧
      |rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i) x - rho Δ x| ≤
        (K / w) / N i := by
    filter_upwards [hrate] with i hi x hx
    constructor
    · calc
        _ ≤ densityNorm Δ hΔ (fun y => rootStepDensity (N i) (N i / 2) (p i) (hp i)
            (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) y - rho Δ y) (hbp i) / w :=
          abs_le_densityNorm_div hΔ _ (hbp i) hx
        _ ≤ (K / (N i : ℝ)) / w := div_le_div_of_nonneg_right hi.1 hw.le
        _ = (K / w) / (N i : ℝ) := by ring
    · calc
        _ ≤ densityNorm Δ hΔ (fun y => rootStepDensity (N i) (N i / 2 - r) (q i) (hq i)
            (hn i) (two_mul_half_sub_le N r i) y - rho Δ y) (hbq i) / w :=
          abs_le_densityNorm_div hΔ _ (hbq i) hx
        _ ≤ (K / (N i : ℝ)) / w := div_le_div_of_nonneg_right hi.2 hw.le
        _ = (K / w) / (N i : ℝ) := by ring
  obtain ⟨B, R, DP, DQ, hB, hR, hDP, hDQ, L, hgeom⟩ :=
    eventually_offset_estimates_of_density_rate hΔ r N h4 hr hN hn p q hp hq hNlim
      (div_nonneg hK hw.le) herror
  have hKlim : Tendsto (fun i => K / (N i : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hNlim).const_mul K
  have hnormlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i) x - rho Δ x)
      (hbq i)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hrate, hKlim.eventually (gt_mem_nhds hε)] with i hi hKi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (densityNorm_nonneg hΔ _ (hbq i))]
    exact hi.2.trans_lt hKi
  have hcount (i : ℕ) : N i = 2 * (N i / 2 - r + r) := by
    obtain ⟨z, hz⟩ := h4 i
    have := hr i
    omega
  have hweak (g : ℝ → ℝ) (hg : Continuous g) :
      Tendsto (fun i => (∑ j, g (q i j)) / (N i : ℝ)) atTop
        (𝓝 (∫ y in (-Real.pi)..Real.pi, g y * rho Δ y)) :=
    theorem26_sums_of_pos hΔ r N (fun i => N i / 2 - r) q hq hn (fun i => by omega)
      hcount hNlim hbq hnormlim g hg
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp hgeom
  let t : ℕ → ℕ := fun i => i₀ + i
  have ht : Tendsto t atTop atTop := tendsto_atTop.mpr (fun a =>
    eventually_atTop.mpr ⟨a, fun b hb => by dsimp [t]; omega⟩)
  have hgt (i : ℕ) : OffsetEstimatesAt (N (t i)) r (h4 (t i)) (hr (t i)) (hn (t i))
      (p (t i)) (q (t i)) B R DP DQ L := hi₀ (t i) (by dsimp [t]; omega)
  have htail := offset_uniform_convergence_of_geometry hΔ r (fun i => N (t i))
    (fun i => h4 (t i)) (fun i => hr (t i)) (fun i => hN (t i)) (fun i => hn (t i))
    (fun i => p (t i)) (fun i => q (t i)) (fun i => hp (t i)) (fun i => hq (t i))
    (fun i => hpBE (t i)) (fun i => hqBE (t i)) (hNlim.comp ht)
    B R DP DQ hR hDP L (fun i => (hgt i).bound) (fun i => (hgt i).pair)
    (fun i => (hgt i).near) (fun i => (hgt i).meshP) (fun i => (hgt i).meshQ)
    (fun g hg => (hweak g hg).comp ht)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp htail ε hε)
  apply eventually_atTop.mpr
  refine ⟨i₀ + j₀, ?_⟩
  intro i hi x hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show i₀ ≤ i by omega)
  exact hj₀ k (by omega) x hx

/-- **Theorem 2.9**, both conclusions, for `N ∈ 4ℕ`. -/
theorem theorem29 :
    TendstoUniformlyOn (fun i x => rho Δ x * offsetFunction (N i) r (h4 i) (hr i) (p i) (q i) (hn i) x)
      (fun x => (r : ℝ) * tauCont Δ x) atTop (Icc (-Real.pi) Real.pi) ∧
    ∃ C > 0, ∃ D ≥ 0, ∀ᶠ i in atTop, ∀ x ∈ Icc (-Real.pi) Real.pi,
      |offsetFunction (N i) r (h4 i) (hr i) (p i) (q i) (hn i) x| ≤ C * |x| + D / N i := by
  exact ⟨theorem29_convergence hΔ r N h4 hr hN hn p q hp hq hpBE hqBE hNlim hbp hbq hK hrate,
    theorem29_control hΔ r N h4 hr hN hn p q hp hq hNlim hbp hbq hK hrate⟩

end

end PottsDiscontinuity.Bethe
