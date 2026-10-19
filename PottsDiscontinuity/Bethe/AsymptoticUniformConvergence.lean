module

public import PottsDiscontinuity.Bethe.AsymptoticCompactness
public import PottsDiscontinuity.Bethe.AsymptoticSubsequenceLimit

/-! # Compactness and uniqueness imply convergence of the whole family -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators UniformConvergence

namespace PottsDiscontinuity.Bethe

theorem offset_uniform_convergence_of_geometry {Δ : ℝ} (hΔ : Δ < -1)
    (r : ℕ) (N : ℕ → ℕ) (h4 : ∀ i, 4 ∣ N i) (hr : ∀ i, r ≤ N i / 2)
    (hN : ∀ i, 0 < N i) (hn : ∀ i, 0 < N i / 2 - r)
    (p : ∀ i, Fin (N i / 2) → ℝ) (q : ∀ i, Fin (N i / 2 - r) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (hq : ∀ i, q i ∈ S_n (N i / 2 - r))
    (hpBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2) (p i))
    (hqBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2 - r) (q i))
    (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    (B R DP DQ : ℝ) (hR : 0 ≤ R) (hDP : 0 ≤ DP) (K : NNReal)
    (hbound : ∀ i j, |offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i) j| ≤ B)
    (hpair : ∀ i j k,
      |offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i) j -
        offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i) k| ≤ (K : ℝ) * |q i j - q i k|)
    (hnear : ∀ i j, |offsetLowerRoot (N i) r (hr i) (p i) j - q i j| ≤ R / N i ∧
      |offsetUpperRoot (N i) r (hr i) (p i) j - q i j| ≤ R / N i)
    (hmeshP : ∀ i, ∀ j : Fin (N i / 2 + 1),
      rootPartitionPoint (N i / 2) (p i) (by have := hn i; omega) j.succ -
        rootPartitionPoint (N i / 2) (p i) (by have := hn i; omega) j.castSucc ≤ DP / N i)
    (hmeshQ : ∀ i, ∀ j : Fin (N i / 2 - r + 1),
      rootPartitionPoint (N i / 2 - r) (q i) (hn i) j.succ -
        rootPartitionPoint (N i / 2 - r) (q i) (hn i) j.castSucc ≤ DQ / N i)
    (hweak : ∀ g : ℝ → ℝ, Continuous g →
      Tendsto (fun i => (∑ j, g (q i j)) / (N i : ℝ)) atTop
        (𝓝 (∫ y in (-Real.pi)..Real.pi, g y * rho Δ y))) :
    TendstoUniformlyOn (fun i x => rho Δ x * offsetFunction (N i) r (h4 i) (hr i) (p i) (q i) (hn i) x)
      (fun x => (r : ℝ) * tauCont Δ x) atTop (Icc (-Real.pi) Real.pi) := by
  let X := Icc (-Real.pi) Real.pi
  let U : ℕ → X →ᵤ ℝ := fun i => UniformFun.ofFun
    (fun x => rho Δ x * offsetFunction (N i) r (h4 i) (hr i) (p i) (q i) (hn i) x)
  let V : X →ᵤ ℝ := UniformFun.ofFun (fun x => (r : ℝ) * tauCont Δ x)
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  change TendstoUniformly (UniformFun.toFun ∘ U) (UniformFun.toFun V) atTop
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hNns : Tendsto (fun i => (N (ns i) : ℝ)) atTop atTop := hNlim.comp hns
  have hinv : Tendsto (fun i => (N (ns i) : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hNns
  have hdQ : Tendsto (fun i => DQ / (N (ns i) : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul DQ
  obtain ⟨f, hf, φ, hφ, hF⟩ := exists_offset_subseq_of_geometry r (fun i => N (ns i))
    (fun i => h4 (ns i)) (fun i => hr (ns i)) (fun i => hn (ns i))
    (fun i => p (ns i)) (fun i => q (ns i)) (fun i => hq (ns i)) K B
    (fun i => hbound (ns i)) (fun i => hpair (ns i))
    (fun i => DQ / (N (ns i) : ℝ)) hdQ (fun i => hmeshQ (ns i))
  let t : ℕ → ℕ := ns ∘ φ
  have ht : Tendsto t atTop atTop := hns.comp hφ.tendsto_atTop
  have hNt : Tendsto (fun i => (N (t i) : ℝ)) atTop atTop := hNlim.comp ht
  have hinvt : Tendsto (fun i => (N (t i) : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hNt
  have hdPt : Tendsto (fun i => DP / (N (t i) : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinvt.const_mul DP
  have hdQt : Tendsto (fun i => DQ / (N (t i) : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinvt.const_mul DQ
  have hweakt (g : ℝ → ℝ) (hg : Continuous g) :
      Tendsto (fun i => (∑ j, g (q (t i) j)) / (N (t i) : ℝ)) atTop
        (𝓝 (∫ y in (-Real.pi)..Real.pi, g y * rho Δ y)) := (hweak g hg).comp ht
  have hid := offset_uniform_limit_identification hΔ r (fun i => N (t i))
    (fun i => h4 (t i)) (fun i => hr (t i)) (fun i => hN (t i)) (fun i => hn (t i))
    (fun i => p (t i)) (fun i => q (t i)) (fun i => hp (t i)) (fun i => hq (t i))
    (fun i => hpBE (t i)) (fun i => hqBE (t i)) hNt B R hR
    (fun i => hbound (t i)) (fun i => hnear (t i))
    (fun i => DP / (N (t i) : ℝ)) (fun i => DQ / (N (t i) : ℝ)) hdPt hdQt
    (fun i => div_nonneg hDP (Nat.cast_nonneg _))
    (fun i => hmeshP (t i)) (fun i => hmeshQ (t i)) hweakt hf hF
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuous_rho hΔ).continuousOn
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  have hρ : TendstoUniformlyOn (fun _i : ℕ => rho Δ) (rho Δ) atTop X := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall (fun i x hx => by simpa using hε)
  have hprod := tendstoUniformlyOn_mul_of_bounds hρ hF
    (show 0 ≤ max M₀ 1 by linarith [le_max_right M₀ 1])
    (show 0 ≤ max C₀ 1 by linarith [le_max_right C₀ 1])
    (fun i x hx => (show |rho Δ x| ≤ M₀ by simpa only [Real.norm_eq_abs] using hM₀ x hx).trans (le_max_left _ _))
    (fun x hx => (show |f x| ≤ C₀ by simpa only [Real.norm_eq_abs] using hC₀ x hx).trans (le_max_left _ _))
  have hfinal := hprod.congr_right hid
  refine ⟨φ, ?_⟩
  apply UniformFun.tendsto_iff_tendstoUniformly.mpr
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hfinal

end PottsDiscontinuity.Bethe
