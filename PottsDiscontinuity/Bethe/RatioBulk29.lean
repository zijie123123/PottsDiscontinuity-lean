module

public import PottsDiscontinuity.Bethe.Asymptotic29
public import PottsDiscontinuity.Bethe.RatioBulkLimit
public import PottsDiscontinuity.Bethe.RatioDensityLimits
public import PottsDiscontinuity.Bethe.RatioOffsetProjection
public import PottsDiscontinuity.Bethe.RatioProducts
public import PottsDiscontinuity.Bethe.RatioTruncation

/-! # The source bulk log-product limit under the exact Theorem 2.9 premises -/

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


include hΔ h4 hN hp hq hpBE hqBE hNlim hbp hbq hK hrate

/-- The logarithm of the source bulk factor, for both parity clauses of
the aligned roots. All density/Bethe premises are exactly those of Theorem 2.9. -/
theorem ratio_bulk_log_limit {c : ℝ} (hc : 2 < c) :
    Tendsto (fun i => ∑ j, (ratioEll c (q i j) -
      ratioEll c (alignedRoot (N i) r (hr i) (p i) j))) atTop
      (𝓝 ((r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x)) := by
  let Pρ : ℕ → ℝ → ℝ := fun i =>
    rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i)
  let Qρ : ℕ → ℝ → ℝ := fun i =>
    rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i)
  have hrP := hrate.mono (fun i hi => hi.1)
  have hrQ := hrate.mono (fun i hi => hi.2)
  have hnormQ : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => Qρ i x - rho Δ x) (hbq i)) atTop (𝓝 0) :=
    ratio_densityNorm_tendsto_of_rate hΔ N hNlim (fun i x => Qρ i x - rho Δ x) hbq hrQ
  have heP := ratio_density_error_of_rate hΔ N Pρ hbp hrP
  have heQ := ratio_density_error_of_rate hΔ N Qρ hbq hrQ
  let E₀ := K / (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1))
  have hE₀ : 0 ≤ E₀ := div_nonneg hK (density_weight_lower_pos hΔ).le
  have herror : ∀ᶠ i in atTop, ∀ x ∈ Icc (-Real.pi) Real.pi,
      |Pρ i x - rho Δ x| ≤ E₀ / N i ∧ |Qρ i x - rho Δ x| ≤ E₀ / N i := by
    filter_upwards [heP, heQ] with i hiP hiQ x hx
    exact ⟨hiP x hx, hiQ x hx⟩
  obtain ⟨B, R, DP, DQ, _hB, _hR, _hDP, hDQ, G, hgeom⟩ :=
    eventually_offset_estimates_of_density_rate hΔ r N h4 hr hN hn p q hp hq hNlim hE₀ herror
  obtain ⟨M, hM, hupper⟩ := ratio_density_eventually_bounded hΔ Qρ hbq hnormQ
  have hU := theorem29_convergence hΔ r N h4 hr hN hn p q hp hq hpBE hqBE hNlim hbp hbq hK hrate
  let k : ℕ → ℕ := fun i => N i / 2 - r - 1
  have hk (i : ℕ) : k i + 1 = N i / 2 - r := by dsimp [k]; have := hn i; omega
  let q' : ∀ i, Fin (k i + 1) → ℝ := fun i j => q i (Fin.cast (hk i) j)
  let a' : ∀ i, Fin (k i + 1) → ℝ := fun i j =>
    alignedRoot (N i) r (hr i) (p i) (Fin.cast (hk i) j)
  have hq' (i : ℕ) : q' i ∈ S_n (k i + 1) := mem_S_n_cast (hk i) (hq i)
  have ha' (i : ℕ) (j : Fin (k i + 1)) : a' i j ∈ Ioo (-Real.pi) Real.pi :=
    ratio_alignedRoot_mem_Ioo (hr i) (hp i) _
  have hs' (i : ℕ) : 2 * (k i + 1) ≤ N i := by rw [hk i]; omega
  have hρcast (i : ℕ) (x : ℝ) :
      rootStepDensity (N i) (k i + 1) (q' i) (hq' i) (by omega) (hs' i) x = Qρ i x := by
    exact congrFun (rootStepDensity_cast (hk i) (q i) (hq i) (by omega) (hn i) (hs' i) (by omega)) x
  let d : ℕ → ℝ := fun i => DQ / N i
  have hd : Tendsto d atTop (𝓝 0) := tendsto_const_nhds.div_atTop hNlim
  have hd0 (i : ℕ) : 0 ≤ d i := div_nonneg hDQ (Nat.cast_nonneg _)
  have hmesh : ∀ᶠ i in atTop, ∀ j : Fin (k i + 1 + 1),
      rootPartitionPoint (k i + 1) (q' i) (by omega) j.succ -
        rootPartitionPoint (k i + 1) (q' i) (by omega) j.castSucc ≤ d i := by
    filter_upwards [hgeom] with i hi
    exact ratio_root_mesh_cast (hk i) (by omega) (hn i) (q i) hi.meshQ
  have hshift : ∀ᶠ i in atTop, ∀ j, |(N i : ℝ) * (q' i j - a' i j)| ≤ (G : ℝ) * |q' i j| := by
    filter_upwards [hgeom] with i hi j
    change |(N i : ℝ) * (q i (Fin.cast (hk i) j) -
      alignedRoot (N i) r (hr i) (p i) (Fin.cast (hk i) j))| ≤ _
    rw [← offsetDisplacement_eq_alignedRoot (N i) r (h4 i)]
    exact ratio_offset_root_linear (h4 i) (hr i) (hp i) (hq i) hi.pair _
  have hupper' : ∀ᶠ i in atTop, ∀ x ∈ Icc (-Real.pi) Real.pi,
      rootStepDensity (N i) (k i + 1) (q' i) (hq' i) (by omega) (hs' i) x ≤ M := by
    filter_upwards [hupper] with i hi x hx
    rw [hρcast]
    exact hi x hx
  have hρpoint (x : ℝ) (hx : x ∈ Ioo (-Real.pi) Real.pi) :
      Tendsto (fun i => rootStepDensity (N i) (k i + 1) (q' i) (hq' i) (by omega) (hs' i) x)
        atTop (𝓝 (rho Δ x)) := by
    simp_rw [hρcast]
    exact ratio_density_tendsto hΔ Qρ hbq hnormQ (Ioo_subset_Icc_self hx)
  have hpred (x : ℝ) (hx : x ∈ Ioo (-Real.pi) Real.pi) (_hx0 : x ≠ 0) :
      Tendsto (fun i => (N i : ℝ) *
        (q' i (ratioRootIndex (by omega) (q' i) x) - a' i (ratioRootIndex (by omega) (q' i) x)))
        atTop (𝓝 ((r : ℝ) * tauCont Δ x / rho Δ x)) := by
    have hpoint := hU.tendsto_at (Ioo_subset_Icc_self hx)
    have hdiv := hpoint.div_const (rho Δ x)
    apply hdiv.congr
    intro i
    have hρne := (rho_pos hΔ x).ne'
    have hproj : (N i : ℝ) *
        (q' i (ratioRootIndex (by omega) (q' i) x) - a' i (ratioRootIndex (by omega) (q' i) x)) =
        offsetFunction (N i) r (h4 i) (hr i) (p i) (q i) (hn i) x := by
      change (N i : ℝ) * (q i (Fin.cast (hk i) (ratioRootIndex (by omega) (q' i) x)) -
        alignedRoot (N i) r (hr i) (p i) (Fin.cast (hk i) (ratioRootIndex (by omega) (q' i) x))) = _
      rw [← offsetDisplacement_eq_alignedRoot (N i) r (h4 i),
        ratio_rootIndex_cast (hk i) (by omega) (hn i) (q i) x,
        ← ratio_offsetFunction_eq_predecessor (h4 i) (hr i) (hn i) (p i) (q i) (hq i)]
    rw [hproj]
    field_simp
  have ht := ratio_logsum_tendsto_of_geometry hc G.property hM N k hN q' a' hq' ha' hs' hNlim
    d hd hd0 hmesh hshift hupper' (rho Δ) (fun x => (r : ℝ) * tauCont Δ x / rho Δ x) hρpoint hpred
  have hsum (i : ℕ) : (∑ j, (ratioEll c (q' i j) - ratioEll c (a' i j))) =
      ∑ j, (ratioEll c (q i j) - ratioEll c (alignedRoot (N i) r (hr i) (p i) j)) :=
    Equiv.sum_comp (finCongr (hk i))
      (fun j => ratioEll c (q i j) - ratioEll c (alignedRoot (N i) r (hr i) (p i) j))
  have hInt : (∫ x in Icc (-Real.pi) Real.pi,
      ratioEllPrime c x * ((r : ℝ) * tauCont Δ x / rho Δ x) * rho Δ x) =
      (r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x := by
    calc
      _ = ∫ x in Icc (-Real.pi) Real.pi, (r : ℝ) * (ratioEllPrime c x * tauCont Δ x) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        field_simp [(rho_pos hΔ x).ne']
      _ = (r : ℝ) * ∫ x in Icc (-Real.pi) Real.pi, ratioEllPrime c x * tauCont Δ x :=
        integral_const_mul _ _
      _ = _ := by
        rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Icc_eq_integral_Ioc]
  simpa only [hsum, hInt] using ht

/-- Equation (3.8), for either parity: the product uses the even shift or
the odd midpoint according to `alignedRoot`. At the odd zero mode both
total factors are one, so including that mode contributes exactly one. -/
theorem ratio_bulk_product_limit {c : ℝ} (hc : 2 < c) :
    Tendsto (fun i => ∏ j,
      ‖BetheAnsatz.M c (BetheAnsatz.z (q i j))‖ /
        ‖BetheAnsatz.M c (BetheAnsatz.z (alignedRoot (N i) r (hr i) (p i) j))‖) atTop
      (𝓝 (Real.exp ((r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x))) := by
  have ht := (Real.continuous_exp.tendsto _).comp
    (ratio_bulk_log_limit hΔ r N h4 hr hN hn p q hp hq hpBE hqBE hNlim hbp hbq hK hrate hc)
  apply ht.congr
  intro i
  dsimp only [Function.comp_def]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Real.exp_sub, ratioEll, ratioEll,
    Real.exp_log (norm_pos_iff.mpr (ratio_M_ne_zero hc _)),
    Real.exp_log (norm_pos_iff.mpr (ratio_M_ne_zero hc _))]

end

end PottsDiscontinuity.Bethe

