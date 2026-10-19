module

public import PottsDiscontinuity.Bethe.RatioBulkBounds
public import PottsDiscontinuity.Bethe.RatioBulkPointwise

/-! # Dominated convergence for the singular logarithmic root sum

This module assembles the general analytic moving-test argument. Source
root families are specialized separately: their displacement limit is
Theorem 2.9 and their finite bounds come from the density-rate geometry.
-/

@[expose] public section

open Set Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

theorem ratio_logsum_tendsto_of_geometry {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {c C M : ℝ} (hc : 2 < c) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (N k : ι → ℕ) (hN : ∀ i, 0 < N i)
    (q a : ∀ i, Fin (k i + 1) → ℝ) (hq : ∀ i, q i ∈ S_n (k i + 1))
    (ha : ∀ i j, a i j ∈ Ioo (-Real.pi) Real.pi) (hs : ∀ i, 2 * (k i + 1) ≤ N i)
    (hNlim : Tendsto (fun i => (N i : ℝ)) l atTop)
    (d : ι → ℝ) (hd : Tendsto d l (𝓝 0)) (hdnonneg : ∀ i, 0 ≤ d i)
    (hmesh : ∀ᶠ i in l, ∀ j : Fin (k i + 1 + 1),
      rootPartitionPoint (k i + 1) (q i) (by omega) j.succ -
        rootPartitionPoint (k i + 1) (q i) (by omega) j.castSucc ≤ d i)
    (hshift : ∀ᶠ i in l, ∀ j, |(N i : ℝ) * (q i j - a i j)| ≤ C * |q i j|)
    (hupper : ∀ᶠ i in l, ∀ x ∈ Icc (-Real.pi) Real.pi,
      rootStepDensity (N i) (k i + 1) (q i) (hq i) (by omega) (hs i) x ≤ M)
    (w E : ℝ → ℝ)
    (hρ : ∀ x ∈ Ioo (-Real.pi) Real.pi,
      Tendsto (fun i => rootStepDensity (N i) (k i + 1) (q i) (hq i) (by omega) (hs i) x) l (𝓝 (w x)))
    (he : ∀ x ∈ Ioo (-Real.pi) Real.pi, x ≠ 0 →
      Tendsto (fun i => (N i : ℝ) *
        (q i (ratioRootIndex (by omega) (q i) x) - a i (ratioRootIndex (by omega) (q i) x)))
        l (𝓝 (E x))) :
    Tendsto (fun i => ∑ j, (ratioEll c (q i j) - ratioEll c (a i j))) l
      (𝓝 (∫ x in Icc (-Real.pi) Real.pi, ratioEllPrime c x * E x * w x)) := by
  let B := Real.pi * (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + Real.pi ^ 2 / 4
  have hB : 0 ≤ B := ratio_profile_bound_nonneg hc
  let L := 2 * B * C
  let F : ι → ℝ → ℝ := fun i => ratioInteriorTest (N i) (q i) (hq i)
    (fun j => (N i : ℝ) * (ratioEll c (q i j) - ratioEll c (a i j)))
  let g : ℝ → ℝ := (Icc (-Real.pi) Real.pi).indicator
    (fun x => ratioEllPrime c x * E x * w x)
  let bound : ℝ → ℝ := (Icc (-Real.pi) Real.pi).indicator (fun _ => L * M)
  have hmeas : ∀ᶠ i in l, AEStronglyMeasurable (F i) := Eventually.of_forall (fun i =>
    (ratio_interiorTest_integrable (hq i) _).aestronglyMeasurable)
  have hbound : ∀ᶠ i in l, ∀ᵐ x, ‖F i x‖ ≤ bound x := by
    filter_upwards [hshift, hupper, hNlim.eventually (eventually_ge_atTop (2 * C))]
      with i hi hu hiN
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs]
    exact ratio_log_step_bound hc (hN i) hC hM hiN (hq i) (ha i) (hs i) hi hu x
  have hboundInt : Integrable bound := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const (by simp)
  have hpoint : ∀ᵐ x, Tendsto (fun i => F i x) l (𝓝 (g x)) := by
    filter_upwards [Measure.ae_ne volume (0 : ℝ), Measure.ae_ne volume Real.pi,
      Measure.ae_ne volume (-Real.pi)] with x hx0 hxp hxm
    by_cases hx : x ∈ Icc (-Real.pi) Real.pi
    · have hxoo : x ∈ Ioo (-Real.pi) Real.pi :=
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hxm), lt_of_le_of_ne hx.2 hxp⟩
      have ht := ratio_log_step_tendsto hc N k hN q a hq hs hNlim d hd hdnonneg hmesh w E
        hxoo hx0 (hρ x hxoo) (he x hxoo hx0)
      simpa only [g, indicator_of_mem hx] using ht
    · have heq (i : ι) : F i x = 0 := ratio_interiorTest_support (hq i) _ hx
      simpa only [g, heq, indicator_of_notMem hx] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) l (𝓝 0))
  have hInt := tendsto_integral_filter_of_dominated_convergence bound hmeas hbound hboundInt hpoint
  have hgInt : (∫ x, g x) = ∫ x in Icc (-Real.pi) Real.pi, ratioEllPrime c x * E x * w x :=
    integral_indicator measurableSet_Icc
  rw [hgInt] at hInt
  have hlast : Tendsto
      (fun i => ratioEll c (q i (Fin.last (k i))) - ratioEll c (a i (Fin.last (k i)))) l (𝓝 0) := by
    have hLlim : Tendsto (fun i => L / (N i : ℝ)) l (𝓝 0) :=
      tendsto_const_nhds.div_atTop hNlim
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hshift, hNlim.eventually (eventually_ge_atTop (2 * C)),
      hLlim.eventually (gt_mem_nhds hε)] with i hi hiN hLi
    have hb := ratio_scaled_root_log_bound hc (hN i) hC hiN ((hq i).1 (Fin.last (k i))) (ha i (Fin.last (k i)))
      (hi (Fin.last (k i)))
    have hNp : (0 : ℝ) < N i := Nat.cast_pos.mpr (hN i)
    rw [abs_mul, abs_of_pos hNp] at hb
    change (N i : ℝ) * |ratioEll c (q i (Fin.last (k i))) - ratioEll c (a i (Fin.last (k i)))| ≤ L at hb
    have hb' : |ratioEll c (q i (Fin.last (k i))) - ratioEll c (a i (Fin.last (k i)))| ≤ L / N i := by
      apply (le_div_iff₀ hNp).mpr
      nlinarith only [hb]
    rw [Real.dist_eq, sub_zero]
    exact hb'.trans_lt hLi
  have hi (i : ι) : (∫ x, F i x) =
      ∑ j : Fin (k i), (ratioEll c (q i j.castSucc) - ratioEll c (a i j.castSucc)) := by
    rw [ratio_integral_interiorTest (hN i) (hq i)]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hn : (N i : ℝ) ≠ 0 := by exact_mod_cast (hN i).ne'
    field_simp
  have ht := hInt.add hlast
  rw [add_zero] at ht
  apply ht.congr
  intro i
  rw [hi i, Fin.sum_univ_castSucc]

end PottsDiscontinuity.Bethe
