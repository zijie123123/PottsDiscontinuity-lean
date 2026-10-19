module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT0Limit

/-!
# Local analytic input for the paired T₁ limit

The only pole in a paired ML-edge contribution is the moved-root factor `L(e^{it})`.
This module records its residue with the complex phase convention used in the source.
-/

@[expose] public section

open Complex Filter Topology

namespace PottsDiscontinuity.BetheAnsatz

/-- The derivative of the unit phase `z(t)=exp(i t)` at zero. -/
theorem hasDerivAt_z_zero : HasDerivAt z I 0 := by
  convert! (hasDerivAt_exp_smul_const (I : ℂ) (0 : ℂ)).comp_ofReal using 1
  · ext t
    simp [z, smul_eq_mul, mul_comm, Complex.exp_eq_exp_ℂ]
  · simp

/-- The exponential denominator has slope `-i` at zero. -/
theorem tendsto_one_sub_z_div_id_zero :
    Tendsto (fun t : ℝ => ((1 - z t) / (t : ℂ))) (𝓝[≠] (0 : ℝ)) (𝓝 (-I)) := by
  have hslope := hasDerivAt_z_zero.tendsto_slope_zero
  have hfun : (fun t : ℝ => ((1 - z t) / (t : ℂ))) =
      fun t => -(t⁻¹ • (z (0 + t) - z 0)) := by
    funext t
    simp only [zero_add, z_zero]
    simp [div_eq_mul_inv, sub_eq_add_neg]
    ring
  rw [hfun]
  exact hslope.neg

/-- Dividing `t` by `1-z(t)` has limit `i` on the punctured neighborhood. -/
theorem tendsto_id_div_one_sub_z_zero :
    Tendsto (fun t : ℝ => (t : ℂ) / (1 - z t)) (𝓝[≠] (0 : ℝ)) (𝓝 I) := by
  have h := tendsto_one_sub_z_div_id_zero.inv₀ (by simp : (-I : ℂ) ≠ 0)
  have hI : (-I : ℂ)⁻¹ = I := by simp
  rw [hI] at h
  apply h.congr'
  filter_upwards [eventually_z_ne_one_zero, self_mem_nhdsWithin] with t ht ht0
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  have hden : 1 - z t ≠ 0 := sub_ne_zero.mpr ht.symm
  field_simp

/-- The principal pole residue of `L(e^{it})`. -/
theorem tendsto_t_mul_L_z_zero (c : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) * L c (z t)) (𝓝[≠] (0 : ℝ))
      (𝓝 (I * (c : ℂ) ^ 2)) := by
  have hz : Tendsto z (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have hAt : ContinuousAt z 0 := hasDerivAt_z_zero.continuousAt
    simpa only [z_zero] using
      hAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hratio := tendsto_id_div_one_sub_z_zero
  have hprod : Tendsto (fun t : ℝ => z t * ((t : ℂ) / (1 - z t)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (I : ℂ)) := by
    simpa using hz.mul hratio
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hAt : ContinuousAt (fun t : ℝ => (t : ℂ)) 0 := continuous_ofReal.continuousAt
    exact hAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hregular : Tendsto (fun t : ℝ =>
      (t : ℂ) + (c : ℂ) ^ 2 * (z t * ((t : ℂ) / (1 - z t))))
      (𝓝[≠] (0 : ℝ)) (𝓝 (I * (c : ℂ) ^ 2)) := by
    have hscaled : Tendsto (fun t : ℝ => (c : ℂ) ^ 2 *
        (z t * ((t : ℂ) / (1 - z t)))) (𝓝[≠] (0 : ℝ))
        (𝓝 ((c : ℂ) ^ 2 * I)) := tendsto_const_nhds.mul hprod
    have hadd := ht.add hscaled
    simpa [add_comm, mul_comm] using hadd
  have heq : (fun t : ℝ => (t : ℂ) * L c (z t)) =ᶠ[𝓝[≠] (0 : ℝ)]
      fun t => (t : ℂ) + (c : ℂ) ^ 2 * (z t * ((t : ℂ) / (1 - z t))) := by
    filter_upwards [eventually_z_ne_one_zero] with t ht
    have hden : 1 - z t ≠ 0 := sub_ne_zero.mpr ht.symm
    unfold L
    field_simp
  apply hregular.congr'
  filter_upwards [heq] with t ht
  exact ht.symm

end PottsDiscontinuity.BetheAnsatz
