module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! # The polynomial crossing prefactor has vanishing block rate -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC

theorem tendsto_block_log_rate_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.log (c/(9*(n:ℝ)^2))/(n:ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 (0:ℝ)) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [pow_one,one_mul,add_zero,Function.comp_def] using h
  have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log c-Real.log 9)).sub
    (hlog.const_mul 2)
  simp only [mul_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  rw [Real.log_div hc.ne' (by positivity),
    Real.log_mul (by norm_num) (by positivity),Real.log_pow]
  ring

end PottsDiscontinuity.TorusRC
