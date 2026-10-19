module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Logarithmic limits of block-product lower bounds -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC

/-- The integer number of complete blocks has asymptotic density 1/d. -/
theorem tendsto_completeBlocks_div (d : ℕ) (hd : 0 < d) :
    Tendsto (fun M : ℕ => ((M/d:ℕ):ℝ)/(M:ℝ)) atTop (𝓝 (1/(d:ℝ))) := by
  have hmod := tendsto_mod_div_atTop_nhds_zero_nat hd
  have hlim := ((tendsto_const_nhds (x := (1:ℝ))).sub hmod).div_const (d:ℝ)
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hsplit : ((M%d:ℕ):ℝ)+(d:ℝ)*((M/d:ℕ):ℝ) = (M:ℝ) := by
    exact_mod_cast Nat.mod_add_div M d
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  field_simp
  nlinarith

/-- A fixed finite-energy cost vanishes in the height-normalized logarithm.
The complete-block floor is retained exactly. This is a numerical lemma;
its product premise is supplied by the proved finite-volume estimate. -/
theorem log_block_product_liminf (height : ℕ → ℕ)
    (hheight : Tendsto height atTop atTop) (p : ℕ → ℝ)
    (C a b : ℝ) (hC : 0 < C) (ha : 0 < a) (hb : 0 < b)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hp : ∀ᶠ k in atTop,
      C * a ^ ((height k:ℝ)/(d:ℝ)) * b ^ (height k/e) ≤ p k) :
    ((Real.log a/(d:ℝ) + Real.log b/(e:ℝ):ℝ):EReal) ≤
      liminf (fun k => ((Real.log (p k)/(height k:ℝ):ℝ):EReal)) atTop := by
  let f : ℕ → ℝ := fun M => Real.log C/(M:ℝ) + Real.log a/(d:ℝ) +
    (((M/e:ℕ):ℝ)/(M:ℝ))*Real.log b
  have hf : Tendsto f atTop (𝓝 (Real.log a/(d:ℝ)+Real.log b/(e:ℝ))) := by
    have h := ((tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).add_const
      (Real.log a/(d:ℝ))).add ((tendsto_completeBlocks_div e he).mul_const (Real.log b))
    simpa only [zero_add,one_div_mul_eq_div] using h
  have hle : ∀ᶠ k in atTop, ((f (height k):ℝ):EReal) ≤
      ((Real.log (p k)/(height k:ℝ):ℝ):EReal) := by
    filter_upwards [hp,hheight.eventually (eventually_ge_atTop 1)] with k hk hH
    have hpos : 0 < C*a^((height k:ℝ)/(d:ℝ))*b^(height k/e) := by positivity
    have hlog := Real.log_le_log hpos hk
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul hC.ne' (Real.rpow_pos_of_pos ha _).ne',
      Real.log_rpow ha,Real.log_pow] at hlog
    apply EReal.coe_le_coe_iff.mpr
    have hHpos : (0:ℝ)<height k := by exact_mod_cast (show 0<height k by omega)
    have hdiv := div_le_div_of_nonneg_right hlog hHpos.le
    dsimp [f]
    convert hdiv using 1; field_simp
  have hlim : Tendsto (fun k => ((f (height k):ℝ):EReal)) atTop
      (𝓝 ((Real.log a/(d:ℝ)+Real.log b/(e:ℝ):ℝ):EReal)) :=
    EReal.tendsto_coe.mpr (hf.comp hheight)
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf hle

end PottsDiscontinuity.TorusRC
