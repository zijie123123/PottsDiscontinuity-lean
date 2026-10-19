module

public import PottsDiscontinuity.Bethe.RatioPole
public import PottsDiscontinuity.Bethe.RatioProfile
public import PottsDiscontinuity.Bethe.RatioWallis

/-! # Half-integer root scales give the logarithmic Wallis factors -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

theorem ratio_half_integer_midpoint_log_tendsto {ι : Type*} {l : Filter ι}
    {c ρ : ℝ} (hc : 2 < c) (hρ : 0 < ρ) (k : ℕ)
    (N : ι → ℝ) (hN : ∀ i, N i ≠ 0) (hNlim : Tendsto N l atTop)
    (x y : ι → ℝ) (hx : ∀ i, x i ∈ Ioo (-Real.pi) Real.pi)
    (hy : ∀ i, y i ∈ Ioo (-Real.pi) Real.pi) (hxpos : ∀ i, 0 < x i) (hypos : ∀ i, 0 < y i)
    (hscaleX : Tendsto (fun i => N i * x i) l (𝓝 (((k : ℝ) + 1 / 2) / ρ)))
    (hscaleY : Tendsto (fun i => N i * y i) l (𝓝 (((k : ℝ) + 3 / 2) / ρ))) :
    Tendsto (fun i => 2 * ratioEll c ((x i + y i) / 2) - ratioEll c (x i) - ratioEll c (y i)) l
      (𝓝 (Real.log (ratioWallisFactor k))) := by
  have hxlim : Tendsto x l (𝓝 0) := by
    have ht := hscaleX.div_atTop hNlim
    apply ht.congr
    intro i
    field_simp [hN i]
  have hylim : Tendsto y l (𝓝 0) := by
    have ht := hscaleY.div_atTop hNlim
    apply ht.congr
    intro i
    field_simp [hN i]
  have ha : 0 < ((k : ℝ) + 1 / 2) / ρ := by positivity
  have hb : 0 < ((k : ℝ) + 3 / 2) / ρ := by positivity
  have ht := ratio_midpoint_factor_tendsto hc ha hb N hN x y hx hy hxpos hypos hxlim hylim hscaleX hscaleY
  have hvalue : 4 * (((k : ℝ) + 1 / 2) / ρ) * (((k : ℝ) + 3 / 2) / ρ) /
      ((((k : ℝ) + 1 / 2) / ρ + ((k : ℝ) + 3 / 2) / ρ) ^ 2) = ratioWallisFactor k := by
    unfold ratioWallisFactor
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have hsum : ((k : ℝ) + 1 / 2) / ρ + ((k : ℝ) + 3 / 2) / ρ = 2 * ((k : ℝ) + 1) / ρ := by ring
    rw [hsum]
    field_simp [hρ.ne', hk]
    ring
  rw [hvalue] at ht
  have hlog := (Real.continuousAt_log (ratio_wallisFactor_pos k).ne').tendsto.comp ht
  apply hlog.congr
  intro i
  dsimp only [Function.comp_def]
  have hmx : ‖M c (z (x i))‖ ≠ 0 := norm_ne_zero_iff.mpr (ratio_M_ne_zero hc _)
  have hmy : ‖M c (z (y i))‖ ≠ 0 := norm_ne_zero_iff.mpr (ratio_M_ne_zero hc _)
  have hmm : ‖M c (z ((x i + y i) / 2))‖ ≠ 0 := norm_ne_zero_iff.mpr (ratio_M_ne_zero hc _)
  rw [Real.log_div (pow_ne_zero 2 hmm) (mul_ne_zero hmx hmy), Real.log_pow, Real.log_mul hmx hmy]
  unfold ratioEll
  ring

end PottsDiscontinuity.Bethe
