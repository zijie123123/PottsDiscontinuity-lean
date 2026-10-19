module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Closing strict probability lower bounds after taking logarithms -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC

/-- Strict lower approximations to a positive probability recover its full
logarithmic bound, including when the upper target is an extended real. -/
theorem log_probability_lower_closed (p : ℝ) (hp : 0 < p)
    (a d : ℝ) (L : EReal)
    (h : ∀ t : ℝ, 0 < t → t < p → ((a+Real.log t/d:ℝ):EReal) ≤ L) :
    ((a+Real.log p/d:ℝ):EReal) ≤ L := by
  let t : ℕ → ℝ := fun k => p*(1-1/((k:ℝ)+2))
  have htpos (k : ℕ) : 0 < t k := by
    dsimp [t]
    apply mul_pos hp
    have hk : (1:ℝ)<(k:ℝ)+2 := by have h := Nat.cast_nonneg (α := ℝ) k; linarith
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hk)
  have htlt (k : ℕ) : t k < p := by
    dsimp [t]
    have hk : 0 < 1/((k:ℝ)+2) := by positivity
    nlinarith
  have ht : Tendsto t atTop (𝓝 p) := by
    have hdiv : Tendsto (fun k : ℕ => 1/((k:ℝ)+2)) atTop (𝓝 (0:ℝ)) :=
      by simpa only [Nat.cast_add,Nat.cast_ofNat] using
        (tendsto_add_atTop_iff_nat 2).2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hlim := (tendsto_const_nhds (x := p)).mul
      ((tendsto_const_nhds (x := (1:ℝ))).sub hdiv)
    simpa [t] using hlim
  have hlog := ht.log hp.ne'
  have hlim : Tendsto (fun k => ((a+Real.log (t k)/d:ℝ):EReal)) atTop
      (𝓝 ((a+Real.log p/d:ℝ):EReal)) :=
    EReal.tendsto_coe.mpr (tendsto_const_nhds.add (hlog.div_const d))
  exact le_of_tendsto hlim (Eventually.of_forall fun k => h (t k) (htpos k) (htlt k))

end PottsDiscontinuity.TorusRC
