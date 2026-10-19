module

public import PottsDiscontinuity.TorusRC.OuterLowerLimit
public import PottsDiscontinuity.TorusRC.CorrelationRate
public import PottsDiscontinuity.TorusRC.BlockLogRate

/-! # Lemma 3.15, equation (3.15), with h319 as the sole external premise -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC

open CorrLength

/-- Equation (3.15) along widths divisible by eight and positive even heights.
The rate is the unique Fekete limit for the exact rotated free law (`CorrLength/`).
The torus topology premises are discharged (`TorusTopology/`); only the named crossing
estimate h319 is a premise here. It is proved by `TorusCrossing.h319_proved`
(`TorusCrossing/Final.lean`). -/
theorem eq315 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ((-inverseCorrelationLength q:ℝ):EReal) ≤ torusRCUOneIteratedLiminf q := by
  obtain ⟨c,hc,_,hbound⟩ := torusRCU_one_outer_liminf_of_h319 q hh319
  have hrate : Tendsto (fun n : ℕ =>
      Real.log ((rotatedDiagonalConnectionProbability (torusRCBridgeParameters q) n : NNReal):ℝ) /
        ((2*n:ℕ):ℝ)) atTop (𝓝 (-inverseCorrelationLength q)) := by
    simpa only [neg_div,neg_neg] using (tendsto_inverseCorrelationLength q).neg
  have hlim : Tendsto (fun n : ℕ =>
      ((Real.log (c/(9*(n:ℝ)^2))/(n:ℝ) +
        Real.log ((rotatedDiagonalConnectionProbability (torusRCBridgeParameters q) n : NNReal):ℝ) /
          ((2*n:ℕ):ℝ):ℝ):EReal)) atTop (𝓝 ((-inverseCorrelationLength q:ℝ):EReal)) := by
    apply EReal.tendsto_coe.mpr
    simpa only [zero_add] using (tendsto_block_log_rate_zero c hc).add hrate
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact hbound n hn

end PottsDiscontinuity.TorusRC
