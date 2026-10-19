module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.FiniteDuality
public import PottsDiscontinuity.TorusExploration.CylinderUnionBound
public import PottsDiscontinuity.TorusExploration.SeamLawBound
public import PottsDiscontinuity.TorusRC.TopologyBounds

/-! The complete finite-volume upper estimate underlying (3.16). -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus TorusRC FK CorrLength MeasureTheory
variable {N M : ℕ}
noncomputable section

lemma torusRCBridgeParameters_eq_critical (q : Set.Ici (1 : ℝ)) :
    torusRCBridgeParameters q=criticalParameters q := rfl

/-- Finite energy, topology, exact conditional FK exploration, reflection,
and the endpoint union bound give the full torus tail estimate. -/
theorem windingTail_probability_le (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 0 μ)
    (r : ℕ) (hr : 1 ≤ r) :
    torusRCProbability hN hM q (torusRCVerticalTail hN hM ⟨0,by omega⟩ r) ≤
      ((N : ℝ)^(2*r)/(1-(rcCriticalParameter q).val)^N) *
        (Real.sqrt (μ.real (CorrLength.connectionEvent (0,0) (diagonalSite (2*(M-1))))))^(r-1) := by
  have hp : 0 < (1-(rcCriticalParameter q).val)^N :=
    pow_pos (sub_pos.2 (criticalParameter_lt_one q)) N
  have hc := torusRCVerticalTail_close_seam_le_unconditional hN hM (by omega) q r
  have hs := torus_seam_joint_le_cylinder hN hM hN4 hM4 (by omega) q r
  have hb := cylinderCrossings_probability_le hN hM hN4 hM4 (torusRCBridgeParameters q) μ
    (by rwa [torusRCBridgeParameters_eq_critical]) r hr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hp).2
  simpa only [mul_comm] using hc.trans (hs.trans hb)

end
end PottsDiscontinuity.TorusExploration
