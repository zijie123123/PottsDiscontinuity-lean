module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.TorusExploration.FiniteTailBound
public import PottsDiscontinuity.TorusExploration.TailPositivity
public import PottsDiscontinuity.TorusExploration.UpperRateLimits

/-! Equation (3.16) with the exact positive-even periods, frozen free limit,
and frozen diagonalSite rate used by RCMProof.contract_eq316. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus TorusRC FK CorrLength MeasureTheory Filter Topology
noncomputable section

/-- The height limsup bound holds at each sufficiently large fixed width. -/
theorem positiveEvenVerticalTailRateE_inner_limsup_le
    (q : Set.Ici (1 : ℝ)) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 0 μ)
    (ξinv : ℝ) (hRate : Tendsto (fun n : ℕ =>
      -Real.log (μ.real (CorrLength.connectionEvent (0,0) (diagonalSite n)))/(n : ℝ)) atTop (𝓝 ξinv))
    (r : ℕ) (hr : 1 ≤ r) (n : ℕ) (hN4 : 4 ≤ positiveEvenPeriod n)
    (hrN : r ≤ positiveEvenPeriod n/2) :
    limsup (fun m : ℕ => positiveEvenVerticalTailRateE q r n m) atTop ≤
      (-((r-1 : ℕ) : ℝ)*ξinv : ℝ) := by
  let N := positiveEvenPeriod n
  let p : ℕ → ℝ := fun m => torusRCProbability (positiveEvenPeriod_even n)
    (positiveEvenPeriod_even m) q
    (torusRCVerticalTail (positiveEvenPeriod_even n) (positiveEvenPeriod_even m)
      ⟨0,positiveEvenPeriod_pos m⟩ r)
  let D : ℕ → ℝ := fun k => μ.real (CorrLength.connectionEvent (0,0) (diagonalSite k))
  let K := (N : ℝ)^(2*r)/(1-(rcCriticalParameter q).val)^N
  have hK : 0 < K := div_pos
    (pow_pos (by exact_mod_cast positiveEvenPeriod_pos n) _)
    (pow_pos (sub_pos.2 (criticalParameter_lt_one q)) _)
  change limsup (fun m => ((Real.log (p m)/(positiveEvenPeriod m : ℝ) : ℝ) : EReal)) atTop ≤ _
  apply log_tail_limsup_le D p
    (fun k => isRCInfiniteVolumeLimit_connection_positive (criticalParameters q) μ hμ (0,0) (diagonalSite k))
    ξinv hRate K hK (r-1)
  filter_upwards [eventually_ge_atTop 1] with m hm
  refine ⟨windingTail_probability_pos (positiveEvenPeriod_even n) (positiveEvenPeriod_even m)
    ⟨0,positiveEvenPeriod_pos m⟩ q r hrN,?_⟩
  exact windingTail_probability_le (positiveEvenPeriod_even n) (positiveEvenPeriod_even m)
    hN4 (by dsimp [positiveEvenPeriod]; omega) q μ hμ r hr

/-- Equation (3.16), exactly in the form of RCMProof.contract_eq316. -/
theorem eq316 (q : Set.Ici (1 : ℝ)) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 0 μ)
    (ξinv : ℝ) (hRate : Tendsto (fun n : ℕ =>
      -Real.log (μ.real (CorrLength.connectionEvent (0,0) (diagonalSite n)))/(n : ℝ)) atTop (𝓝 ξinv))
    (r : ℕ) (hr : 1 ≤ r) :
    limsup (fun n : ℕ => limsup
      (fun m : ℕ => positiveEvenVerticalTailRateE q r n m) atTop) atTop ≤
      (-((r-1 : ℕ) : ℝ)*ξinv : ℝ) := by
  have he : ∀ᶠ n : ℕ in atTop,
      limsup (fun m : ℕ => positiveEvenVerticalTailRateE q r n m) atTop ≤
        ((-((r-1 : ℕ) : ℝ)*ξinv : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop (r+1)] with n hn
    apply positiveEvenVerticalTailRateE_inner_limsup_le q μ hμ ξinv hRate r hr n
    · dsimp [positiveEvenPeriod]; omega
    · dsimp [positiveEvenPeriod]; omega
  simpa using (limsup_le_limsup (v := fun _ : ℕ =>
    ((-((r-1 : ℕ) : ℝ)*ξinv : ℝ) : EReal)) he)

end
end PottsDiscontinuity.TorusExploration
