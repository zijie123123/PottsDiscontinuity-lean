module

public import PottsDiscontinuity.CorrLength.Positivity
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite
public import PottsDiscontinuity.Potts.FreeSpinFormula

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.CorrLength

theorem free_spin_rate_of_rc_rate (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 φ))
    (hφrc : IsRCInfiniteVolumeLimit (fkParameters q hq β hβ).toP
      (fkParameters q hq β hβ).toQ 0 φ.toMeasure)
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β 0 μ.toMeasure)
    (L : ℝ)
    (hL : Tendsto
      (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
        (φ.toMeasure.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
      atTop (𝓝 L)) :
    Tendsto
      (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
        (μ.toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / (q : ℝ)))
      atTop (𝓝 L) := by
  let θ : FK.Parameters := fkParameters q hq β hβ
  let c : ℝ := 1 - 1 / (q : ℝ)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqone : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hc : 0 < c := by
    dsimp [c]
    rw [sub_pos]
    exact (div_lt_one hqpos).2 hqone
  have hconn (n : ℕ) : 0 < φ.toMeasure.real
      {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} := by
    have hevent : connectionEvent (0, 0) (diagonalSite n) =
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} := by
      ext ω
      exact connectionEvent_iff_rcInfiniteReachable (0, 0) (diagonalSite n) ω
    rw [← hevent]
    exact isRCInfiniteVolumeLimit_connection_positive θ φ.toMeasure hφrc (0, 0)
      (diagonalSite n)
  have hcorr := free_spin_correlation q hq β hβ φ hφ μ hμ
  have hfactor (n : ℕ) :
      μ.toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / (q : ℝ) =
        c * φ.toMeasure.real
          {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} := by
    rw [hcorr (0, 0) (diagonalSite n)]
    dsimp [c]
    ring
  have hlog (n : ℕ) :
      Real.log (μ.toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / (q : ℝ)) =
        Real.log c + Real.log
          (φ.toMeasure.real
            {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}) := by
    rw [hfactor]
    exact Real.log_mul hc.ne' (hconn n).ne'
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log c) atTop (𝓝 0) := by
    have hprod : Tendsto (fun n : ℕ => (-Real.log c) * (n : ℝ)⁻¹) atTop
        (𝓝 ((-Real.log c) * 0)) := tendsto_const_nhds.mul hinv
    have heq : (fun n : ℕ => -(1 / (n : ℝ)) * Real.log c) =
        (fun n : ℕ => (-Real.log c) * (n : ℝ)⁻¹) := by
      funext n
      simp only [one_div]
      ring
    rw [heq]
    simpa using hprod
  have hsum := hL.add hsmall
  have hseq :
      (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
        (μ.toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / (q : ℝ))) =
      (fun n : ℕ =>
        -(1 / (n : ℝ)) * Real.log
            (φ.toMeasure.real
              {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}) +
          -(1 / (n : ℝ)) * Real.log c) := by
    funext n
    rw [hlog n]
    ring
  rw [hseq]
  simpa using hsum

end PottsDiscontinuity.PottsThm
