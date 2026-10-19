module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.IsPottsInfiniteVolumeLimit
public import PottsDiscontinuity.Frozen.Defs.IsTranslationErgodic
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite
public import PottsDiscontinuity.Frozen.Defs.PottsCriticalBeta
public import PottsDiscontinuity.PottsThm.PottsTheorem11
public import PottsDiscontinuity.RCMProof.Item3
public import PottsDiscontinuity.TorusCrossing.Final
public import PottsDiscontinuity.Analysis.Identity44

/-!
# Proof of Theorem 1.1 (`potts_theorem_1_1`)

This module proves the exact statement of Theorem 1.1. The statement file
`PottsDiscontinuity/Frozen/Theorem11.lean` restates it as `PottsDiscontinuity.potts_theorem_1_1`,
is checked against `Challenge.lean`, and closes it with the export below. This module does not
import the statement file.

Convention: the export `PottsDiscontinuity.Provider.potts_theorem_1_1` has the type of the
stated theorem, with the leading parameter `q` implicit and the premise `4 < q` an explicit
`:= by assumption` auto-parameter, so that the proof body in the statement file is exactly
`by exact PottsDiscontinuity.Provider.potts_theorem_1_1` (no arguments).

Proof: `PottsThm.potts_theorem_1_1_of_rc_rate` (Theorem 1.1 from the random-cluster rate) applied
to the random-cluster rate for every free critical limit, which is
`RCMProof.rcItem3ForEveryFreeLimit_proved` (item 3 of Theorem 1.2; its premise, the crossing
estimate (3.19), is `TorusCrossing.h319_proved`), together with the positivity `0 < λ + 2S` from
`identity44` (the analytic part of Theorem 1.2).
-/

@[expose] public section

namespace PottsDiscontinuity.Provider

open MeasureTheory Filter Topology Real
open scoped ENNReal

/-- The random-cluster input of Theorem 1.1: the rate (1.2) with its positivity, for every free critical limit,
at an integer `q > 4`. -/
theorem potts_rc_rate_input (q : ℕ) (hq : 4 < q) :
    ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
      ∀ φ₀ : Measure FK.LatticeConfiguration,
        IsRCInfiniteVolumeLimit
          (rcCriticalParameter ⟨(q : ℝ), by
            change (1 : ℝ) ≤ (q : ℝ)
            exact_mod_cast (show 1 ≤ q by omega)⟩)
          ⟨(q : ℝ), by
            change (0 : ℝ) < (q : ℝ)
            exact_mod_cast (show 0 < q by omega)⟩ 0 φ₀ →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
            (φ₀.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
            atTop (𝓝 (lam + 2 * S)) ∧ 0 < lam + 2 * S := by
  intro lam hlam hcosh φ₀ hφ₀
  have hq' : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨S, hS, hrate⟩ := RCMProof.rcItem3ForEveryFreeLimit_proved
    (fun q => TorusCrossing.h319_proved q) (q : ℝ) hq' φ₀ hφ₀ lam hlam hcosh
  obtain ⟨S₀, _T, hS₀, _hT, hpos, _hid⟩ := identity44 lam hlam
  have hSS₀ : S = S₀ := tendsto_nhds_unique hS hS₀
  exact ⟨S, hS, hrate, hSS₀ ▸ hpos⟩

/-- Theorem 1.1, in the form used to close the statement `potts_theorem_1_1`. -/
theorem potts_theorem_1_1 {q : ℕ} (hq : 4 < q := by assumption) :
    ∃ μ : Fin (q + 1) → Measure (ℤ × ℤ → Set.Icc 1 q),
      (∀ i, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i (μ i)) ∧
      ((∀ i j, i ≠ j → μ i ≠ μ j) ∧ (∀ i, IsTranslationErgodic (μ i)) ∧
        μ 0 ≠ (q : ℝ≥0∞)⁻¹ • ∑ i : Fin q, μ i.succ) ∧
      (∀ i : Fin q, (1 : ℝ) / q < (μ i.succ).real {σ | ((σ (0, 0) : ℕ)) = (i.succ : ℕ)}) ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((μ 0).real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / q))
            atTop (𝓝 (lam + 2 * S)) ∧
          0 < lam + 2 * S) :=
  PottsThm.potts_theorem_1_1_of_rc_rate q hq (potts_rc_rate_input q hq)

end PottsDiscontinuity.Provider
