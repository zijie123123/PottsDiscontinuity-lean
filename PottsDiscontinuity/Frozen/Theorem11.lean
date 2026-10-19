module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.IsPottsInfiniteVolumeLimit
public import PottsDiscontinuity.Frozen.Defs.IsTranslationErgodic
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite
public import PottsDiscontinuity.Frozen.Defs.PottsCriticalBeta
public import PottsDiscontinuity.Provider.Theorem11

/-!
# Theorem statement `potts_theorem_1_1` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree. Its proof is the assembled result from `PottsDiscontinuity/Provider/`.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- **Theorem 1.1** (arXiv:1611.09877v2, p. 2). -/
theorem potts_theorem_1_1 (q : ℕ) (hq : 4 < q) :
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
  by exact PottsDiscontinuity.Provider.potts_theorem_1_1

end PottsDiscontinuity
