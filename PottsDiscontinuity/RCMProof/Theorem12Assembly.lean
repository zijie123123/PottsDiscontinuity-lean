module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.RCMProof.Item3

@[expose] public section

open MeasureTheory Filter Topology Real

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity

/-- The exact frozen Theorem 1.2 conclusion, assembled from FK box-limit
existence, the proved item-3 rate for every free limit, and duality. Its only
remaining input is equation (3.19), required by the proved (3.15) theorem. -/
theorem rc_theorem_1_2_assembled
    (hW21h319 : contract_h319)
    (q : ℝ) (hq : 4 < q) :
    ∃ φ : Fin 2 → Measure (squareLattice.edgeSet → Bool),
      (∀ i, IsRCInfiniteVolumeLimit
        (rcCriticalParameter ⟨q, Set.mem_Ici.2 (by linarith)⟩)
        ⟨q, Set.mem_Ioi.2 (by linarith)⟩ i (φ i)) ∧
      φ 1 ≠ φ 0 ∧
      (φ 1).real {ω | ∃ x, {y | (rcInfiniteOpenGraph ω).Reachable x y}.Infinite} = 1 ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((φ 0).real {ω | (rcInfiniteOpenGraph ω).Reachable
                (0, 0) (diagonalSite n)})) atTop (𝓝 (lam + 2 * S))) := by
  exact rc_theorem_1_2_from_item3 q hq
    (rcItem3ForEveryFreeLimit_proved hW21h319 q hq)

end PottsDiscontinuity.RCMProof
