module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.IsRCInfiniteVolumeLimit
public import PottsDiscontinuity.Frozen.Defs.RCCriticalParameter
public import PottsDiscontinuity.Frozen.Defs.RCInfiniteOpenGraph
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite
public import PottsDiscontinuity.RCMProof.Theorem12Assembly
public import PottsDiscontinuity.TorusCrossing.Final

/-!
# Proof of Theorem 1.2, items 1–3 and (1.2) (`rc_theorem_1_2`)

This module proves the exact statement of Theorem 1.2, items 1–3 including (1.2). The statement
file `PottsDiscontinuity/Frozen/Theorem12.lean` restates it as `PottsDiscontinuity.rc_theorem_1_2`,
is checked against `Challenge.lean`, and closes it with the export below. This module does not
import the statement file.

Convention: the export `PottsDiscontinuity.Provider.rc_theorem_1_2` has the type of the stated
theorem, with the leading parameter `q` implicit and the premise `4 < q` an explicit
`:= by assumption` auto-parameter, so that the proof body in the statement file is exactly
`by exact PottsDiscontinuity.Provider.rc_theorem_1_2` (no arguments).

Proof: `RCMProof.rc_theorem_1_2_assembled` (the assembly of Theorem 1.2: box limits, items 1–2
from the positive diagonal rate, item 3 from (1.7), the lower and upper bounds on the inverse
correlation length and the repaired dominance step), whose only premise, equation (3.19) for
every `q ≥ 1` (`RCMProof.contract_h319`), is the crossing estimate `TorusCrossing.h319_proved`.
-/

@[expose] public section

namespace PottsDiscontinuity.Provider

open MeasureTheory Filter Topology Real

/-- Theorem 1.2, items 1–3 and (1.2), in the form used to close the statement
`rc_theorem_1_2`. -/
theorem rc_theorem_1_2 {q : ℝ} (hq : 4 < q := by assumption) :
    ∃ φ : Fin 2 → Measure (squareLattice.edgeSet → Bool),
      (∀ i, IsRCInfiniteVolumeLimit (rcCriticalParameter ⟨q, Set.mem_Ici.2 (by linarith)⟩)
        ⟨q, Set.mem_Ioi.2 (by linarith)⟩ i
        (φ i)) ∧
      φ 1 ≠ φ 0 ∧
      (φ 1).real {ω | ∃ x, {y | (rcInfiniteOpenGraph ω).Reachable x y}.Infinite} = 1 ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((φ 0).real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
            atTop (𝓝 (lam + 2 * S))) :=
  RCMProof.rc_theorem_1_2_assembled (fun q => TorusCrossing.h319_proved q) q hq

end PottsDiscontinuity.Provider
