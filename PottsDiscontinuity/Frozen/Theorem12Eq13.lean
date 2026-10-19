module

public import Mathlib
public import PottsDiscontinuity.Provider.Theorem12Eq13

/-!
# Theorem statement `rc_theorem_1_2_positivity_eq_1_3` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree. Its proof is the assembled result from `PottsDiscontinuity/Provider/`.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- **Theorem 1.2**, the final assertions: positivity of the right side of (1.2) and (1.3)
(arXiv:1611.09877v2, p. 4). Here `λ = arcosh(√q / 2)` is the `λ > 0` with `cosh λ = √q / 2`. -/
theorem rc_theorem_1_2_positivity_eq_1_3 :
    (∀ q : ℝ, 4 < q → ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
      ∃ S T : ℝ,
        Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
        HasSum (fun k : ℕ => 4 / ((2 * k + 1) * Real.sinh (π ^ 2 * (2 * k + 1) / (2 * lam)))) T ∧
        0 < lam + 2 * S ∧ lam + 2 * S = T) ∧
    Asymptotics.IsEquivalent (𝓝[>] (4 : ℝ))
      (fun q => ∑' k : ℕ, 4 / ((2 * k + 1) *
        Real.sinh (π ^ 2 * (2 * k + 1) / (2 * Real.arcosh (Real.sqrt q / 2)))))
      (fun q => 8 * Real.exp (-(π ^ 2 / Real.sqrt (q - 4)))) :=
  by exact PottsDiscontinuity.Provider.rc_theorem_1_2_positivity_eq_1_3

end PottsDiscontinuity
