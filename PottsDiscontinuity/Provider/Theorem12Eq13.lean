module

public import Mathlib
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.Analysis.Asymptotic13

/-!
# Proof of Theorem 1.2, positivity and (1.3) (`rc_theorem_1_2_positivity_eq_1_3`)

This module proves the exact statement of the final assertions of Theorem 1.2: positivity of the
right side of (1.2) and the asymptotics (1.3). The statement file
`PottsDiscontinuity/Frozen/Theorem12Eq13.lean` restates it as
`PottsDiscontinuity.rc_theorem_1_2_positivity_eq_1_3`, is checked against `Challenge.lean`, and
closes it with the export below. This module does not import the statement file.

Convention: the export `PottsDiscontinuity.Provider.rc_theorem_1_2_positivity_eq_1_3` has exactly
the type of the stated theorem, so that the proof body in the statement file is exactly
`by exact PottsDiscontinuity.Provider.rc_theorem_1_2_positivity_eq_1_3`.
-/

@[expose] public section

namespace PottsDiscontinuity.Provider

open MeasureTheory Filter Topology Real

/-- The proof of `rc_theorem_1_2_positivity_eq_1_3`: it has exactly the type of
that statement.  The convergence/positivity/identity assertion is `identity44` (valid for every
`lam > 0`; the hypothesis `cosh lam = √q / 2` is not needed), and the asymptotics (1.3) is
`asymptotic13`. -/
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
  ⟨fun _ _ lam hlam _ => identity44 lam hlam, asymptotic13⟩

end PottsDiscontinuity.Provider
