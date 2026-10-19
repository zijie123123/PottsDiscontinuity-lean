module

public import Mathlib

/-!
# The parameter `λ = arcosh(√q / 2)`

For `q > 4`, `λ = arcosh(√q/2)` is the unique `λ > 0` with `cosh λ = √q / 2`.
-/

@[expose] public section

namespace PottsDiscontinuity

theorem arcosh_unique (q lam : ℝ) (hl : 0 < lam)
    (hc : Real.cosh lam = Real.sqrt q / 2) : lam = Real.arcosh (Real.sqrt q / 2) := by
  rw [← hc, Real.arcosh_cosh hl.le]

theorem arcosh_pos_of_gt4 (q : ℝ) (hq : 4 < q) :
    0 < Real.arcosh (Real.sqrt q / 2) ∧ Real.cosh (Real.arcosh (Real.sqrt q / 2)) = Real.sqrt q / 2 := by
  have h2 : (2:ℝ) < Real.sqrt q := by
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) hq
  have h1 : (1:ℝ) < Real.sqrt q / 2 := by linarith
  exact ⟨Real.arcosh_pos h1, Real.cosh_arcosh (by linarith)⟩

end PottsDiscontinuity
