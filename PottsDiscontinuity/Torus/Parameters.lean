module

public import PottsDiscontinuity.Torus.SmoothingSum
public import PottsDiscontinuity.Infra.Lambda

/-!
# The parameter conversion in (3.12)

This connects the proved local smoothing sums to the exact parameter `sqrt (2 + sqrt q)`.
It supplies no FK or global topological input.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

/-- The positive parameter from (3.10), expressed using the already proved arcosh API. -/
theorem exp_add_exp_neg_arcosh (q : ℝ) (hq : 4 < q) :
    Real.exp (Real.arcosh (Real.sqrt q / 2)) +
      Real.exp (-Real.arcosh (Real.sqrt q / 2)) = Real.sqrt q := by
  have h := (arcosh_pos_of_gt4 q hq).2
  rw [Real.cosh_eq] at h
  linarith only [h]

/-- Squaring the half-parameter sum gives (3.12); positivity chooses the positive square root. -/
theorem half_exp_add_eq_sqrt (q lam : ℝ)
    (h : Real.exp lam + Real.exp (-lam) = Real.sqrt q) :
    Real.exp (lam / 2) + Real.exp (-lam / 2) = Real.sqrt (2 + Real.sqrt q) := by
  have hp : Real.exp (lam / 2) ^ 2 = Real.exp lam := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hn : Real.exp (-lam / 2) ^ 2 = Real.exp (-lam) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hm : Real.exp (lam / 2) * Real.exp (-lam / 2) = 1 := by
    rw [← Real.exp_add, show lam / 2 + -lam / 2 = 0 by ring, Real.exp_zero]
  have hs : (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^ 2 = 2 + Real.sqrt q := by
    nlinarith only [hp, hn, hm, h]
  have hpos : 0 ≤ Real.exp (lam / 2) + Real.exp (-lam / 2) :=
    add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  rw [← hs, Real.sqrt_sq hpos]

/-- The exact parameter in Corollary 3.13, for the canonical choice of lambda. -/
theorem half_exp_arcosh_eq_sqrt (q : ℝ) (hq : 4 < q) :
    Real.exp (Real.arcosh (Real.sqrt q / 2) / 2) +
      Real.exp (-Real.arcosh (Real.sqrt q / 2) / 2) = Real.sqrt (2 + Real.sqrt q) :=
  half_exp_add_eq_sqrt q _ (exp_add_exp_neg_arcosh q hq)

/-- The smoothing expansion at the exact `q`-dependent six-vertex parameter.
This intermediate identity is not Corollary 3.13(i): its left side is not an FK sum. -/
theorem sum_smoothingWeight_eq_Z6V_sqrt {N M : ℕ} (q : ℝ) (hq : 4 < q) :
    (∑ ω : ArrowConfig N M, ∑ s : Smoothing N M,
      smoothingWeight (Real.arcosh (Real.sqrt q / 2)) ω s) =
      Z6V (Real.sqrt (2 + Real.sqrt q)) N M := by
  rw [sum_smoothingWeight_eq_Z6V, half_exp_arcosh_eq_sqrt q hq]

/-- The smoothing expansion in a fixed row sector at the exact parameter. -/
theorem sum_smoothingWeight_eq_Z6Vr_sqrt {N M : ℕ} (q : ℝ) (hq : 4 < q) (r : ℕ) :
    (∑ ω : ArrowConfig N M with ω.absUp + r = N / 2,
      ∑ s : Smoothing N M, smoothingWeight (Real.arcosh (Real.sqrt q / 2)) ω s) =
      Z6Vr (Real.sqrt (2 + Real.sqrt q)) N M r := by
  rw [sum_smoothingWeight_eq_Z6Vr, half_exp_arcosh_eq_sqrt q hq]

end PottsDiscontinuity.Torus
