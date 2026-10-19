module

public import Mathlib
public import PottsDiscontinuity.Bethe.AsymptoticDefs
public import PottsDiscontinuity.Bethe.Prop21Positivity

/-!
# Basic consequences of the Bethe density norm

This module reuses the definitions of (2.3) and (2.5) from
`AsymptoticDefs.lean`.  In particular, norm bounds are always interpreted on
the full closed parameter interval used in (2.3).
-/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

/-- A bound on `densityNorm` bounds its weighted integrand at every point of
`[-π, π]`. -/
theorem densityNorm_pointwise_le {Δ : ℝ} (hΔ : Δ < -1) (f : ℝ → ℝ)
    (hbounded : BddAbove (Set.range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|))
    (B : ℝ) (hB : densityNorm Δ hΔ f hbounded ≤ B)
    {α : ℝ} (hα : α ∈ Icc (-Real.pi) Real.pi) :
    |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)| ≤ B := by
  have hpoint : |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)| ≤
      densityNorm Δ hΔ f hbounded := by
    apply le_csSup hbounded
    exact ⟨⟨α, hα⟩, rfl⟩
  exact hpoint.trans hB

/-- The `Ξ` weight in (2.3) has a positive lower bound uniform over
`Δ ≤ Δ₀ < -1`. -/
theorem exists_uniform_Xi_lower_bound {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ m : ℝ, 0 < m ∧ ∀ Δ : ℝ, Δ ≤ Δ₀ → ∀ α : ℝ,
      m ≤ Xi (lamOf Δ) α := by
  let lam₀ := lamOf Δ₀
  let m := (Real.exp lam₀ - 1) / (Real.exp lam₀ + 1)
  have hlam₀ : 0 < lam₀ := lamOf_pos hΔ₀
  have hexp : 1 < Real.exp lam₀ := by simpa using hlam₀
  have hm : 0 < m := by
    dsimp [m]
    exact div_pos (by linarith) (by linarith)
  refine ⟨m, hm, fun Δ hΔ α => ?_⟩
  have hΔ' : Δ < -1 := lt_of_le_of_lt hΔ hΔ₀
  have hlam : 0 < lamOf Δ := lamOf_pos hΔ'
  have hmono : lam₀ ≤ lamOf Δ := lamOf_mono hΔ₀ hΔ
  have hratio : m ≤ (Real.exp (lamOf Δ) - 1) /
      (Real.exp (lamOf Δ) + 1) := by
    dsimp [m]
    exact exp_ratio_mono' hlam₀ hmono
  exact hratio.trans (Xi_ge_exp_ratio hlam α)

/-- A weighted supremum bound controls the unweighted error because `Ξ` is
uniformly bounded below. -/
theorem densityNorm_unweighted_pointwise_le {Δ₀ Δ : ℝ} (hΔ₀ : Δ₀ < -1)
    (hΔ : Δ ≤ Δ₀) (f : ℝ → ℝ)
    (hbounded : BddAbove (Set.range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|))
    (B m : ℝ) (hm : 0 < m)
    (hXi : ∀ α : ℝ, m ≤ Xi (lamOf Δ) α)
    (hB : densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀) f hbounded ≤ B)
    {α : ℝ} (hα : α ∈ Icc (-Real.pi) Real.pi) :
    |f (kMap (lamOf Δ) α)| ≤ B / m := by
  have hXiα := hXi α
  have hXiPos : 0 < Xi (lamOf Δ) α := lt_of_lt_of_le hm hXiα
  have hweighted := densityNorm_pointwise_le (lt_of_le_of_lt hΔ hΔ₀) f
    hbounded B hB hα
  rw [abs_mul, abs_of_pos hXiPos] at hweighted
  have hprod : m * |f (kMap (lamOf Δ) α)| ≤ B := by
    exact (mul_le_mul_of_nonneg_right hXiα (abs_nonneg _)).trans hweighted
  exact (le_div_iff₀ hm).2 (by simpa [mul_comm] using hprod)

/-- The weighted norm bound also controls the unweighted density error at each
physical coordinate `x ∈ [-π, π]`. -/
theorem densityNorm_x_pointwise_le {Δ₀ Δ : ℝ} (hΔ₀ : Δ₀ < -1)
    (hΔ : Δ ≤ Δ₀) (f : ℝ → ℝ)
    (hbounded : BddAbove (Set.range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * f (kMap (lamOf Δ) α)|))
    (B m : ℝ) (hm : 0 < m)
    (hXi : ∀ α : ℝ, m ≤ Xi (lamOf Δ) α)
    (hB : densityNorm Δ (lt_of_le_of_lt hΔ hΔ₀) f hbounded ≤ B)
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |f x| ≤ B / m := by
  have hlam : 0 < lamOf Δ := lamOf_pos (lt_of_le_of_lt hΔ hΔ₀)
  have hα : kInv (lamOf Δ) x ∈ Icc (-Real.pi) Real.pi :=
    kInv_mem_Icc hlam hx
  have hpoint := densityNorm_unweighted_pointwise_le hΔ₀ hΔ f hbounded B m hm hXi hB hα
  simpa only [kMap_kInv hlam] using hpoint

  
  

end PottsDiscontinuity.Bethe
